package au.qut.apromore.ScalableConformanceChecker;

import au.qut.apromore.ScalableConformanceChecker.ConformResult.RedSection;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNNode;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Flow;
import org.processmining.plugins.petrinet.replayresult.StepTypes;
import org.processmining.plugins.replayer.replayresult.AllSyncReplayResult;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class AlignmentAnalyzer {

  public static ConformResult extractDelta(BPMNDiagram diagram, AllSyncReplayResult traceAlignment) {
    ConformResult conformResult = new ConformResult();

    List<Flow> activeFlows = new ArrayList<>();
    BPMNNode lastMatch = null;
    BPMNNode prevNode = null;
    StepTypes prevStep = null;
    RedSection currentRedSection = null;

    for (int i = 0; i < traceAlignment.getNodeInstanceLst().get(0).size(); i++) {
      String move = traceAlignment.getNodeInstanceLst().get(0).get(i).toString();
      StepTypes moveType = traceAlignment.getStepTypesLst().get(0).get(i);
      var moveNode = diagram.getNodes().stream().filter(n -> n.getAttributeMap().get("Original id").equals(move)).findFirst();

      if (moveType == StepTypes.LMGOOD) {
        if (prevStep == StepTypes.L) {
          currentRedSection.setEndPoint(move);
          conformResult.addRed(currentRedSection);
          currentRedSection = null;
        } else {
          var flows = activeFlows.stream().filter(e -> e.getTarget().equals(moveNode.get())).collect(Collectors.toList());
          BPMNNode finalPrevNode = prevNode;
          var directConnection = flows.stream().filter(e -> e.getSource().equals(finalPrevNode)).findFirst();
          List<Flow> coloredFlows = flows;
          //List<BPMNEdge> coloredFlows = directConnection.map(Collections::singletonList).orElse(flows);

          for(var flow: coloredFlows){
            String flowID = flow.getAttributeMap().get("Original id").toString();
            String sourceID = flow.getSource().getAttributeMap().get("Original id").toString();
            if(conformResult.getGreen().contains(sourceID))
              conformResult.addGreen(flowID);
            else if(conformResult.getGrey().contains(sourceID))
              conformResult.addGrey(flowID);
          }

          /*if(prevStep == StepTypes.LMGOOD){
            for(var flow: coloredFlows)
              conformResult.addGreen(flow.getAttributeMap().get("Original id").toString());
          }
          else if(prevStep == StepTypes.MREAL){
            for(var flow: coloredFlows)
              conformResult.addGrey(flow.getAttributeMap().get("Original id").toString());
          }*/

          activeFlows.removeAll(coloredFlows);
        }
        conformResult.addGreen(move);
        lastMatch = moveNode.get();
        activeFlows.addAll(diagram.getOutEdges(lastMatch).stream().filter(e -> e instanceof Flow).map(e -> (Flow) e).collect(Collectors.toList()));
      }
      else if (moveType == StepTypes.L) {
        if (currentRedSection == null) {
          currentRedSection = conformResult.new RedSection();
          String startPoint = lastMatch != null ? lastMatch.getAttributeMap().get("Original id").toString() : null;
          currentRedSection.setStartPoint(startPoint);
        }

        if (moveNode.isPresent())
          currentRedSection.addActivity(moveNode.get().getLabel());
        else
          currentRedSection.addActivity(move);
      }
      else if (moveType == StepTypes.MREAL) {
        BPMNNode activeNode = prevStep == StepTypes.L ? lastMatch : prevNode;
        var flows = activeFlows.stream().filter(e -> e.getTarget().equals(moveNode.get())).collect(Collectors.toList());
        var directConnection = flows.stream().filter(e -> e.getSource().equals(activeNode)).findFirst();
        List<Flow> coloredFlows = directConnection.map(Collections::singletonList).orElse(flows);

        for(var flow: coloredFlows)
          conformResult.addGrey(flow.getAttributeMap().get("Original id").toString());

        activeFlows.removeAll(coloredFlows);
        conformResult.addGrey(move);
        activeFlows.addAll(diagram.getOutEdges(moveNode.get()).stream().filter(e -> e instanceof Flow).
            map(e -> (Flow) e).collect(Collectors.toList()));
      }
      prevStep = moveType;
      prevNode = moveNode.orElse(null);
    }
    return conformResult;
  }
}