package org.apromore.alignmentautomaton.ScalableConformanceChecker;

import org.apromore.alignmentautomaton.ReplayResult;
import org.apromore.alignmentautomaton.ScalableConformanceChecker.ConformanceResult.RedSection;
import org.apromore.alignmentautomaton.StepType;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNNode;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Flow;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.UUID;
import java.util.stream.Collectors;

public class AlignmentAnalyzer {
  public static ConformanceResult extractDelta(BPMNDiagram diagram, ReplayResult traceAlignment) {
    ConformanceResult conformResult = new ConformanceResult();

    List<Flow> activeFlows = new ArrayList<>();
    BPMNNode lastMatch = null;
    BPMNNode prevNode = null;
    StepType prevStep = null;
    RedSection currentRedSection = null;

    for (int i = 0; i < traceAlignment.getNodeInstances().size(); i++) {
      String move = traceAlignment.getNodeInstances().get(i);
      StepType moveType = traceAlignment.getStepTypes().get(i);
      var moveNode = diagram.getNodes().stream().filter(n -> n.getAttributeMap().get("Original id").equals(move)).findFirst();

      if (moveType == StepType.LMGOOD) {
        if (prevStep == StepType.L) {
          currentRedSection.setEndPoint(move);
          conformResult.addRed(currentRedSection);
          currentRedSection = null;
        } else {
          var flows = activeFlows.stream().filter(e -> e.getTarget().equals(moveNode.get())).collect(Collectors.toList());
          List<Flow> coloredFlows = flows;

          RedSection finalCurrentRedSection = currentRedSection;
          if(currentRedSection != null){
            currentRedSection.setEndPoint(move);
            conformResult.addRed(currentRedSection);
            currentRedSection = null;
          }

          for(var flow: coloredFlows){
            String flowID = flow.getAttributeMap().get("Original id").toString();
            String sourceID = flow.getSource().getAttributeMap().get("Original id").toString();
            if(conformResult.getGreen().contains(sourceID))
              conformResult.addGreen(flowID);
            else if(conformResult.getGrey().contains(sourceID))
              conformResult.addGrey(flowID);
          }

          activeFlows.removeAll(coloredFlows);
        }
        conformResult.addGreen(move);
        lastMatch = moveNode.get();
        activeFlows.addAll(diagram.getOutEdges(lastMatch).stream().filter(e -> e instanceof Flow).map(e -> (Flow) e).collect(Collectors.toList()));
      }
      else if (moveType == StepType.L) {
        if (currentRedSection == null) {
          currentRedSection = conformResult.new RedSection();
          String startPoint = lastMatch != null ? lastMatch.getAttributeMap().get("Original id").toString() : null;
          currentRedSection.setStartPoint(startPoint);
        }

        String label = moveNode.isPresent() ? moveNode.get().getLabel() : move;
        String id = "node-" + UUID.randomUUID();
        currentRedSection.addActivity(new ConformanceResult().new RedSection().new RedActivity(id, label));
      }
      else if (moveType == StepType.MREAL) {
        BPMNNode activeNode = prevStep == StepType.L ? lastMatch : prevNode;
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
