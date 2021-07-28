package org.apromore.alignmentautomaton.importer;

import org.apromore.processmining.models.graphbased.AbstractGraphEdge;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagramFactory;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNNode;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Event;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Flow;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Gateway;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.stream.Collectors;

public class BPMNPreprocessor {
  BPMNDiagram diagram;
  List<Gateway> orSplits;

  public BPMNDiagram preprocessModel(BPMNDiagram diagram){
    this.diagram = diagram;
    orSplits = getOrSplits();
    for(var orSplit: orSplits)
      decomposeORSplit(orSplit);

    orSplits = getOrSplits();
    while(orSplits.size() > 0){
      replaceORSplit(orSplits.get(0));
      orSplits = getOrSplits();
    }

    return this.diagram;
  }

  private void replaceORSplit(Gateway node){
    int counter = 0;
    var inEdges = diagram.getInEdges(node).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
    var outEdges = diagram.getOutEdges(node).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());

    List<BPMNNode> sources = inEdges.stream().map(AbstractGraphEdge::getSource).collect(Collectors.toList());
    List<BPMNNode> targets = outEdges.stream().map(AbstractGraphEdge::getTarget).collect(Collectors.toList());

    var originalGateway = node.getAttributeMap().containsKey("belongsTo") ? node.getAttributeMap().get("belongsTo") :
        node.getAttributeMap().get("Original id");

    var g0 = diagram.addGateway(node.getAttributeMap().get("Original id") + "_" + (counter++), Gateway.GatewayType.DATABASED);
    g0.getAttributeMap().put("Original id", g0.getLabel());
    g0.getAttributeMap().put("belongsTo", originalGateway);
    for(var source: sources)
      diagram.addFlow(source, g0, null);

    var g1 = diagram.addGateway(node.getAttributeMap().get("Original id") + "_" + (counter++), Gateway.GatewayType.PARALLEL);
    g1.getAttributeMap().put("Original id", g1.getLabel());
    g1.getAttributeMap().put("belongsTo", originalGateway);
    diagram.addFlow(g0, g1, null);

    for(var target: targets){
      var g = diagram.addGateway(node.getAttributeMap().get("Original id") + "_" + (counter++), Gateway.GatewayType.DATABASED);
      g.getAttributeMap().put("Original id", g.getLabel());
      g.getAttributeMap().put("belongsTo", originalGateway);
      diagram.addFlow(g, target, null);
      diagram.addFlow(g1, g, null);
      diagram.addFlow(g0, g, null);
    }

    diagram.removeGateway(node);
  }

  private void decomposeORSplit(Gateway node){
        var currentGateway = node;
        var outEdges = diagram.getOutEdges(currentGateway).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
        int counter = 0;

        String originalGateway = node.getAttributeMap().get("Original id").toString();

        while(outEdges.size() > 2){
            var processEdges = new ArrayList<>(outEdges).subList(1, outEdges.size());
            Gateway gateway = diagram.addGateway(currentGateway.getAttributeMap().get("Original id") + "_" + counter, Gateway.GatewayType.INCLUSIVE);
            gateway.getAttributeMap().put("Original id", currentGateway.getAttributeMap().get("Original id") + "_" + counter);
            gateway.getAttributeMap().put("belongsTo", originalGateway);

            counter++;
            diagram.addFlow(currentGateway, gateway, null);
            for(var edge: processEdges){
                diagram.removeEdge(edge);
                diagram.addFlow(gateway, edge.getTarget(), null);
            }
            currentGateway = gateway;
            outEdges = diagram.getOutEdges(currentGateway).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
        }
    }

  private List<Gateway> getOrSplits(){
    List<Gateway> orSplits = new ArrayList<>();
    for(var gateway: diagram.getGateways()){
      var outEdges = diagram.getOutEdges(gateway).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
      if(gateway.getGatewayType() == Gateway.GatewayType.INCLUSIVE && outEdges.size() > 1)
        orSplits.add(gateway);
    }

    return orSplits;
  }

  public List<BPMNDiagram> extractScomponents(){
    List<BPMNDiagram> scomps = new ArrayList<>();
    extractScomponentsUtil(this.diagram, scomps);
    return scomps;
  }

  public void extractScomponentsUtil(BPMNDiagram scomp, List<BPMNDiagram> globalScomps){
    var nonTrivialAndSplits = getNonTrivialAndSplits(scomp);
    if(nonTrivialAndSplits.size() == 0)
      globalScomps.add(BPMNDiagramFactory.cloneBPMNDiagram(scomp));
    else{
      var andSplit = nonTrivialAndSplits.get(0);
      var outgoingFlows = scomp.getOutEdges(andSplit).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
      for(var outgoingFlow: outgoingFlows){
        BPMNDiagram s = BPMNDiagramFactory.cloneBPMNDiagram(scomp);
        var removeFlows = outgoingFlows.stream().filter(flow -> !flow.equals(outgoingFlow)).collect(Collectors.toList());
        for(var removeFlow: removeFlows){
          var flows = s.getFlows().stream().filter(flow -> equal(flow, (Flow) removeFlow)).collect(Collectors.toList()).get(0);
          s.removeEdge(flows);
        }

        var removeNodes = getUnreachableNodes(s);
        for(var node: removeNodes)
          s.removeNode(node);
        extractScomponentsUtil(s, globalScomps);
      }
    }
  }

  public List<Gateway> getNonTrivialAndSplits(BPMNDiagram diagram){
    List<Gateway> nonTrivialAndSplits = new ArrayList<>();
    for(var gateway: diagram.getGateways()){
      var outEdges = diagram.getOutEdges(gateway).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
      if(gateway.getGatewayType() == Gateway.GatewayType.PARALLEL && outEdges.size() > 1)
        nonTrivialAndSplits.add(gateway);
    }

    return nonTrivialAndSplits;
  }

  public List<BPMNNode> getUnreachableNodes(BPMNDiagram diagram){
    List<BPMNNode> visited = new ArrayList<>();
    Queue<BPMNNode> queue = new LinkedList<>();

    for(var event: diagram.getEvents())
      if(event.getEventType() == Event.EventType.START){
        visited.add(event);
        queue.add(event);
      }

    while(queue.size() != 0) {
      var next = queue.poll();
      var outgoingEdges = diagram.getOutEdges(next).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
      for (var edge : outgoingEdges) {
        var target = edge.getTarget();
        if (!visited.contains(target)) {
          visited.add(target);
          queue.add(target);
        }
      }
    }

    return diagram.getNodes().stream().filter(node -> !visited.contains(node)).collect(Collectors.toList());
  }

  private boolean equal(Flow f1, Flow f2){
    return f1.getSource().getAttributeMap().get("Original id").equals(f2.getSource().getAttributeMap().get("Original id")) &&
        f1.getTarget().getAttributeMap().get("Original id").equals(f2.getTarget().getAttributeMap().get("Original id"));
  }
}
