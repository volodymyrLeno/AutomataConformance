package org.apromore.alignmentautomaton.importer;

import org.apromore.processmining.models.graphbased.AbstractGraphEdge;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagramFactory;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNNode;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Event;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Flow;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Gateway;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Activity;
import org.deckfour.xes.model.XLog;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class BPMNPreprocessor {
  BPMNDiagram diagram;
  List<Gateway> orSplits;
  HashMap<String, List<String>> artificialGatewaysInfo;

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

    String originalGateway = node.getAttributeMap().containsKey("belongsTo") ? node.getAttributeMap().get("belongsTo").toString() :
        node.getAttributeMap().get("Original id").toString();

    var g0 = diagram.addGateway(node.getAttributeMap().get("Original id") + "_" + (counter++), Gateway.GatewayType.DATABASED);
    g0.getAttributeMap().put("Original id", g0.getLabel());
    g0.getAttributeMap().put("belongsTo", originalGateway);
    addArtificialGateway(g0, originalGateway);
    for(var source: sources)
      diagram.addFlow(source, g0, null);

    var g1 = diagram.addGateway(node.getAttributeMap().get("Original id") + "_" + (counter++), Gateway.GatewayType.PARALLEL);
    g1.getAttributeMap().put("Original id", g1.getLabel());
    g1.getAttributeMap().put("belongsTo", originalGateway);
    addArtificialGateway(g1, originalGateway);
    diagram.addFlow(g0, g1, null);

    for(var target: targets){
      var g = diagram.addGateway(node.getAttributeMap().get("Original id") + "_" + (counter++), Gateway.GatewayType.DATABASED);
      g.getAttributeMap().put("Original id", g.getLabel());
      g.getAttributeMap().put("belongsTo", originalGateway);
      addArtificialGateway(g, originalGateway);
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

  public List<BPMNDiagram> extractScomponents(BPMNDiagram diagram){
    List<BPMNDiagram> scomps = new ArrayList<>();
    extractScomponentsUtil(diagram, scomps);
    return scomps;
  }

  private void extractScomponentsUtil(BPMNDiagram scomp, List<BPMNDiagram> globalScomps){
    var nonTrivialParallelSplit = getFirstNonTrivialParallelSplit(scomp);
    if(nonTrivialParallelSplit == null)
      globalScomps.add(BPMNDiagramFactory.cloneBPMNDiagram(scomp));
    else{
      var outgoingFlows = scomp.getOutEdges(nonTrivialParallelSplit).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
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

  private BPMNNode getFirstNonTrivialParallelSplit(BPMNDiagram diagram){
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
        if(isParallelSplit(target, diagram))
          return target;
        else{
          if (!visited.contains(target)) {
            visited.add(target);
            queue.add(target);
          }
        }
      }
    }

    return null;
  }

  private boolean isParallelSplit(BPMNNode node, BPMNDiagram diagram){
    var outEdges = diagram.getOutEdges(node).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
    if(outEdges.size() > 1){
      if(node instanceof Gateway){
        Gateway.GatewayType gatewayType = ((Gateway) node).getGatewayType();
        return gatewayType == Gateway.GatewayType.INCLUSIVE || gatewayType == Gateway.GatewayType.PARALLEL;
      }
      else return node instanceof Activity || node instanceof Event;
    }
    return false;
  }

  public LinkedList<BPMNNode> getNonTrivialParallelSplits(BPMNDiagram diagram){
    LinkedList<BPMNNode> nonTrivialParallelSplits = new LinkedList<>();
    for(var node: diagram.getNodes().stream().filter(node -> node instanceof Activity ||
        node instanceof Gateway || node instanceof Event).collect(Collectors.toList())){
      if(isParallelSplit(node, diagram))
        nonTrivialParallelSplits.add(node);
    }

    return nonTrivialParallelSplits;
  }

  public List<BPMNNode> getUnreachableNodes(BPMNDiagram diagram){
    Set<BPMNNode> reachableNodes = new HashSet<>();
    reachableNodes.addAll(forwardTraversal(diagram));
    reachableNodes.retainAll(backwardTraversal(diagram));
    return diagram.getNodes().stream().filter(node -> !reachableNodes.contains(node)).collect(Collectors.toList());
  }

  public List<BPMNNode> forwardTraversal(BPMNDiagram diagram){
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
    return visited;
  }

  public List<BPMNNode> backwardTraversal(BPMNDiagram diagram){
    List<BPMNNode> visited = new ArrayList<>();
    Queue<BPMNNode> queue = new LinkedList<>();

    for(var event: diagram.getEvents())
      if(event.getEventType() == Event.EventType.END){
        visited.add(event);
        queue.add(event);
      }

    while(queue.size() != 0) {
      var next = queue.poll();
      var incomingEdges = diagram.getInEdges(next).stream().filter(e -> e instanceof Flow).collect(Collectors.toList());
      for (var edge : incomingEdges) {
        var source = edge.getSource();
        if (!visited.contains(source)) {
          visited.add(source);
          queue.add(source);
        }
      }
    }

    return visited;
  }

  private void addArtificialGateway(Gateway gateway, String originalGateway){
    if(!artificialGatewaysInfo.containsKey(originalGateway))
      artificialGatewaysInfo.put(originalGateway, Collections.singletonList(gateway.getLabel()));
    else
      artificialGatewaysInfo.put(originalGateway, Stream.concat(artificialGatewaysInfo.get(originalGateway).stream(),
          Collections.singletonList(gateway.getLabel()).stream()).collect(Collectors.toList()));
  }

  public BPMNDiagram filterModel(BPMNDiagram diagram, XLog xLog, Integer maxFanout){
    var concurrencyInfo = computeConcurrencyInfo(diagram, xLog);
    for(Map.Entry<BPMNNode, HashMap<Flow, Double>> entry: concurrencyInfo.entrySet()){
      var node = entry.getKey();
      var flowsSupport = entry.getValue();
      if(flowsSupport.size() > maxFanout){
        if(node instanceof Gateway && (((Gateway) node).getGatewayType() == Gateway.GatewayType.DATABASED ||
            ((Gateway) node).getGatewayType() == Gateway.GatewayType.EVENTBASED))
          continue;
        else{
          var removeFlows = flowsSupport.entrySet().stream().sorted(Map.Entry.comparingByValue())
              .limit(flowsSupport.size() - maxFanout).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue, (e1, e2) -> e1, LinkedHashMap::new));
          for(var flow: removeFlows.keySet())
            diagram.removeEdge(flow);
        }
      }
    }
    for(var node: getUnreachableNodes(diagram))
      diagram.removeNode(node);

    return diagram;
  }

  public BPMNDiagram filterNodes(BPMNDiagram diagram, XLog xLog, Double minSupport){
    HashMap<String, Double> supportInfo = computeSupportInfo(xLog);
    for(var node: diagram.getNodes()) {
      var label = node.getLabel();
      if (supportInfo.containsKey(label)) {
        var sup = supportInfo.get(label);
        if (sup <= minSupport)
          diagram.removeNode(node);
      }
    }
    for(var node: getUnreachableNodes(diagram))
      diagram.removeNode(node);

    return diagram;
  }

  public HashMap<BPMNNode, HashMap<Flow, Double>> computeConcurrencyInfo(BPMNDiagram diagram, XLog xLog){
    HashMap<String, Double> supportInfo = computeSupportInfo(xLog);
    HashMap<BPMNNode, HashMap<Flow, Double>> concurrencyInfo = new HashMap<>();
    for(var node: diagram.getNodes().stream().filter(node -> node instanceof Activity ||
        node instanceof Event || node instanceof Gateway).collect(Collectors.toList())){
      concurrencyInfo.put(node, computeFlowsSupport(node, supportInfo, diagram));
    }
    return concurrencyInfo;
  }

  private HashMap<Flow, Double> computeFlowsSupport(BPMNNode node, HashMap<String, Double> supportInfo, BPMNDiagram diagram){
    HashMap<Flow, Double> flowsSupportInfo = new HashMap<>();
    var outEdges = diagram.getOutEdges(node).stream().filter(edge -> edge instanceof Flow).collect(Collectors.toList());
    for(var edge: outEdges){
      Flow flow = (Flow) edge;
      flowsSupportInfo.put(flow, computeFlowSupport(flow, supportInfo, diagram));
    }
    return flowsSupportInfo;
  }

  private HashMap<String, Double> computeSupportInfo(XLog log){
    HashMap<String, Double> support = new HashMap<>();
    HashMap<String, Set<Integer>> appearances = new HashMap<>();
    for(int i = 0; i < log.size(); i++){
      for(int j = 0; j < log.get(i).size(); j++){
        var event = log.get(i).get(j);
        String elementLabel = event.getAttributes().get("concept:name").toString();
        if(!appearances.containsKey(elementLabel))
          appearances.put(elementLabel, Collections.singleton(i));
        else
          appearances.put(elementLabel, Stream.concat(appearances.get(elementLabel).stream(),
              Collections.singleton(i).stream()).collect(Collectors.toSet()));
      }
    }
    for(Map.Entry<String, Set<Integer>> entry: appearances.entrySet())
      support.put(entry.getKey(), (double) entry.getValue().size()/log.size());

    return support;
  }

  private Double computeFlowSupport(Flow flow, HashMap<String, Double> supportInfo, BPMNDiagram diagram){
    BPMNNode target = flow.getTarget();
    String tLabel = target.getLabel();
    if((target instanceof Activity || target instanceof Event)){
      if(supportInfo.containsKey(tLabel))
        return supportInfo.get(tLabel);
      else
        return 0.0;
    }

    else{
      var outEdges = diagram.getOutEdges(target).stream().filter(edge -> edge instanceof Flow).collect(Collectors.toList());
      Double max = 0.0;
      for(var edge: outEdges){
        Double support = computeFlowSupport((Flow) edge, supportInfo, diagram);
        if(support > max)
          max = support;
      }
      return max;
    }
  }

  private boolean equal(Flow f1, Flow f2){
    return f1.getSource().getAttributeMap().get("Original id").equals(f2.getSource().getAttributeMap().get("Original id")) &&
        f1.getTarget().getAttributeMap().get("Original id").equals(f2.getTarget().getAttributeMap().get("Original id"));
  }

  public HashMap<String, List<String>> getArtificialGatewaysInfo(){ return this.artificialGatewaysInfo; }
}
