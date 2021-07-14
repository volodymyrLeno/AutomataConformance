package au.qut.apromore.importer;

import org.processmining.models.graphbased.AbstractGraphEdge;
import org.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.processmining.models.graphbased.directed.bpmn.BPMNDiagramFactory;
import org.processmining.models.graphbased.directed.bpmn.BPMNDiagramImpl;
import org.processmining.models.graphbased.directed.bpmn.BPMNNode;
import org.processmining.models.graphbased.directed.bpmn.elements.Event;
import org.processmining.models.graphbased.directed.bpmn.elements.Gateway;

import java.util.*;
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
        var inEdges = diagram.getInEdges(node);
        var outEdges = diagram.getOutEdges(node);

        List<BPMNNode> sources = inEdges.stream().map(AbstractGraphEdge::getSource).collect(Collectors.toList());
        List<BPMNNode> targets = outEdges.stream().map(AbstractGraphEdge::getTarget).collect(Collectors.toList());

        var g0 = diagram.addGateway("gateway " + node.getAttributeMap().get("Original id"), Gateway.GatewayType.DATABASED);
        for(var source: sources)
            diagram.addFlow(source, g0, null);

        var g1 = diagram.addGateway("gateway " + node.getAttributeMap().get("Original id"), Gateway.GatewayType.PARALLEL);
        diagram.addFlow(g0, g1, null);

        for(var target: targets){
            var g = diagram.addGateway("gateway " + node.getAttributeMap().get("Original id"), Gateway.GatewayType.DATABASED);
            diagram.addFlow(g, target, null);
            diagram.addFlow(g1, g, null);
            diagram.addFlow(g0, g, null);
        }

        diagram.removeGateway(node);
    }

    private void decomposeORSplit(Gateway node){
        var currentGateway = node;
        var outEdges = diagram.getOutEdges(currentGateway);

        while(outEdges.size() > 2){
            var processEdges = new ArrayList<>(outEdges).subList(1, outEdges.size());
            Gateway gateway = diagram.addGateway("gateway " + node.getAttributeMap().get("Original id"), Gateway.GatewayType.INCLUSIVE);
            gateway.getAttributeMap().put("Original id", node.getAttributeMap().get("Original id"));
            diagram.addFlow(currentGateway, gateway, null);
            for(var edge: processEdges){
                diagram.removeEdge(edge);
                diagram.addFlow(gateway, edge.getTarget(), null);
            }
            currentGateway = gateway;
            outEdges = diagram.getOutEdges(currentGateway);
        }
    }

    private List<Gateway> getOrSplits(){
        List<Gateway> orSplits = new ArrayList<>();
        for(var gateway: diagram.getGateways()){
            var outEdges = diagram.getOutEdges(gateway);
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
            var outgoingFlows = scomp.getOutEdges(andSplit);
            for(var outgoingFlow: outgoingFlows){
                var s = BPMNDiagramFactory.cloneBPMNDiagram(scomp);
                var removeFlows = outgoingFlows.stream().filter(flow -> !flow.equals(outgoingFlow)).collect(Collectors.toList());
                for(var flow: removeFlows)
                    s.removeEdge(flow);
                var removeNodes = getUnreachableNodes(scomp);
                for(var node: removeNodes)
                    s.removeNode(node);
                extractScomponentsUtil(s, globalScomps);
            }
        }
    }

    public List<Gateway> getNonTrivialAndSplits(BPMNDiagram diagram){
        List<Gateway> nonTrivialAndSplits = new ArrayList<>();
        for(var gateway: diagram.getGateways()){
            var outEdges = diagram.getOutEdges(gateway);
            if(gateway.getGatewayType() == Gateway.GatewayType.PARALLEL && outEdges.size() > 1)
                nonTrivialAndSplits.add(gateway);
        }

        return nonTrivialAndSplits;
    }

    public List<BPMNNode> getUnreachableNodes(BPMNDiagram diagram){
        List<BPMNNode> visitedNodes = new ArrayList<>();
        Queue<BPMNNode> toBeVisited = new LinkedList<>();

        for(var event: diagram.getEvents())
            if(event.getEventType() == Event.EventType.START)
                toBeVisited.add(event);

        var next = toBeVisited.poll();
        while(next != null && !visitedNodes.contains(next)){
            var outgoingEdges = diagram.getOutEdges(next);
            for(var edge: outgoingEdges)
                toBeVisited.add(edge.getTarget());
            visitedNodes.add(next);
            next = toBeVisited.poll();
        }

        return diagram.getNodes().stream().filter(node -> !visitedNodes.contains(node)).collect(Collectors.toList());
    }
}
