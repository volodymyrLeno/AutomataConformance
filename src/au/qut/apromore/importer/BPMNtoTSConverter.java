package au.qut.apromore.importer;

import org.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.processmining.models.graphbased.directed.bpmn.BPMNNode;
import org.processmining.models.graphbased.directed.bpmn.elements.Event;
import org.processmining.models.graphbased.directed.bpmn.elements.Flow;
import org.processmining.models.graphbased.directed.bpmn.elements.Gateway;
import org.processmining.models.graphbased.directed.transitionsystem.ReachabilityGraph;

import java.util.*;
import java.util.stream.Collectors;

public class BPMNtoTSConverter {
    Queue<BitSet> toBeVisited;
    LinkedHashMap<Integer, Flow> labeledFlows;
    LinkedHashMap<Flow, Integer> invertedLabeledFlows;
    LinkedHashMap<BPMNNode, LinkedHashSet<BitSet>> bitMasks;
    ReachabilityGraph rg;

    BPMNDiagram diagram;

    public ReachabilityGraph BPMNtoTS(BPMNDiagram diagram){
        this.diagram = diagram;
        rg = new ReachabilityGraph("");
        toBeVisited = new LinkedList<>();
        labeledFlows = labelFlows(diagram.getFlows());
        invertedLabeledFlows = new LinkedHashMap<>(labeledFlows.entrySet().stream().
                collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey)));
        bitMasks = computeBitMasks();


        getInitialMarking();
        var next = toBeVisited.poll();
        while(next != null){
            visit(next);
            next = toBeVisited.poll();
        }

        return rg;
    }

    private void getInitialMarking(){
        for(Map.Entry<Integer, Flow> flow: labeledFlows.entrySet()){
            var value = flow.getValue();
            if(isStart(value.getSource())){
                BitSet marking = new BitSet();
                marking.set(flow.getKey());
                toBeVisited.add(marking);
                rg.addState(marking);
            }
        }
    }

    private LinkedHashMap<BPMNNode, LinkedHashSet<BitSet>> computeBitMasks(){
        LinkedHashMap<BPMNNode, LinkedHashSet<BitSet>> bitMasks = new LinkedHashMap<>();
        var nodes = diagram.getNodes();
        for(var node: nodes)
            bitMasks.put(node, computeBitMask(node));
        return bitMasks;
    }

    private LinkedHashSet<BitSet> computeBitMask(BPMNNode node){
        LinkedHashSet<BitSet> bitMask = new LinkedHashSet<>();

        var inEdges = diagram.getInEdges(node);
        if(inEdges.size() > 1){
            if(isANDGateway(node)){
                BitSet mask = new BitSet(labeledFlows.size());
                for(var flow: inEdges)
                    mask.set(invertedLabeledFlows.get(flow));

                bitMask.add(mask);
            }
            else if(isXORGateway(node)){
                for(var flow: inEdges){
                    BitSet mask = new BitSet(labeledFlows.size());
                    mask.set(invertedLabeledFlows.get(flow));
                    bitMask.add(mask);
                }
            }
        }
        else if(inEdges.size() > 0) {
            BitSet mask = new BitSet(labeledFlows.size());
            mask.set(invertedLabeledFlows.get(inEdges.toArray()[0]));
            bitMask.add(mask);
        }
        return bitMask;
    }

    private LinkedHashMap<Integer, Flow> labelFlows(Collection<Flow> flows){
        LinkedHashMap<Integer, Flow> labeledFlows = new LinkedHashMap<>();
        int i = 0;
        for(Flow flow: flows)
            labeledFlows.put(i++, flow);

        return labeledFlows;
    }

    private void visit(BitSet activeMarking){
        var enabledElements = enabledElements(activeMarking);
        for(var element: enabledElements)
            fire(activeMarking, element);
    }

    private LinkedHashSet<BPMNNode> enabledElements(BitSet activeMarking){
        LinkedHashSet<BPMNNode> enabledElements = new LinkedHashSet<>();

        for (int i = activeMarking.nextSetBit(0); i >= 0; i = activeMarking.nextSetBit(i+1)) {
            var target = labeledFlows.get(i).getTarget();
            if(enabled(activeMarking, target))
                enabledElements.add(target);

            if (i == Integer.MAX_VALUE) {
                break;
            }
        }
        return enabledElements;
    }

    private boolean enabled(BitSet activeMarking, BPMNNode node){
        var bitMask = bitMasks.get(node);
        if(bitMask.size() > 1){
            for(BitSet mask: bitMask){
                BitSet m = (BitSet) activeMarking.clone();
                m.and(mask);
                if(m.equals(mask))
                    return true;
            }
            return false;
        }
        else{
            BitSet m = (BitSet) activeMarking.clone();
            BitSet mask = (BitSet) bitMask.toArray()[0];
            m.and(mask);
            return m.equals(mask);
        }
    }

    private void fire(BitSet activeMarking, BPMNNode node){
        List<Integer> newFlows = new ArrayList<>();
        //var invisibleTransition = false;
        var outEdges = diagram.getOutEdges(node);

        for(var flow: outEdges)
            newFlows.add(invertedLabeledFlows.get(flow));

        List<Integer> oldFlows = new ArrayList<>();
        var inEdges = diagram.getInEdges(node);

        for(var flow: inEdges)
            oldFlows.add(invertedLabeledFlows.get(flow));

        if(!isXORGateway(node)){
            BitSet newMarking = (BitSet) activeMarking.clone();

            for(int idx: newFlows)
                newMarking.set(idx);

            if(!isActivity(node))
                updateReachabilityGraph(activeMarking, node, newMarking, oldFlows, true);
            else
                updateReachabilityGraph(activeMarking, node, newMarking, oldFlows, false);
        }
        else{
            for(int idx: newFlows){
                BitSet newMarking = (BitSet) activeMarking.clone();
                newMarking.set(idx);
                updateReachabilityGraph(activeMarking, node, newMarking, oldFlows, true);
            }
        }
    }

    private void updateReachabilityGraph(BitSet activeMarking, BPMNNode node, BitSet newMarking,
                                         List<Integer> oldFlows, Boolean invisibleTransition) {
        for(int jdx: oldFlows)
            newMarking.set(jdx, false);

        if(newMarking.cardinality() > 0){
            if(!rg.getStates().contains(newMarking)){
                rg.addState(newMarking);
                toBeVisited.add(newMarking);
            }

            if(invisibleTransition){
                rg.addTransition(activeMarking, newMarking, node);
                rg.findTransition(activeMarking, newMarking, node).setLabel("tau");
            }
            else
                rg.addTransition(activeMarking, newMarking, node);
        }
    }

    private boolean isStart(BPMNNode node){
        return node instanceof org.processmining.models.graphbased.directed.bpmn.elements.Event &&
                ((Event) node).getEventType().name().equals("START");
    }

    private boolean isActivity(BPMNNode node){
        return node instanceof org.processmining.models.graphbased.directed.bpmn.elements.Activity;
    }

    private boolean isXORGateway(BPMNNode node){
        return node instanceof org.processmining.models.graphbased.directed.bpmn.elements.Gateway &&
                ((Gateway) node).getGatewayType().name().equals("DATABASED");
    }

    private boolean isANDGateway(BPMNNode node){
        return node instanceof org.processmining.models.graphbased.directed.bpmn.elements.Gateway &&
                ((Gateway) node).getGatewayType().name().equals("PARALLEL");
    }

    private boolean isORGateway(BPMNNode node){
        return node instanceof org.processmining.models.graphbased.directed.bpmn.elements.Gateway &&
                ((Gateway) node).getGatewayType().name().equals("INCLUSIVE");
    }
}