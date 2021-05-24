package au.qut.apromore.importer;

import org.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.processmining.models.graphbased.directed.bpmn.BPMNNode;
import org.processmining.models.graphbased.directed.bpmn.elements.Event;
import org.processmining.models.graphbased.directed.bpmn.elements.Flow;
import org.processmining.models.graphbased.directed.bpmn.elements.Gateway;
import org.processmining.models.graphbased.directed.transitionsystem.ReachabilityGraph;

import java.util.*;
import java.util.stream.Collectors;

public class BPMNtoFSMConverter {
    Queue<BitSet> toBeVisited;
    LinkedHashSet<BitSet> states;
    LinkedHashSet<BitSet> finalStates;
    LinkedHashSet<BitSet> sourceStates;
    LinkedHashSet<Trans> transitions;
    LinkedHashMap<BitSet, LinkedHashSet<Trans>> incomingTransitions;
    LinkedHashMap<BitSet, LinkedHashSet<Trans>> outgoingTransitions;
    LinkedHashMap<Integer, Flow> labeledFlows;
    LinkedHashMap<Flow, Integer> invertedLabeledFlows;
    LinkedHashMap<BPMNNode, LinkedHashSet<BitSet>> bitMasks;

    BPMNDiagram diagram;

    public ReachabilityGraph BPMNtoFSM(BPMNDiagram diagram){
        this.diagram = diagram;
        toBeVisited = new LinkedList<>();
        states = new LinkedHashSet<>();
        sourceStates = new LinkedHashSet<>();
        finalStates = new LinkedHashSet<>();
        transitions = new LinkedHashSet<>();
        incomingTransitions = new LinkedHashMap<>();
        outgoingTransitions = new LinkedHashMap<>();
        labeledFlows = labelFlows(diagram.getFlows());
        invertedLabeledFlows = new LinkedHashMap<>(labeledFlows.entrySet().stream().
                collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey)));
        bitMasks = computeBitMasks();
        var initialMarking = new BitSet(labeledFlows.size());
        initialMarking = getInitialMarking();
        states.add(initialMarking);

        toBeVisited.add(initialMarking);
        var next = toBeVisited.poll();
        while(next != null){
            visit(next);
            next = toBeVisited.poll();
        }
        return null;
    }

    private BitSet getInitialMarking(){
        BitSet marking = new BitSet();
        for(Map.Entry<Integer, Flow> flow: labeledFlows.entrySet()){
            var value = flow.getValue();
            if(isStart(value.getSource()))
                marking.set(flow.getKey());
        }
        sourceStates.add(marking); // at the moment work when there is only one start event in the model
        return marking;
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

            updateReachabilityGraph(activeMarking, node, newMarking, oldFlows);
        }
        else{
            for(int idx: newFlows){
                BitSet newMarking = (BitSet) activeMarking.clone();
                newMarking.set(idx);
                updateReachabilityGraph(activeMarking, node, newMarking, oldFlows);
            }
        }
    }

    private void updateReachabilityGraph(BitSet activeMarking, BPMNNode node, BitSet newMarking, List<Integer> oldFlows) {
        for(int jdx: oldFlows)
            newMarking.set(jdx, false);

        if(newMarking.cardinality() == 0)
            finalStates.add(activeMarking);
        else {
            Trans transition = new Trans(activeMarking, newMarking, node);

            if(!states.contains(newMarking)){
                states.add(newMarking);
                toBeVisited.add(newMarking);
            }

            transitions.add(transition);

            addIncomingTransition(newMarking, transition);
            addOutgoingTransition(activeMarking, transition);
        }
    }

    private void addIncomingTransition(BitSet marking, Trans transition){
        LinkedHashSet<Trans> newTransition = new LinkedHashSet<>(Collections.singletonList(transition));
        if(!incomingTransitions.containsKey(marking))
            incomingTransitions.put(marking, newTransition);
        else
            incomingTransitions.get(marking).addAll(newTransition);
    }

    private void addOutgoingTransition(BitSet marking, Trans transition){
        LinkedHashSet<Trans> newTransition = new LinkedHashSet(Collections.singleton(transition));
        if(!outgoingTransitions.containsKey(marking))
            outgoingTransitions.put(marking, newTransition);
        else
            outgoingTransitions.get(marking).addAll(newTransition);
    }

    private boolean isStart(BPMNNode node){
        return node instanceof org.processmining.models.graphbased.directed.bpmn.elements.Event &&
                ((Event) node).getEventType().name().equals("START");
    }

    private boolean isEnd(BPMNNode node){
        return node instanceof org.processmining.models.graphbased.directed.bpmn.elements.Event &&
                ((Event) node).getEventType().name().equals("END");
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

class Trans{
    BitSet source;
    BitSet target;
    BPMNNode transition;
    //Boolean isInvisible;

    public Trans(BitSet source, BitSet target, BPMNNode transition){//, boolean isInvisible){
        this.source = (BitSet) source.clone();
        this.target = (BitSet) target.clone();
        this.transition = transition;
        //this.isInvisible = isInvisible;
    }
}