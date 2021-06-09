package au.qut.apromore.ScalableConformanceChecker;

import au.qut.apromore.automaton.Automaton;
import au.qut.apromore.automaton.State;
import au.qut.apromore.automaton.Transition;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.processmining.plugins.petrinet.replayresult.StepTypes;
import org.processmining.plugins.replayer.replayresult.AllSyncReplayResult;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Volodymyr Leno,
 * @version 1.0, 09.06.2021
 */

public class AlignmentPostprocessor {

    private static List<Integer> gatewayIDs;
    private static LinkedHashMap<State, LinkedHashMap<Transition, List<Transition>>> gatewaysInfo;

    public static Map<IntArrayList, AllSyncReplayResult> computeEnhancedAlignments(Map<IntArrayList, AllSyncReplayResult> alignments, Automaton originalAutomaton){

        Map<IntArrayList, AllSyncReplayResult> enhancedAlignments = new HashMap<>();

        getGatewayIds(originalAutomaton);
        gatewaysInfo = computeGateways(originalAutomaton);

        for(Map.Entry<IntArrayList, AllSyncReplayResult> entry : alignments.entrySet()){
            enhancedAlignments.put(entry.getKey(), getEnhancedAlignment(entry.getValue(), originalAutomaton));
        }

        return enhancedAlignments;
    }

    private static AllSyncReplayResult getEnhancedAlignment(AllSyncReplayResult alignment, Automaton automaton){
        State currentState = automaton.source();
        List<List<Object>> nodeInstanceLsts = new ArrayList<>();
        List<List<StepTypes>> stepTypesLsts = new ArrayList<>();
        List<Object> nodeInstances = new ArrayList<>();
        List<StepTypes> stepTypes = new ArrayList<>();

        for(int i = 0; i < alignment.getStepTypesLst().get(0).size(); i++){

            StepTypes stepType = alignment.getStepTypesLst().get(0).get(i);
            String step = alignment.getNodeInstanceLst().get(0).get(i).toString();

            if(stepType == StepTypes.LMGOOD || stepType == StepTypes.MREAL) {
                LinkedHashMap<Transition, List<Transition>> info = gatewaysInfo.get(currentState);

                for (Map.Entry<Transition, List<Transition>> entry : info.entrySet()) {
                    if (entry.getKey() != null && entry.getKey().eventID() == automaton.inverseEventLabels().get(step)) {
                        var gateways = entry.getValue().stream().map(Transition::eventID).collect(Collectors.toList());

                        for (var gateway : gateways) {
                            String move = automaton.eventLabels().get(gateway);
                            nodeInstances.add(move);
                            stepTypes.add(StepTypes.MREAL);
                            currentState = executeMove(automaton, currentState, move, alignment, i-1);
                            }
                        }

                    }
                    nodeInstances.add(step);
                    stepTypes.add(stepType);
                    currentState = executeMove(automaton, currentState, step, alignment, i);
                }

            else{
                nodeInstances.add(step);
                stepTypes.add(stepType);
            }

        }

        if(!currentState.isFinal()){
            var gateways = gatewaysInfo.get(currentState).get(null).stream().map(Transition::eventID).collect(Collectors.toList());
            for(var gateway: gateways){
                nodeInstances.add(automaton.eventLabels().get(gateway));
                stepTypes.add(StepTypes.MREAL);
            }
        }

        nodeInstanceLsts.add(nodeInstances);
        stepTypesLsts.add(stepTypes);

        AllSyncReplayResult enhancedAlignment = new AllSyncReplayResult(nodeInstanceLsts, stepTypesLsts, 0, alignment.isReliable());

        enhancedAlignment.setInfo(alignment.getInfo());
        enhancedAlignment.setTraceIndex(alignment.getTraceIndex());
        return enhancedAlignment;
    }


    private static State executeMove(Automaton automaton, State currentState, String move, AllSyncReplayResult alignment, Integer activePos){
        var transitions = currentState.outgoingTransitions();

        for(var transition: transitions){
            if(transition.eventID() == automaton.inverseEventLabels().get(move) &&
                    fulfillsAlignment(automaton, transition.target(), alignment, activePos))
                return transition.target();
        }

        return null;
    }

    private static boolean fulfillsAlignment(Automaton automaton, State newState, AllSyncReplayResult alignment, Integer activePos){
        String nextModelMove = null;

        for(int i = activePos + 1; i < alignment.getNodeInstanceLst().get(0).size(); i++) {
            var stepType = alignment.getStepTypesLst().get(0).get(i);
            if (stepType == StepTypes.LMGOOD || stepType == StepTypes.MREAL) {
                nextModelMove = alignment.getNodeInstanceLst().get(0).get(i).toString();
                break;
            }
        }

        var transitions = gatewaysInfo.get(newState);

        for(Transition transition: transitions.keySet()) {
            if(transition == null && nextModelMove == null)
                return true;
            else if(transition != null){
                var evId = transition.eventID();
                var moveId = automaton.inverseEventLabels().get(nextModelMove);
                if (evId == moveId)
                    return true;
            }
        }

        return false;
    }

    private static LinkedHashMap<State, LinkedHashMap<Transition, List<Transition>>> computeGateways(Automaton automaton){
        LinkedHashMap<State, LinkedHashMap<Transition, List<Transition>>> info = new LinkedHashMap<>();

        for (Map.Entry<Integer, State> entry : automaton.states().entrySet()) {
            var value = entry.getValue();
            info.put(value, getGateways(value));
        }

        return info;
    }

    private static LinkedHashMap<Transition, List<Transition>> getGateways(State state){
        LinkedHashMap<Transition, List<Transition>> gateways = new LinkedHashMap<>();

        Queue<List<Transition>> queue = new LinkedList<>();

        for(var transition: state.outgoingTransitions()){
            List<Transition> path = new ArrayList<>(Collections.singleton(transition));
            queue.offer(path);
        }

        while(!queue.isEmpty()){
            List<Transition> activePath = queue.poll();
            Transition last = activePath.get(activePath.size() - 1);

            if(!gatewayIDs.contains(last.eventID())){
                gateways.put(last, activePath.subList(0, activePath.size() - 1));
            }

            else{
                List<Transition> lastNode = last.target().outgoingTransitions();

                if(lastNode.size() > 0){

                    for(Transition transition: lastNode){
                        if(!activePath.contains(transition)){
                            List<Transition> newPath = new ArrayList<>(activePath);
                            newPath.add(transition);
                            queue.offer(newPath);
                        }
                    }

                }
                else
                    gateways.put(null, activePath);
            }
        }

        return gateways;
    }

    private static void getGatewayIds(Automaton automaton){
        gatewayIDs = new ArrayList<>();

        for (Map.Entry<Integer, String> entry : automaton.eventLabels().entrySet()) {
            var idx = entry.getKey();
            var label = entry.getValue();
            if(label.startsWith("gateway"))
                gatewayIDs.add(idx);
        }

    }
}
