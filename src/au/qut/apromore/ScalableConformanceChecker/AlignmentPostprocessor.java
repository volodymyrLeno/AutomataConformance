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

    public static Map<IntArrayList, AllSyncReplayResult> computeEnhancedAlignments(Map<IntArrayList, AllSyncReplayResult> alignments, Automaton originalAutomaton, Integer lookupStepsAhead){

        Map<IntArrayList, AllSyncReplayResult> enhancedAlignments = new HashMap<>();
        Map<IntArrayList, AllSyncReplayResult> notParsableAlignments = new HashMap<>();

        getGatewayIds(originalAutomaton);
        gatewaysInfo = computeGateways(originalAutomaton);

        for(Map.Entry<IntArrayList, AllSyncReplayResult> entry : alignments.entrySet()){
            var enhancedAlignment = getEnhancedAlignment(entry.getValue(), originalAutomaton, lookupStepsAhead);
            if(enhancedAlignment != null)
                enhancedAlignments.put(entry.getKey(), enhancedAlignment);
            else
                notParsableAlignments.put(entry.getKey(), entry.getValue());
        }

        return enhancedAlignments;
    }

    private static AllSyncReplayResult getEnhancedAlignment(AllSyncReplayResult alignment, Automaton automaton, Integer lookupStepsAhead){
        State currentState = automaton.source();
        List<List<Object>> nodeInstanceLsts = new ArrayList<>();
        List<List<StepTypes>> stepTypesLsts = new ArrayList<>();
        List<Object> nodeInstances = new ArrayList<>();
        List<StepTypes> stepTypes = new ArrayList<>();

        for(int i = 0; i < alignment.getStepTypesLst().get(0).size(); i++){

            StepTypes stepType = alignment.getStepTypesLst().get(0).get(i);
            String step = alignment.getNodeInstanceLst().get(0).get(i).toString();

            if(stepType == StepTypes.LMGOOD || stepType == StepTypes.MREAL) {

                if(currentState == null)
                    return null;

                LinkedHashMap<Transition, List<Transition>> info = gatewaysInfo.get(currentState);

                for (Map.Entry<Transition, List<Transition>> entry : info.entrySet()) {
                    if (entry.getKey() != null && entry.getKey().eventID() == automaton.inverseEventLabels().get(step) &&
                    fitsAlignmentWithLookup(automaton, entry.getKey().target(), alignment, i, lookupStepsAhead)){
                        var gateways = entry.getValue().stream().map(Transition::eventID).collect(Collectors.toList());

                        for (var gateway : gateways) {
                            String move = automaton.eventLabels().get(gateway);
                            nodeInstances.add(move);
                            stepTypes.add(StepTypes.MREAL);
                        }

                        currentState = entry.getKey().source();

                        break;
                        }

                    }
                    nodeInstances.add(step);
                    stepTypes.add(stepType);
                    currentState = executeMove(automaton, currentState, step);
                }

            else{
                nodeInstances.add(step);
                stepTypes.add(stepType);
            }

        }

        if(currentState != null && !currentState.isFinal()){
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

    private static State executeMove(Automaton automaton, State currentState, String move){
        var transitions = currentState.outgoingTransitions();

        for(var transition: transitions){
            if(transition.eventID() == automaton.inverseEventLabels().get(move))
                return transition.target();
        }

        return null;
    }

    private static boolean fitsAlignment(Automaton automaton, State newState, AllSyncReplayResult alignment, Integer activePos){
        String nextModelMove = null;

        for(int i = activePos + 1; i < alignment.getNodeInstanceLst().get(0).size(); i++) {
            var stepType = alignment.getStepTypesLst().get(0).get(i);
            if (stepType == StepTypes.LMGOOD || stepType == StepTypes.MREAL) {
                nextModelMove = alignment.getNodeInstanceLst().get(0).get(i).toString();
                break;
            }
        }

        if(newState.isFinal() && nextModelMove == null)
            return true;

        var transitions = gatewaysInfo.get(newState);

        if(nextModelMove == null && transitions.containsKey(null))
            return true;

        for(Transition transition: transitions.keySet()) {
            if(transition != null){
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

    private static boolean fitsAlignmentWithLookup(Automaton automaton, State newState, AllSyncReplayResult alignment, Integer activePos, Integer stepsAhead){
        if(stepsAhead == 1)
            return fitsAlignment(automaton, newState, alignment, activePos);
        else{
            List<String> nextModelMoves = new ArrayList<>();
            for(int i = activePos + 1; i < alignment.getNodeInstanceLst().get(0).size(); i++){
                if(nextModelMoves.size() < stepsAhead){
                    var stepType = alignment.getStepTypesLst().get(0).get(i);
                    if(stepType == StepTypes.LMGOOD || stepType == StepTypes.MREAL){
                            nextModelMoves.add(alignment.getNodeInstanceLst().get(0).get(i).toString());
                        }
                    }
                else
                    break;
            }

            var paths = getPaths(automaton, newState, stepsAhead);

            if(nextModelMoves.size() == 0){
                if(paths.size() == 0)
                    return true;
                else{
                    for(var path: paths){
                        if(path.size() == 0)
                            return true;
                    }
                    return false;
                }
            }
            else
                return paths.contains(nextModelMoves);
        }
    }
    
    private static List<List<String>> getPaths(Automaton automaton, State state, Integer length){
        List<List<String>> paths = new ArrayList<>();

        Queue<List<Transition>> queue = new LinkedList<>();

        for(var transition: gatewaysInfo.get(state).keySet()){
            List<Transition> path = new ArrayList<>(Collections.singleton(transition));
            queue.offer(path);
        }

        while(!queue.isEmpty()){
            List<Transition> activePath = queue.poll();
            Transition last = activePath.get(activePath.size() - 1);

            if(activePath.size() == length){
                List<String> path = new ArrayList<>();
                for(var transition: activePath){
                    if(transition != null)
                        path.add(automaton.eventLabels().get(transition.eventID()));
                }
                paths.add(path);
            }

            else{
                if(last != null){
                    List<Transition> lastNode = new ArrayList<>(gatewaysInfo.get(last.target()).keySet());

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
                        paths.add(activePath.stream().map(el -> automaton.eventLabels().get(el.eventID())).collect(Collectors.toList()));
                }
            }
        }

        return paths;
    }
}