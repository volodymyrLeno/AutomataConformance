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
 * @version 2.0, 01.07.2021
 */

public class AlignmentPostprocessor {

    private static List<Integer> tauIDs;
    private static LinkedHashMap<State, LinkedHashMap<Transition, List<Transition>>> gatewaysInfo;

    public static Map<IntArrayList, AllSyncReplayResult> computeEnhancedAlignments(Map<IntArrayList, AllSyncReplayResult> alignments, Automaton originalAutomaton, HashMap<String, String> idsMapping, HashMap<String, List<String>> artificialGatewaysInfo){
        Map<IntArrayList, AllSyncReplayResult> enhancedAlignments = new HashMap<>();
        Map<IntArrayList, AllSyncReplayResult> notParsableAlignments = new HashMap<>();

        getTauIds(originalAutomaton);
        gatewaysInfo = computeGatewaysInfo(originalAutomaton);

        for(Map.Entry<IntArrayList, AllSyncReplayResult> entry : alignments.entrySet()){
            try{
                var enhancedAlignment = getEnhancedAlignment(entry.getValue(), originalAutomaton, idsMapping, artificialGatewaysInfo);
                enhancedAlignments.put(entry.getKey(), enhancedAlignment);
            }
            catch(Exception e){
                notParsableAlignments.put(entry.getKey(), entry.getValue());
            }
        }

        return enhancedAlignments;
    }

    public static List<AllSyncReplayResult> computeEnhancedAlignments(List<AllSyncReplayResult> alignments, Automaton originalAutomaton, HashMap<String, String> idsMapping, HashMap<String, List<String>> artificialGatewaysInfo){
        List<AllSyncReplayResult> enhancedAlignments = new ArrayList<>();
        List<AllSyncReplayResult> notParsableAlignments = new ArrayList<>();

        getTauIds(originalAutomaton);
        gatewaysInfo = computeGatewaysInfo(originalAutomaton);

        for(var alignment : alignments){
            try{
                var enhancedAlignment = getEnhancedAlignment(alignment, originalAutomaton, idsMapping, artificialGatewaysInfo);
                enhancedAlignments.add(enhancedAlignment);
            }
            catch(Exception e){
                notParsableAlignments.add(alignment);
            }
        }

        return enhancedAlignments;
    }

    private static AllSyncReplayResult getEnhancedAlignment(AllSyncReplayResult alignment, Automaton automaton, HashMap<String, String> idsMapping, HashMap<String, List<String>> artificialGatewaysInfo){
        List<List<Object>> nodeInstanceLsts = new ArrayList<>();
        List<List<StepTypes>> stepTypesLsts = new ArrayList<>();

        State currentState = automaton.source();
        List<Object> nodeInstances = new ArrayList<>();
        List<StepTypes> stepTypes = new ArrayList<>();
        List<Transition> avoid = new ArrayList<>();
        Stack<Transition> path = new Stack<>();

        for(int i = 0; i < alignment.getStepTypesLst().get(0).size(); i++){
            var stepType = alignment.getStepTypesLst().get(0).get(i);
            var step = alignment.getNodeInstanceLst().get(0).get(i).toString();

            if(stepType == StepTypes.LMGOOD || stepType == StepTypes.MREAL) {
                var stepID = automaton.inverseEventLabels().get(step);
                LinkedHashMap<Transition, List<Transition>> info = gatewaysInfo.get(currentState);

                var availableTransitions = info.keySet().stream().filter(transition -> transition != null &&
                        !avoid.contains(transition)).collect(Collectors.toList());
                var availableMoves = availableTransitions.stream().map(Transition::eventID).collect(Collectors.toList());

                int idx = availableMoves.indexOf(stepID);

                Transition nextTransition;

                if(idx != -1)
                    nextTransition = availableTransitions.get(idx);
                else{
                    while(idx == -1){
                        var lastTransition = path.pop();
                        avoid.add(lastTransition);

                        if(!tauIDs.contains(lastTransition.eventID())){
                            for(int j = i; j >= 0; j--){
                                stepType = alignment.getStepTypesLst().get(0).get(j);
                                if(stepType == StepTypes.LMGOOD || stepType == StepTypes.MREAL) {
                                    i--;
                                    break;
                                }
                                else
                                    i--;
                            }
                        }

                        for(int j = i; j >= 0; j--){
                            stepType = alignment.getStepTypesLst().get(0).get(j);
                            if(stepType == StepTypes.LMGOOD || stepType == StepTypes.MREAL) {
                                step = alignment.getNodeInstanceLst().get(0).get(j).toString();
                                stepID = automaton.inverseEventLabels().get(step);
                                break;
                            }
                        }

                        var lastMove = automaton.eventLabels().get(lastTransition.eventID());

                        var lastIndex = nodeInstances.lastIndexOf(lastMove);
                        nodeInstances.remove(lastIndex);
                        stepTypes.remove(lastIndex);

                        currentState = lastTransition.source();
                        info = gatewaysInfo.get(currentState);
                        availableTransitions = info.keySet().stream().filter(transition -> transition != null &&
                                !avoid.contains(transition)).collect(Collectors.toList());
                        availableMoves = availableTransitions.stream().map(Transition::eventID).collect(Collectors.toList());
                        idx = availableMoves.indexOf(stepID);
                    }

                    nextTransition = availableTransitions.get(idx);
                }

                for (Transition transition: info.get(nextTransition)) {
                    var gateway = transition.eventID();
                    String move = automaton.eventLabels().get(gateway);
                    nodeInstances.add(move);
                    stepTypes.add(StepTypes.LMGOOD);

                    path.push(transition);
                }

                currentState = nextTransition.source();

                nodeInstances.add(step);
                stepTypes.add(stepType);
                currentState = executeMove(automaton, currentState, step);

                path.push(nextTransition);
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
                stepTypes.add(StepTypes.LMGOOD);
            }
        }

        if(!nodeInstances.get(0).toString().startsWith("startEvent ")){
            int i = 1;
            var node = nodeInstances.get(i);
            var step = stepTypes.get(i);
            while(!nodeInstances.get(i).toString().startsWith("startEvent ")){
                i++;
                node = nodeInstances.get(i);
                step = stepTypes.get(i);
            }
            nodeInstances.remove(i);
            nodeInstances.add(0, node);
            stepTypes.remove(i);
            stepTypes.add(0, step);
        }

        for(int i = 0; i < nodeInstances.size(); i++){
            String currentLabel = nodeInstances.get(i).toString();
            if(currentLabel.startsWith("gateway "))
                nodeInstances.set(i, currentLabel.substring(("gateway ").length()));
            else if(currentLabel.startsWith("event "))
                nodeInstances.set(i, currentLabel.substring(("event ").length()));
            else if(currentLabel.startsWith("startEvent "))
                nodeInstances.set(i, currentLabel.substring(("startEvent ").length()));
            else if(currentLabel.startsWith("endEvent "))
                nodeInstances.set(i, currentLabel.substring(("endEvent ").length()));
            else if(idsMapping.containsKey(currentLabel))
                nodeInstances.set(i, idsMapping.get(currentLabel));
        }

        if(artificialGatewaysInfo != null)
            removeArtificialGateways(nodeInstances, stepTypes, artificialGatewaysInfo);

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

    private static LinkedHashMap<State, LinkedHashMap<Transition, List<Transition>>> computeGatewaysInfo(Automaton automaton){
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

            if(!tauIDs.contains(last.eventID())){
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

    private static void getTauIds(Automaton automaton){
        tauIDs = new ArrayList<>();

        for (Map.Entry<Integer, String> entry : automaton.eventLabels().entrySet()) {
            var idx = entry.getKey();
            var label = entry.getValue();
            if(label.startsWith("gateway") || label.startsWith("startEvent ") || label.startsWith("endEvent "))
                tauIDs.add(idx);
        }
    }

    private static void removeArtificialGateways(List<Object> nodeInstanceLst, List<StepTypes> stepTypesLst, HashMap<String, List<String>> artificialGatewaysInfo){
        List<Object> nodeInstances = new ArrayList<>();
        List<StepTypes> stepTypes = new ArrayList<>();
        String entryPoint = null;

        HashMap<String, String> artificialGatewaysHelper = new HashMap<>();
        for(Map.Entry<String, List<String>> entry: artificialGatewaysInfo.entrySet()){
            for(var value: entry.getValue())
                artificialGatewaysHelper.put(value, entry.getKey());
        }

        for(int i = 0; i < nodeInstanceLst.size(); i++){
            String nodeInstance = nodeInstanceLst.get(i).toString();
            if(!artificialGatewaysHelper.containsKey(nodeInstance)){
                nodeInstances.add(nodeInstanceLst.get(i));
                stepTypes.add(stepTypesLst.get(i));
            }
            else{
                if(entryPoint == null){
                    nodeInstances.add(artificialGatewaysHelper.get(nodeInstance));
                    stepTypes.add(stepTypesLst.get(i));
                    entryPoint = nodeInstance;
                }
                else{
                    var tempList = artificialGatewaysInfo.get(artificialGatewaysHelper.get(nodeInstance));
                    if(!tempList.contains(entryPoint)){
                        nodeInstances.add(artificialGatewaysHelper.get(nodeInstance));
                        stepTypes.add(stepTypesLst.get(i));
                        entryPoint = nodeInstance;
                    }
                    else if(entryPoint.equals(nodeInstance)){
                        nodeInstances.add(artificialGatewaysHelper.get(nodeInstance));
                        stepTypes.add(stepTypesLst.get(i));
                    }
                }
            }
        }
        nodeInstanceLst.clear();
        stepTypesLst.clear();

        nodeInstanceLst.addAll(nodeInstances);
        stepTypesLst.addAll(stepTypes);
    }
}