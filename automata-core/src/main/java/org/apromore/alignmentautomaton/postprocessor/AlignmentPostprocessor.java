package org.apromore.alignmentautomaton.postprocessor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Stack;
import java.util.stream.Collectors;
import org.apromore.alignmentautomaton.automaton.Automaton;
import org.apromore.alignmentautomaton.automaton.State;
import org.apromore.alignmentautomaton.automaton.Transition;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.processmining.plugins.petrinet.replayresult.StepTypes;
import org.processmining.plugins.replayer.replayresult.AllSyncReplayResult;

/**
 * @author Volodymyr Leno,
 * @version 2.0, 01.07.2021
 */

public class AlignmentPostprocessor {

  private static List<Integer> gatewayIDs;
  private static LinkedHashMap<State, LinkedHashMap<Transition, List<Transition>>> gatewaysInfo;

  public static Map<IntArrayList, AllSyncReplayResult> computeEnhancedAlignments(Map<IntArrayList, AllSyncReplayResult> alignments, Automaton originalAutomaton, HashMap<String, String> idsMapping){
    Map<IntArrayList, AllSyncReplayResult> enhancedAlignments = new HashMap<>();
    Map<IntArrayList, AllSyncReplayResult> notParsableAlignments = new HashMap<>();

    getGatewayIds(originalAutomaton);
    gatewaysInfo = computeGatewaysInfo(originalAutomaton);

    for(Map.Entry<IntArrayList, AllSyncReplayResult> entry : alignments.entrySet()){
      try{
        var enhancedAlignment = getEnhancedAlignment(entry.getValue(), originalAutomaton, idsMapping);
        enhancedAlignments.put(entry.getKey(), enhancedAlignment);
      }
      catch(Exception e){
        notParsableAlignments.put(entry.getKey(), entry.getValue());
      }
    }

    return enhancedAlignments;
  }

  public static List<AllSyncReplayResult> computeEnhancedAlignments(List<AllSyncReplayResult> alignments, Automaton originalAutomaton, HashMap<String, String> idsMapping){
    List<AllSyncReplayResult> enhancedAlignments = new ArrayList<>();
    List<AllSyncReplayResult> notParsableAlignments = new ArrayList<>();

    getGatewayIds(originalAutomaton);
    gatewaysInfo = computeGatewaysInfo(originalAutomaton);

    for(var alignment : alignments){
      try{
        var enhancedAlignment = getEnhancedAlignment(alignment, originalAutomaton, idsMapping);
        enhancedAlignments.add(enhancedAlignment);
      }
      catch(Exception e){
        notParsableAlignments.add(alignment);
      }
    }

    return enhancedAlignments;
  }

  private static AllSyncReplayResult getEnhancedAlignment(AllSyncReplayResult alignment, Automaton automaton, HashMap<String, String> idsMapping){
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

            if(!gatewayIDs.contains(lastTransition.eventID())){
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
          stepTypes.add(StepTypes.MREAL);

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
        stepTypes.add(StepTypes.MREAL);
      }
    }

    for(int i = 0; i < nodeInstances.size(); i++){
      String currentLabel = nodeInstances.get(i).toString();
      if(currentLabel.startsWith("gateway "))
        nodeInstances.set(i, currentLabel.substring(("gateway ").length()));
      else if(currentLabel.startsWith("event "))
        nodeInstances.set(i, currentLabel.substring(("event ").length()));
      else if(idsMapping.containsKey(currentLabel))
        nodeInstances.set(i, idsMapping.get(currentLabel));
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