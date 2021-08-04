package org.apromore.alignmentautomaton;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import lombok.Data;
import lombok.NoArgsConstructor;
import lombok.NonNull;

@Data
@NoArgsConstructor
public class ReplayResult {

  @NonNull
  private List<String> nodeInstances = new ArrayList<>();

  @NonNull
  private List<StepType> stepTypes = new ArrayList<>();

  @NonNull
  private SortedSet<Integer> traceIndex = new TreeSet<>();

  private boolean reliable = false;

  @NonNull
  private Map<String, Double> info = new HashMap<>();

  @NonNull
  private List<Map<String, Double>> singleInfoLst = new ArrayList<>();

  public ReplayResult(List<String> nodeInstances, List<StepType> stepTypes, int traceIndex, boolean reliable) {
    this(nodeInstances, stepTypes, new TreeSet<>(), reliable, new HashMap<>(), new ArrayList<>());
    addNewCase(traceIndex);
  }

  public ReplayResult(List<String> nodeInstances, List<StepType> stepTypes, SortedSet<Integer> traceIndex,
      boolean reliable, Map<String, Double> info, List<Map<String, Double>> singleInfoLst) {
    this.nodeInstances = nodeInstances;
    this.stepTypes = stepTypes;
    this.traceIndex = traceIndex;
    this.reliable = reliable;
    this.info = info;
    this.singleInfoLst = singleInfoLst;
  }

  public void addNewCase(int traceIndex) {
    this.traceIndex.add(traceIndex);
  }

  public void addSingleInfo(Map<String, Double> singleInfo) {
    this.singleInfoLst.add(singleInfo);
  }
}
