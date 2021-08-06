package org.apromore.alignmentautomaton;

import java.util.Map;
import java.util.stream.Collectors;
import lombok.NonNull;
import org.apromore.alignmentautomaton.ScalableConformanceChecker.HybridConformanceChecker;
import org.apromore.alignmentautomaton.importer.BPMNPreprocessor;
import org.apromore.alignmentautomaton.importer.DecomposingTRImporter;
import org.apromore.alignmentautomaton.postprocessor.AlignmentPostprocessor;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Flow;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Gateway.GatewayType;
import org.deckfour.xes.model.XLog;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.processmining.plugins.replayer.replayresult.AllSyncReplayResult;

public class HybridAlignmentGenerator implements AlignmentGenerator {

  private static final int NUM_THREADS = 4;

  public static final int DEFAULT_MAX_FANOUT = 4;

  @Override
  public AlignmentResult computeAlignment(@NonNull BPMNDiagram bpmn, @NonNull XLog xLog) {
    return computeAlignment(bpmn, xLog, false, DEFAULT_MAX_FANOUT);
  }

  @Override
  public AlignmentResult computeAlignment(@NonNull BPMNDiagram bpmn, @NonNull XLog xLog, boolean filterModel,
      int maxFanout) {
    try {
      BPMNDiagram filteredModel = filterModel ? new BPMNPreprocessor().filterModel(bpmn, xLog, maxFanout) : bpmn;
      DecomposingTRImporter importer = new DecomposingTRImporter();
      importer.importAndDecomposeModelAndLogForConformanceChecking(filteredModel, xLog);
      boolean containsORSplits = filteredModel.getGateways().stream().anyMatch(
          gateway -> gateway.getGatewayType() == GatewayType.INCLUSIVE
              && filteredModel.getOutEdges(gateway).stream().filter(edge -> edge instanceof Flow).count() > 1);
      HybridConformanceChecker checker = new HybridConformanceChecker(importer, containsORSplits, NUM_THREADS);

      Map<IntArrayList, AllSyncReplayResult> res = AlignmentPostprocessor
          .computeEnhancedAlignments(checker.traceAlignmentsMapping, importer.originalModelAutomaton,
              importer.idsMapping, importer.artificialGatewaysInfo);
      return convertResult(res);
    } catch (Exception ex) {
      throw new AlignmentGenerationException("Internal error generating alignment, cause: " + ex.getMessage(), ex);
    }
  }

  private AlignmentResult convertResult(Map<IntArrayList, AllSyncReplayResult> res) {

    return new AlignmentResult(
        res.values().stream().map(HybridAlignmentGenerator::mapReplayResult).collect(Collectors.toList()));
  }

  private static ReplayResult mapReplayResult(AllSyncReplayResult origReplayResult) {
    return new ReplayResult(
        origReplayResult.getNodeInstanceLst().get(0).stream().map(Object::toString).collect(Collectors.toList()),
        origReplayResult.getStepTypesLst().get(0).stream().map(s -> StepType.valueOf(s.name()))
            .collect(Collectors.toList()), origReplayResult.getTraceIndex(), origReplayResult.isReliable(),
        origReplayResult.getInfo(), origReplayResult.getSingleInfo());
  }
}
