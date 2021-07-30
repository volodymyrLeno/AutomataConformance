package org.apromore.alignmentautomaton;

import java.io.IOException;
import java.util.Map;
import lombok.NonNull;
import org.apromore.alignmentautomaton.ScalableConformanceChecker.HybridConformanceChecker;
import org.apromore.alignmentautomaton.importer.DecomposingTRImporter;
import org.apromore.alignmentautomaton.postprocessor.AlignmentPostprocessor;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.deckfour.xes.model.XLog;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.processmining.framework.connections.ConnectionCannotBeObtained;
import org.processmining.models.graphbased.directed.petrinet.Petrinet;
import org.processmining.models.semantics.petrinet.Marking;
import org.processmining.plugins.petrinet.replayresult.PNMatchInstancesRepResult;
import org.processmining.plugins.replayer.replayresult.AllSyncReplayResult;

public class HybridAlignmentGenerator implements AlignmentGenerator {

  private static final int NUM_THREADS = 4;

  public AlignmentResult computeAlignment(Petrinet petrinet, Marking marking, XLog xLog) {
    try {
      DecomposingTRImporter importer = new DecomposingTRImporter();
      importer.importAndDecomposeModelAndLogForConformanceChecking(petrinet, marking, xLog);
      HybridConformanceChecker checker = new HybridConformanceChecker(importer, NUM_THREADS);
      return new AlignmentResult(checker.getAlignments());
    } catch (ConnectionCannotBeObtained | IOException ex) {
      throw new AlignmentGenerationException("Internal error generating alignment, cause: " + ex.getMessage(), ex);
    }
  }

  @Override
  public AlignmentResult computeAlignment(@NonNull BPMNDiagram bpmn, @NonNull XLog xLog) {
    try {
      DecomposingTRImporter importer = new DecomposingTRImporter();
      importer.importAndDecomposeModelAndLogForConformanceChecking(bpmn, xLog);
      HybridConformanceChecker checker = new HybridConformanceChecker(importer, NUM_THREADS);

      Map<IntArrayList, AllSyncReplayResult> res = AlignmentPostprocessor
          .computeEnhancedAlignments(checker.traceAlignmentsMapping, importer.originalModelAutomaton,
              importer.idsMapping);
      return new AlignmentResult(new PNMatchInstancesRepResult(res.values()));
    } catch (Exception ex) {
      throw new AlignmentGenerationException("Internal error generating alignment, cause: " + ex.getMessage(), ex);
    }
  }
}
