package org.apromore.alignmentautomaton;

import com.google.common.io.Resources;
import org.apromore.alignmentautomaton.ScalableConformanceChecker.AlignmentAnalyzer;
import org.apromore.alignmentautomaton.ScalableConformanceChecker.ConformanceResult;
import org.apromore.alignmentautomaton.importer.ImportEventLog;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.plugins.bpmn.plugins.BpmnImportPlugin;
import org.deckfour.xes.model.XLog;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;
import java.io.File;
import java.io.FileInputStream;

public class AlignmentAnalyzerTest {
  @Test
  void test1() throws Exception{
    runTestConformanceChecking("simple1.xes", "simple.bpmn", 12, 0, 1);
  }

  @Test
  void test2() throws Exception{
    runTestConformanceChecking("simple2.xes", "simple.bpmn", 15, 3, 2);
  }

  @Test
  void test3() throws Exception{
    runTestConformanceChecking("simple3.xes", "simple.bpmn", 10, 3, 1);
  }

  @Test
  void test4() throws Exception{
    runTestConformanceChecking("simple4.xes", "simple.bpmn", 10, 3, 0);
  }

  private void runTestConformanceChecking(final String xesF, final String modelF, final int greens, final int greys, final int reds) throws Exception{
    File xes = new File(Resources.getResource("fixtures/" + xesF).getFile());
    File modelFile = new File(Resources.getResource("fixtures/" + modelF).getFile());
    XLog xLog = new ImportEventLog().importEventLog(xes);
    BPMNDiagram bpmn = new BpmnImportPlugin().importFromStreamToDiagram(new FileInputStream(modelFile), modelF);
    AlignmentResult alignmentResult = new HybridAlignmentGenerator().computeAlignment(bpmn, xLog);
    ConformanceResult conformanceResult = AlignmentAnalyzer.extractDelta(bpmn, alignmentResult.getAlignmentResults().get(0));
    assertEquals(greens, conformanceResult.getGreen().size());
    assertEquals(greys, conformanceResult.getGrey().size());
    assertEquals(reds, conformanceResult.getRed().size());
  }
}
