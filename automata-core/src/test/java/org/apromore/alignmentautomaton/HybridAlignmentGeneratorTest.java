package org.apromore.alignmentautomaton;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;
import com.google.common.io.Resources;
import org.apromore.alignmentautomaton.importer.ImportEventLog;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.plugins.bpmn.plugins.BpmnImportPlugin;
import org.deckfour.xes.model.XLog;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;

class HybridAlignmentGeneratorTest {

  private static final ObjectMapper mapper = new ObjectMapper().findAndRegisterModules()
      .configure(SerializationFeature.INDENT_OUTPUT, true);

  @Test
  void computeAlignmentHospitalBillingBPMN() throws Exception {
    runTestBPMN("Hospital_Billing.xes.gz", "Hospital_Billing.bpmn", "build/hb.json");
  }

  @Test
  @Disabled
  void loan() throws Exception {
    runTestBPMN("loan.xes.gz", "loan.bpmn", "build/loan.json");
  }

  @Test
  void simpleBPMN() throws Exception {
    runTestBPMN("simple.xes", "simple.bpmn", "build/simple.json");
  }

  @Test
  void fittingTrace() throws Exception{
    AlignmentResult alignmentResult = runTestBPMN("fittingTrace.xes", "simple.bpmn", "build/simple.json");
    double traceFitness = alignmentResult.getAlignmentResults().get(0).getInfo().get("Trace Fitness");
    assertEquals(1.0, traceFitness);
  }

  @Test
  void deviatingTrace() throws Exception{
    AlignmentResult alignmentResult = runTestBPMN("deviatingTrace.xes", "simple.bpmn", "build/simple.json");
    double traceFitness = alignmentResult.getAlignmentResults().get(0).getInfo().get("Trace Fitness");
    assert traceFitness < 1.0;
  }

  private AlignmentResult runTestBPMN(final String xesF, final String modelF, String output) throws Exception {
    File xes = new File(Resources.getResource("fixtures/" + xesF).getFile());
    File modelFile = new File(Resources.getResource("fixtures/" + modelF).getFile());

    XLog xLog = new ImportEventLog().importEventLog(xes);
    BPMNDiagram bpmn = new BpmnImportPlugin().importFromStreamToDiagram(new FileInputStream(modelFile), modelF);
    AlignmentResult alignmentResult = new HybridAlignmentGenerator().computeAlignment(bpmn, xLog);

    try (BufferedWriter w = new BufferedWriter(new FileWriter(output))) {
      mapper.writeValue(w, alignmentResult);
    }

    return alignmentResult;
  }
}