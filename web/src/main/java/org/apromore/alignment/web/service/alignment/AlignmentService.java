package org.apromore.alignment.web.service.alignment;

import java.io.File;
import java.io.FileInputStream;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.apromore.alignment.web.service.filestore.InputFileStoreService;
import org.apromore.alignmentautomaton.AlignmentResult;
import org.apromore.alignmentautomaton.HybridAlignmentGenerator;
import org.apromore.alignmentautomaton.importer.ImportEventLog;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.plugins.bpmn.plugins.BpmnImportPlugin;
import org.deckfour.xes.model.XLog;
import org.springframework.stereotype.Service;

@Service
@RequiredArgsConstructor
@Slf4j
public class AlignmentService {

  private final InputFileStoreService fileStoreService;

  public AlignmentResult runAlignment(String xesFileName, String modelFileName) {

    HybridAlignmentGenerator hybridAlignmentGenerator = new HybridAlignmentGenerator();

    File xes = fileStoreService.retrieveFile(xesFileName);
    File model = fileStoreService.retrieveFile(modelFileName);

    log.info("Generating alignment with files {}, {}", xes.getAbsolutePath(), model.getAbsolutePath());

    BPMNDiagram bpmn;
    XLog xLog;
    try {
      bpmn = new BpmnImportPlugin().importFromStreamToDiagram(new FileInputStream(modelFileName), modelFileName);
      xLog = new ImportEventLog().importEventLog(xes);
    } catch (Exception e) {
      log.error("Error importing files: {}", e.getMessage(), e);
      throw new IllegalStateException(e);
    }

    log.debug("Imported model and log");
    return hybridAlignmentGenerator.computeAlignment(bpmn, xLog);
  }
}