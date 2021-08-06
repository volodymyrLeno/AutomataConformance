package org.apromore.alignment.web.controller;

import io.swagger.annotations.ApiOperation;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.apromore.alignmentautomaton.api.RESTEndpointsConfig;
import org.apromore.alignment.web.service.alignment.AlignmentService;
import org.apromore.alignmentautomaton.AlignmentResult;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;

@Slf4j
@RestController
@RequiredArgsConstructor
public class AlignmentController {

  private final AlignmentService alignmentService;

  @PostMapping(RESTEndpointsConfig.ALIGNMENT_PATH)
  @ApiOperation(value = "Generated an alignment from a XES input and a model (BPMN or PNML) file")
  public @ResponseBody
  AlignmentResult genAlignment(@RequestParam String xesFileName, @RequestParam String modelFileName, @RequestParam int maxFanout) throws Exception {
    return alignmentService.runAlignment(xesFileName, modelFileName, maxFanout);
  }
}
