package org.apromore.alignmentautomaton;

import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.deckfour.xes.model.XLog;

public interface AlignmentGenerator {

  AlignmentResult computeAlignment(BPMNDiagram bpmn, XLog xLog, int maxFanout);
}
