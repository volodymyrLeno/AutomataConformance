package org.apromore.alignmentautomaton;

import lombok.Data;
import lombok.NonNull;
import lombok.RequiredArgsConstructor;
import org.processmining.plugins.petrinet.replayresult.PNMatchInstancesRepResult;

@Data
@RequiredArgsConstructor
public class AlignmentResult {

  @NonNull
  private final PNMatchInstancesRepResult alignmentResults;
}
