package org.apromore.alignmentautomaton;

import java.util.List;
import lombok.Data;
import lombok.NonNull;
import lombok.RequiredArgsConstructor;

@Data
@RequiredArgsConstructor
public class AlignmentResult {

  @NonNull
  private final List<ReplayResult> alignmentResults;
}
