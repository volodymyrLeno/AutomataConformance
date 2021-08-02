package org.apromore.alignmentautomaton.api;

import lombok.Data;
import lombok.NonNull;

@Data
public class FileStoreResponse {

  @NonNull
  private final String fileName;
}
