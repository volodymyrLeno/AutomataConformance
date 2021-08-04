package org.apromore.alignmentautomaton;

public enum StepType {
  LMGOOD("Sync move"),
  LMNOGOOD("False sync move"),
  L("Log move"),
  MINVI("Invisible step"),
  MREAL("Model move"),
  LMREPLACED("Replaced step"),
  LMSWAPPED("Swapped step");

  private final String descr;

  StepType(String descr) {
    this.descr = descr;
  }

  public String toString() {
    return this.descr;
  }

}
