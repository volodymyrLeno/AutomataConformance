package org.apromore.alignmentautomaton.ScalableConformanceChecker;

import lombok.Data;
import lombok.NoArgsConstructor;
import lombok.NonNull;
import lombok.RequiredArgsConstructor;
import java.util.ArrayList;
import java.util.List;

@Data
@RequiredArgsConstructor
public class ConformanceResult {
  @NonNull
  private List<String> green = new ArrayList<>();
  @NonNull
  private List<String> grey = new ArrayList<>();
  private List<RedSection> red = new ArrayList<>();

  public void addGreen(String value){ green.add(value); }
  public void addGrey(String value){ grey.add(value); }
  public void addRed(RedSection value){ red.add(value); }

  @Data
  @NoArgsConstructor
  @RequiredArgsConstructor
  public class RedSection {
    @NonNull
    private String startPoint;
    @NonNull
    private String endpoint;
    @NonNull
    private List<String> activities = new ArrayList();

    public void addActivity(String activity){ activities.add(activity); }
    public void setStartPoint(String startPoint){ this.startPoint = startPoint; }
    public void setEndPoint(String endPoint){ this.endpoint = endPoint; }
  }
}
