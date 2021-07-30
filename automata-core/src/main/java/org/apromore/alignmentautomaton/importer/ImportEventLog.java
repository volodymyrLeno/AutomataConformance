package org.apromore.alignmentautomaton.importer;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import lombok.NonNull;
import name.kazennikov.dafsa.AbstractIntDAFSA;
import name.kazennikov.dafsa.IntDAFSAInt;
import org.apromore.alignmentautomaton.automaton.Automaton;
import org.apromore.alignmentautomaton.automaton.State;
import org.apromore.alignmentautomaton.automaton.Transition;
import org.deckfour.xes.extension.XExtension;
import org.deckfour.xes.extension.std.XConceptExtension;
import org.deckfour.xes.factory.XFactory;
import org.deckfour.xes.factory.XFactoryNaiveImpl;
import org.deckfour.xes.in.XesXmlGZIPParser;
import org.deckfour.xes.in.XesXmlParser;
import org.deckfour.xes.model.XAttributeLiteral;
import org.deckfour.xes.model.XAttributeMap;
import org.deckfour.xes.model.XEvent;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.XTrace;
import org.eclipse.collections.impl.list.mutable.FastList;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.UnifiedMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntIntHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.ObjectIntHashMap;
import org.eclipse.collections.impl.set.mutable.UnifiedSet;
import org.eclipse.collections.impl.set.mutable.primitive.IntHashSet;

/*
 * Copyright © 2009-2017 The Apromore Initiative.
 *
 * This file is part of "Apromore".
 *
 * "Apromore" is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation; either version 3 of the
 * License, or (at your option) any later version.
 *
 * "Apromore" is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program.
 * If not, see <http://www.gnu.org/licenses/lgpl-3.0.html>.
 */

/**
 * @author Daniel Reissner,
 * @version 1.0, 01.02.2017
 */

public class ImportEventLog {

  private final String conceptname = "concept:name";

  private final String lifecycle = "lifecycle:transition";

  private BiMap<Integer, String> labelMapping;

  private BiMap<String, Integer> inverseLabelMapping = HashBiMap.create();

  private BiMap<Integer, State> stateMapping;

  private BiMap<Integer, Transition> transitionMapping;

  private int initialState = 0;

  private IntHashSet finalStates;

  //private Map<IntArrayList, Boolean> tracesContained;
  private UnifiedMap<IntArrayList, IntArrayList> caseTracesMapping;

  //private IntObjectHashMap<String> traceIDtraceName;
  //private UnifiedMap<IntArrayList,UnifiedSet<DecodeTandemRepeats>> reductions;
  private UnifiedMap<IntArrayList, IntObjectHashMap<UnifiedSet<DecodeTandemRepeats>>> reductions;

  private double reductionLength = 0;

  private UnifiedSet<IntArrayList> visited;

  private Map<Integer, String> caseIDs;

  private XLog xlog;

  private Automaton dafsa;

  private Automaton reducedDafsa;

  public XLog importEventLog(String fileName) throws Exception {
    File xesFileIn = new File(fileName);
    return importEventLog(xesFileIn);
  }

  public XLog importEventLog(File file) throws Exception {
    XesXmlParser parser = new XesXmlParser(new XFactoryNaiveImpl());
    if (!parser.canParse(file)) {
      parser = new XesXmlGZIPParser();
      if (!parser.canParse(file)) {
        throw new IllegalArgumentException("Unparsable log file: " + file.getAbsolutePath());
      }
    }

    return parser.parse(file).remove(0);
  }

  public XLog createReducedTREventLog(String fileName) throws Exception {
    XLog xLog = importEventLog(fileName);

    caseTracesMapping = new UnifiedMap<>();
    Map<Integer, String> caseIDs = new UnifiedMap<>();
    IntArrayList traces;
    labelMapping = HashBiMap.create();
    inverseLabelMapping = HashBiMap.create();
    reductions = new UnifiedMap<>();
    String eventName;
    String traceID;
    int translation = 1;
    int iTransition = 0;
    IntArrayList tr;
    //UnifiedSet<DecodeTandemRepeats> redTr;
    IntObjectHashMap<UnifiedSet<DecodeTandemRepeats>> redTr;
    IntDAFSAInt fsa = new IntDAFSAInt();
    Integer key = null;
    UnifiedSet<IntArrayList> visited = new UnifiedSet<>();
    int it = 0;
    IntArrayList reductionStats = new IntArrayList();
    IntArrayList traceLengthStats = new IntArrayList();
    IntArrayList redTraceLengthStats = new IntArrayList();
    IntIntHashMap labelCount = new IntIntHashMap();
    UnifiedSet<IntArrayList> uniqueTraces = new UnifiedSet<>();
    UnifiedSet<IntArrayList> uniqueTRTraces = new UnifiedSet<IntArrayList>();
    XTrace trace;
    int i, j;
    DecodeTandemRepeats decoder;
    XFactory xFac = new XFactoryNaiveImpl();
    XLog log = xFac.createLog();
    //XExtensionManager xEvMan = XExtensionManager.instance();
    //xEvMan.
    XExtension xtend = XConceptExtension.instance();
    XAttributeLiteral xAttrLiteral = xFac.createAttributeLiteral(conceptname, "", xtend);
    XAttributeLiteral xLc = xFac.createAttributeLiteral(lifecycle, "", xtend);
    for (i = 0; i < xLog.size(); i++) {
      trace = xLog.get(i);
      traceID = ((XAttributeLiteral) trace.getAttributes().get(conceptname)).getValue();
      tr = new IntArrayList(trace.size());
      for (j = 0; j < trace.size(); j++) {
        eventName = ((XAttributeLiteral) trace.get(j).getAttributes().get(conceptname))
            .getValue();//xce.extractName(event);
        if ((key = (inverseLabelMapping.get(eventName))) == null) {
          //labelMapping.put(translation, eventName);
          inverseLabelMapping.put(eventName, translation);
          key = translation;
          translation++;
        }
        tr.add(key);
      }
      uniqueTraces.add(tr);
      decoder = new DecodeTandemRepeats(tr, 0, tr.size());
      //decoder.reduceTandemRepeats();
      XTrace newTr = xFac.createTrace();
      for (j = 0; j < decoder.reducedTrace().size(); j++) {
        XAttributeMap xAttr = xFac.createAttributeMap();
        xAttrLiteral.setValue(inverseLabelMapping.inverse().get(decoder.reducedTrace().get(j)));
        labelCount.addToValue(decoder.reducedTrace().get(j), 1);
        xLc.setValue("" + labelCount.get(decoder.reducedTrace().get(j)));
        xAttr.put(conceptname, xAttrLiteral);
        xAttr.put(lifecycle, xLc);
        XEvent event = xFac.createEvent(xAttr);
        newTr.add(event);
      }
      labelCount.clear();
      log.add(newTr);
      reductionStats.add(decoder.trace().size() - decoder.reducedTrace().size());
      traceLengthStats.add(decoder.trace().size());
      redTraceLengthStats.add(decoder.reducedTrace().size());
      if ((redTr = reductions.get(decoder.reducedTrace())) == null) {
        redTr = new IntObjectHashMap<>();
        reductions.put(decoder.reducedTrace(), redTr);
        fsa.addMinWord(decoder.reducedTrace());
        uniqueTRTraces.add(decoder.reducedTrace());
      }

      //redTr.add(decoder);
      //if(visited.add(decoder.reducedTrace))
      //	fsa.addMinWord(decoder.reducedTrace);
      //caseTracesMapping.put(tr, tracesLabelsMapping.get(trace));
      if ((traces = caseTracesMapping.get(tr)) == null) {
        traces = new IntArrayList();
        caseTracesMapping.put(tr, traces);
      }
      traces.add(it);
      caseIDs.put(it, traceID);
      it++;
    }
    labelMapping = inverseLabelMapping.inverse();
    System.out.println(
        "Stats - Avg. : " + reductionStats.average() + "; Max : " + reductionStats.max() + "; Med. : " + reductionStats
            .median());
    System.out.println(
        "Stats - Avg. : " + traceLengthStats.average() + "; Max : " + traceLengthStats.max() + "; Med. : "
            + traceLengthStats.median());
    System.out.println(
        "Stats - Avg. : " + redTraceLengthStats.average() + "; Max : " + redTraceLengthStats.max() + "; Med. : "
            + redTraceLengthStats.median());
    System.out.println("Log size : " + xLog.size());
    System.out.println("Unique traces : " + uniqueTraces.size());
    System.out.println("TR unique traces : " + uniqueTRTraces.size());
    return log;
  }

  public Automaton convertLogToAutomatonFrom(String fileName) throws Exception {
    //long start = System.nanoTime();
    File xesFileIn = new File(fileName);
    this.xlog = importEventLog(xesFileIn);
        /*
        while (xLogs.size() > 0) {
        	xLog.addAll(xLogs.remove(0));
        }
        */
    //long end = System.nanoTime();
    //System.out.println("Log import: " + TimeUnit.SECONDS.convert((end - start), TimeUnit.NANOSECONDS) + "s");
    return this.createDAFSAfromLog(xlog);
  }

  public Automaton convertLogToAutomatonWithTRFrom(String fileName) throws Exception {
    File xesFileIn = new File(fileName);
    XesXmlParser parser = new XesXmlParser(new XFactoryNaiveImpl());
    if (!parser.canParse(xesFileIn)) {
      parser = new XesXmlGZIPParser();
      if (!parser.canParse(xesFileIn)) {
        throw new IllegalArgumentException("Unparsable log file: " + xesFileIn.getAbsolutePath());
      }
    }
    List<XLog> xLogs = parser.parse(xesFileIn);
    this.xlog = xLogs.get(0);
    return this.createReducedDAFSAfromLog(xlog);
  }

  public Automaton createReducedDAFSAfromLog(@NonNull XLog xLog, BiMap<String, Integer> inverseLabelMapping) {
    this.inverseLabelMapping = HashBiMap.create(inverseLabelMapping);
    return createReducedDAFSAfromLog(xLog);
  }

  public Automaton createReducedDAFSAfromLog(@NonNull XLog xLog) {
    this.xlog = xLog;
    caseTracesMapping = new UnifiedMap<>();
    caseIDs = new UnifiedMap<>();
    IntArrayList traces;
    labelMapping = HashBiMap.create();
    if (inverseLabelMapping == null) {
      inverseLabelMapping = HashBiMap.create();
    }
    reductions = new UnifiedMap<>();
    String eventName;
    String traceID;
    int translation = inverseLabelMapping.size() + 1;
    int iTransition = 0;
    IntArrayList tr;
    //UnifiedSet<DecodeTandemRepeats> redTr;
    IntObjectHashMap<UnifiedSet<DecodeTandemRepeats>> redTr;
    UnifiedSet<DecodeTandemRepeats> setDecoders;
    UnifiedMap<IntIntHashMap, UnifiedSet<IntArrayList>> configReducedTraceMapping = new UnifiedMap<>();
    IntDAFSAInt fsa = new IntDAFSAInt();
    Integer key = null;
    visited = new UnifiedSet<>();
    int uniqueTraces = 0, uniqueTRTraces = 0;
    int it = 0;
    IntArrayList reductionStats = new IntArrayList();
    IntArrayList traceLengthStats = new IntArrayList();
    IntArrayList redTraceLengthStats = new IntArrayList();

    XTrace trace;
    int i, j;
    DecodeTandemRepeats decoder;

    for (i = 0; i < xLog.size(); i++) {
      trace = xLog.get(i);
      XAttributeLiteral xAt;
      if (((xAt = (XAttributeLiteral) trace.getAttributes().get(conceptname))) == null) {
        traceID = "" + it;
      } else {
        traceID = xAt.getValue();
      }

      tr = new IntArrayList(trace.size());
      for (j = 0; j < trace.size(); j++) {
        eventName = ((XAttributeLiteral) trace.get(j).getAttributes().get(conceptname))
            .getValue();//xce.extractName(event);
        if ((key = (inverseLabelMapping.get(eventName))) == null) {
          //labelMapping.put(translation, eventName);
          inverseLabelMapping.put(eventName, translation);
          key = translation;
          translation++;
        }
        tr.add(key);
      }
      if (visited.add(tr)) {
        uniqueTraces++;
        decoder = new DecodeTandemRepeats(tr, 0, tr.size());
        reductionStats.add(decoder.getReductionLength());
        traceLengthStats.add(decoder.trace().size());
        redTraceLengthStats.add(decoder.reducedTrace().size());
        if ((redTr = reductions.get(decoder.reducedTrace())) == null) {
          uniqueTRTraces++;
          redTr = new IntObjectHashMap<>();
          reductions.put(decoder.reducedTrace(), redTr);
          fsa.addMinWord(decoder.reducedTrace());
          UnifiedSet<IntArrayList> reducedTraces;
          if ((reducedTraces = configReducedTraceMapping.get(decoder.finalReducedConfiguration)) == null) {
            reducedTraces = new UnifiedSet<>();
            configReducedTraceMapping.put(decoder.finalReducedConfiguration, reducedTraces);
          }
          reducedTraces.add(decoder.reducedTrace());
        }
        if ((setDecoders = redTr.get(decoder.getReductionLength())) == null) {
          setDecoders = new UnifiedSet<>();
          redTr.put(decoder.getReductionLength(), setDecoders);
        }
        setDecoders.add(decoder);
      }
      if ((traces = caseTracesMapping.get(tr)) == null) {
        traces = new IntArrayList();
        caseTracesMapping.put(tr, traces);
      }
      traces.add(it);
      caseIDs.put(it, traceID);
      it++;
    }
    labelMapping = inverseLabelMapping.inverse();
    this.reductionLength = reductionStats.average();
    //System.out.println("Stats - Avg. : " + reductionStats.average() + "; Max : " + reductionStats.max() + "; Med. : " + reductionStats.median());
    //System.out.println("Stats - Avg. : " + traceLengthStats.average() + "; Max : " + traceLengthStats.max() + "; Med. : " + traceLengthStats.median());
    //System.out.println("Stats - Avg. : " + redTraceLengthStats.average() + "; Max : " + redTraceLengthStats.max() + "; Med. : " + redTraceLengthStats.median());
    //System.out.println("Unique Traces : " + uniqueTraces);
    //System.out.println("Unique TR Traces : " + uniqueTRTraces);
    this.prepareLogAutomaton(fsa);
    return new Automaton(stateMapping, labelMapping, inverseLabelMapping, transitionMapping, initialState, finalStates,
        caseTracesMapping, caseIDs, reductions, configReducedTraceMapping);
  }

  private void prepareLogAutomaton(IntDAFSAInt fsa) {
    int i;
    int iTransition = 0;
    int idest = 0;
    int ilabel = 0;
    stateMapping = HashBiMap.create();
    transitionMapping = HashBiMap.create();
    finalStates = new IntHashSet();
    for (AbstractIntDAFSA.State n : fsa.getStates()) {
      if (!(n.outbound() == 0 && (!fsa.isFinalState(n.getNumber())))) {
        if (!stateMapping.containsKey(n.getNumber())) {
          stateMapping.put(n.getNumber(),
              new State(n.getNumber(), fsa.isSource(n.getNumber()), fsa.isFinalState(n.getNumber())));
        }
        if (initialState != 0 && fsa.isSource(n.getNumber())) {
          initialState = n.getNumber();
        }
        if (fsa.isFinalState(n.getNumber())) {
          finalStates.add(n.getNumber());
        }
        for (i = 0; i < n.outbound(); i++) {
          idest = AbstractIntDAFSA.decodeDest(n.next.get(i));
          ilabel = AbstractIntDAFSA.decodeLabel(n.next.get(i));

          if (!stateMapping.containsKey(idest)) {
            stateMapping.put(idest,
                new State(idest, fsa.isSource(idest), fsa.isFinalState(AbstractIntDAFSA.decodeDest(n.next.get(i)))));
          }
          iTransition++;
          Transition t = new Transition(stateMapping.get(n.getNumber()), stateMapping.get(idest), ilabel);
          transitionMapping.put(iTransition, t);
          stateMapping.get(n.getNumber()).outgoingTransitions().add(t);
          stateMapping.get(idest).incomingTransitions().add(t);
        }
      }
    }
    stateMapping.get(initialState).setFinal(true);
    //Automaton logAutomaton = new Automaton(stateMapping, labelMapping, inverseLabelMapping, transitionMapping, initialState, finalStates, caseTracesMapping, caseIDs);//, concurrencyOracle);
    //long conversion = System.nanoTime();
    //System.out.println("Log Automaton creation: " + TimeUnit.MILLISECONDS.convert((automaton - start), TimeUnit.NANOSECONDS) + "ms");
    //System.out.println("Log Automaton conversion: " + TimeUnit.MILLISECONDS.convert((conversion - automaton), TimeUnit.NANOSECONDS) + "ms");
    //return logAutomaton;
  }

  public Automaton createOriginalDAFSAafterReduction() {
    if (visited == null) {
      return null;
    }
    IntDAFSAInt fsa = new IntDAFSAInt();
    for (IntArrayList trace : visited) {
      fsa.addMinWord(trace);
    }
    this.prepareLogAutomaton(fsa);
    return new Automaton(stateMapping, labelMapping, inverseLabelMapping, transitionMapping, initialState, finalStates,
        caseTracesMapping, caseIDs);
  }

  public Automaton createDAFSAfromLogFile(String fileName) throws Exception {
    XLog xLog = this.importEventLog(fileName);
    return this.createDAFSAfromLog(xLog);
  }

  public Automaton createDAFSAfromLog(XLog xLog, BiMap<String, Integer> inverseLabelMapping) throws IOException {
    this.inverseLabelMapping = HashBiMap.create(inverseLabelMapping);
    return createDAFSAfromLog(xLog);
  }

  public Automaton createDAFSAfromLog(XLog xLog) {
    //long start = System.nanoTime();
    //tracesContained = new UnifiedMap<IntArrayList, Boolean>();
    caseTracesMapping = new UnifiedMap<>();
    Map<Integer, String> caseIDs = new UnifiedMap<Integer, String>();
    IntArrayList traces;
    //traceIDtraceName = new IntObjectHashMap<String>();
    labelMapping = HashBiMap.create();
    if (inverseLabelMapping == null) {
      inverseLabelMapping = HashBiMap.create();
    }
    String eventName;
    String traceID;
    int translation = inverseLabelMapping.size();
    int iTransition = 0;
    IntArrayList tr;
    IntDAFSAInt fsa = new IntDAFSAInt();
    Integer key = null;
    UnifiedSet<IntArrayList> visited = new UnifiedSet<IntArrayList>();
    int it = 0;

    XTrace trace;
    int i, j;
    for (i = 0; i < xLog.size(); i++) {
      trace = xLog.get(i);
      XAttributeLiteral xAt;
      if (((xAt = (XAttributeLiteral) trace.getAttributes().get(conceptname))) == null) {
        traceID = "" + it;
      } else {
        traceID = xAt.getValue();
      }
      tr = new IntArrayList(trace.size());
      for (j = 0; j < trace.size(); j++) {
        eventName = ((XAttributeLiteral) trace.get(j).getAttributes().get(conceptname))
            .getValue();//xce.extractName(event);
        if ((key = (inverseLabelMapping.get(eventName))) == null) {
          //labelMapping.put(translation, eventName);
          inverseLabelMapping.put(eventName, translation);
          key = translation;
          translation++;
        }
        tr.add(key);
      }

      if (visited.add(tr)) {
        fsa.addMinWord(tr);
      }
      //caseTracesMapping.put(tr, tracesLabelsMapping.get(trace));
      if ((traces = caseTracesMapping.get(tr)) == null) {
        traces = new IntArrayList();
        caseTracesMapping.put(tr, traces);
      }
      traces.add(it);
      caseIDs.put(it, traceID);
      it++;
      //listTraces.add(traceLabels);

      //			if((traces = tracesLabelsMapping.get(traceLabels))==null)
      //			{
      //				traces = new IntArrayList();
      //				tracesLabelsMapping.put(traceLabels, traces);
      //			}
      //			traces.add(it);
    }
    labelMapping = inverseLabelMapping.inverse();
    this.prepareLogAutomaton(fsa);
    return new Automaton(stateMapping, labelMapping, inverseLabelMapping, transitionMapping, initialState, finalStates,
        caseTracesMapping, caseIDs);
  }

	/*public Automaton createDAFSAfromLog(XLog xLog, BiMap<String,Integer> inverseLabelMapping) throws IOException
	{
		//long start = System.nanoTime();
		//tracesContained = new UnifiedMap<IntArrayList, Boolean>();
		caseTracesMapping = new UnifiedMap<>();
		Map<Integer, String> caseIDs = new UnifiedMap<Integer, String>();
		IntArrayList traces;
		//traceIDtraceName = new IntObjectHashMap<String>();
		//labelMapping = HashBiMap.create();
		this.inverseLabelMapping = HashBiMap.create(inverseLabelMapping);
		String eventName;
		String traceID;
		int translation = this.inverseLabelMapping.size();
		int iTransition = 0;
		IntArrayList tr;
		IntDAFSAInt fsa = new IntDAFSAInt();
		Integer key = null;
		UnifiedSet<IntArrayList> visited = new UnifiedSet<IntArrayList>();
		int it = 0;

		XTrace trace;
		int i, j;
		for (i = 0; i < xLog.size(); i++)
		{
			trace = xLog.get(i);
			XAttributeLiteral xAt;
			if(((xAt = (XAttributeLiteral) trace.getAttributes().get(conceptname))) == null)
			{
				traceID = "" + it;
			}
			else
			{
				traceID = xAt.getValue();
			}
			tr = new IntArrayList(trace.size());
			for (j = 0; j < trace.size(); j++)
			{
				eventName = ((XAttributeLiteral) trace.get(j).getAttributes().get(conceptname)).getValue();//xce.extractName(event);
				if((key = (inverseLabelMapping.get(eventName))) == null)
				{
					//labelMapping.put(translation, eventName);
					inverseLabelMapping.put(eventName, translation);
					key = translation;
					translation++;
				}
				tr.add(key);
			}

			if(visited.add(tr))
				fsa.addMinWord(tr);
			//caseTracesMapping.put(tr, tracesLabelsMapping.get(trace));
			if((traces = caseTracesMapping.get(tr))==null)
			{
				traces = new IntArrayList();
				caseTracesMapping.put(tr, traces);
			}
			traces.add(it);
			caseIDs.put(it, traceID);
			it++;
			//listTraces.add(traceLabels);

//			if((traces = tracesLabelsMapping.get(traceLabels))==null)
//			{
//				traces = new IntArrayList();
//				tracesLabelsMapping.put(traceLabels, traces);
//			}
//			traces.add(it);
		}
		labelMapping = inverseLabelMapping.inverse();
		this.prepareLogAutomaton(fsa);
		return new Automaton(stateMapping, labelMapping, inverseLabelMapping, transitionMapping, initialState, finalStates, caseTracesMapping, caseIDs);
	}*/

  public List<Automaton> convertLogToAutomatonFrom(String fileName, List<Map<Integer, String>> projectionLabels)
      throws Exception {
    //long start = System.nanoTime();
    File xesFileIn = new File(fileName);
    XesXmlParser parser = new XesXmlParser(new XFactoryNaiveImpl());
    if (!parser.canParse(xesFileIn)) {
      parser = new XesXmlGZIPParser();
      if (!parser.canParse(xesFileIn)) {
        throw new IllegalArgumentException("Unparsable log file: " + xesFileIn.getAbsolutePath());
      }
    }
    List<XLog> xLogs = parser.parse(xesFileIn);
    XLog xLog = xLogs.remove(0);
        /*
        while (xLogs.size() > 0) {
        	xLog.addAll(xLogs.remove(0));
        }
        */
    //long end = System.nanoTime();
    //System.out.println("Log import: " + TimeUnit.SECONDS.convert((end - start), TimeUnit.NANOSECONDS) + "s");
    List<XLog> projectedLogs = projectModelLabelsOn(xLog, projectionLabels);
    List<Automaton> projectedDafsas = new FastList<Automaton>();
    for (XLog pLog : projectedLogs) {
      projectedDafsas.add(this.createDAFSAfromLog(pLog));
    }
    return projectedDafsas;
  }

  public XLog filterLogSimple(XLog xLog, double percentile) {
    int i, j, translation = 0;
    Integer key;
    XTrace trace;
    String traceID, eventName;
    IntArrayList tr;
    UnifiedSet<IntArrayList> visited = new UnifiedSet<IntArrayList>();
    ObjectIntHashMap<IntArrayList> traceCounts = new ObjectIntHashMap<>();
    UnifiedMap<IntArrayList, FastList<XTrace>> traceMapping = new UnifiedMap<>();
    FastList<XTrace> traces;
    for (i = 0; i < xLog.size(); i++) {
      trace = xLog.get(i);
      traceID = ((XAttributeLiteral) trace.getAttributes().get(conceptname)).getValue();
      tr = new IntArrayList(trace.size());
      for (j = 0; j < trace.size(); j++) {
        eventName = ((XAttributeLiteral) trace.get(j).getAttributes().get(conceptname))
            .getValue();//xce.extractName(event);
        if ((key = (inverseLabelMapping.get(eventName))) == null) {
          //labelMapping.put(translation, eventName);
          inverseLabelMapping.put(eventName, translation);
          key = translation;
          translation++;
        }
        tr.add(key);
      }

      if ((traces = traceMapping.get(tr)) == null) {
        traces = new FastList<>();
        traceMapping.put(tr, traces);
      }
      traceCounts.addToValue(tr, 1);
      traces.add(trace);
    }
    int[] nTraces = traceCounts.values().toArray();
    Arrays.sort(nTraces);
    int pos = (int) Math.round(nTraces.length * percentile);
    int threshold = nTraces[pos];
    XFactory xFac = new XFactoryNaiveImpl();
    XLog filteredLog = xFac.createLog(xLog.getAttributes());
    int uTraces = 0;
    XExtension xtend = XConceptExtension.instance();
    XAttributeLiteral xAttrLiteral = null;
    //System.out.println("Min: " +nTraces[0] );
    //System.out.println("Threshold: " + threshold);
    for (IntArrayList uTrace : traceCounts.keySet()) {
      if (traceCounts.get(uTrace) > threshold) {
        uTraces++;
        for (XTrace trace1 : traceMapping.get(uTrace)) {
          XTrace xTr = xFac.createTrace(trace1.getAttributes());
          for (Object ev : trace1.toArray()) {
            XEvent event = (XEvent) ev;
            //xAttrLiteral = xFac.createAttributeLiteral("concept:name", ((XAttributeLiteral) event.getAttributes().get(conceptname)).getValue(), xtend);
            XAttributeMap xAttr = xFac.createAttributeMap();
            xAttr.putAll(event.getAttributes());
            //xAttr.put("concept:name", xAttrLiteral);
            XEvent xEv = xFac.createEvent(xAttr);
            xTr.add(xEv);
            //System.out.print(decompositions.globalInverseLabels.inverse().get(ev) + ", ");
          }
          filteredLog.add(xTr);
        }
      }
    }
    System.out.println(traceCounts.size());
    System.out.println(uTraces);
    return filteredLog;
  }

  public List<XLog> projectModelLabelsOn(XLog xLog, List<Map<Integer, String>> projectionLabels) {
    List<XLog> projectedLogs = new FastList<XLog>(projectionLabels.size());
    Map<Integer, String> caseIDs = new UnifiedMap<Integer, String>();
    IntArrayList traces;
    String eventName;
    String traceID;
    int translation = 0;
    int iTransition = 0;
    IntArrayList tr;
    IntDAFSAInt fsa = new IntDAFSAInt();
    Integer key = null;
    UnifiedSet<IntArrayList> visited = new UnifiedSet<IntArrayList>();
    int it = 0;
    XTrace trace;
    int i, j;
    for (i = 0; i < xLog.size(); i++) {
      trace = xLog.get(i);
      XAttributeLiteral xAt;
      if (((xAt = (XAttributeLiteral) trace.getAttributes().get(conceptname))) == null) {
        traceID = "" + it;
      } else {
        traceID = xAt.getValue();
      }
      tr = new IntArrayList(trace.size());
      for (j = 0; j < trace.size(); j++) {
        eventName = ((XAttributeLiteral) trace.get(j).getAttributes().get(conceptname))
            .getValue();//xce.extractName(event);
        if ((key = (inverseLabelMapping.get(eventName))) == null) {
          //labelMapping.put(translation, eventName);
          inverseLabelMapping.put(eventName, translation);
          key = translation;
          translation++;
        }
        tr.add(key);
      }

      if (visited.add(tr)) {
        fsa.addMinWord(tr);
      }
      //caseTracesMapping.put(tr, tracesLabelsMapping.get(trace));
      if ((traces = caseTracesMapping.get(tr)) == null) {
        traces = new IntArrayList();
        caseTracesMapping.put(tr, traces);
      }
      traces.add(it);
      caseIDs.put(it, traceID);
      it++;
      //listTraces.add(traceLabels);

      //			if((traces = tracesLabelsMapping.get(traceLabels))==null)
      //			{
      //				traces = new IntArrayList();
      //				tracesLabelsMapping.put(traceLabels, traces);
      //			}
      //			traces.add(it);
    }
    labelMapping = inverseLabelMapping.inverse();
    return projectedLogs;
  }

  public double getReductionLength() {
    return reductionLength;
  }

}