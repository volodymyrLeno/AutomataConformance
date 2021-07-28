package org.apromore.alignmentautomaton.importer;

import java.io.*;
import java.util.*;
import cern.colt.list.DoubleArrayList;
import cern.colt.matrix.DoubleMatrix2D;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import name.kazennikov.dafsa.AbstractIntDAFSA;
import name.kazennikov.dafsa.IntDAFSAInt;
import org.apromore.alignmentautomaton.automaton.Automaton;
import org.apromore.alignmentautomaton.automaton.State;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.apromore.processmining.plugins.bpmn.plugins.BpmnImportPlugin;
import org.deckfour.xes.model.XAttributeLiteral;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.XTrace;
import org.eclipse.collections.impl.list.mutable.FastList;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.UnifiedMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntIntHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;
import org.eclipse.collections.impl.set.mutable.UnifiedSet;
import org.eclipse.collections.impl.set.mutable.primitive.IntHashSet;
import org.processmining.framework.connections.ConnectionCannotBeObtained;
import org.processmining.framework.plugin.PluginContext;
import org.processmining.framework.util.collection.MultiSet;
import org.processmining.models.graphbased.AttributeMap;
import org.processmining.models.graphbased.directed.petrinet.Petrinet;
import org.processmining.models.graphbased.directed.petrinet.PetrinetEdge;
import org.processmining.models.graphbased.directed.petrinet.PetrinetGraph;
import org.processmining.models.graphbased.directed.petrinet.PetrinetNode;
import org.processmining.models.graphbased.directed.petrinet.analysis.PlaceInvariantSet;
import org.processmining.models.graphbased.directed.petrinet.analysis.SComponentSet;
import org.processmining.models.graphbased.directed.petrinet.elements.Place;
import org.processmining.models.graphbased.directed.petrinet.elements.Transition;
import org.processmining.models.graphbased.directed.petrinet.impl.PetrinetImpl;
import org.processmining.models.semantics.petrinet.Marking;
import org.processmining.plugins.bpmn.Bpmn;
import org.processmining.plugins.petrinet.structuralanalysis.IncidenceMatrixFactory;
import org.processmining.plugins.petrinet.structuralanalysis.invariants.PlaceInvariantCalculator;
import org.processmining.plugins.petrinet.structuralanalysis.util.SelfLoopTransitionExtract;
import org.processmining.models.graphbased.directed.transitionsystem.ReachabilityGraph;

public class DecomposingTRImporter extends ImportProcessModel {

  public Automaton modelFSM;

  public Automaton dafsa;

  private ImportEventLog importer;

  private final String conceptname = "concept:name";

  //private Map<IntArrayList, Boolean> tracesContained;
  public UnifiedMap<IntArrayList, IntArrayList> caseTracesMapping;

  //private IntObjectHashMap<String> traceIDtraceName;
  private final BiMap<Integer, IntArrayList> labelComponentsMapping = HashBiMap.create();

  public List<Automaton> sComponentFSMs = new FastList<Automaton>();

  public FastList<Petrinet> sComponentNets = new FastList<Petrinet>();

  public FastList<ImportProcessModel> sComponentImporters = new FastList<>();

  public Map<Integer, String> caseIDs = new UnifiedMap<Integer, String>();

  public UnifiedMap<Integer, Automaton> componentDAFSAs = new UnifiedMap<Integer, Automaton>();

  public IntObjectHashMap<UnifiedMap<IntArrayList, IntObjectHashMap<UnifiedSet<DecodeTandemRepeats>>>> componentReductions = new IntObjectHashMap<>();

  public IntObjectHashMap<UnifiedMap<IntIntHashMap, UnifiedSet<IntArrayList>>> componentConfigurationReducedTracesMapping = new IntObjectHashMap<>();

  private final UnifiedSet<IntArrayList> visited = new UnifiedSet<IntArrayList>();

  public XLog xLog;

  public UnifiedMap<IntArrayList, UnifiedMap<Integer, IntArrayList>> traceProjections = new UnifiedMap<IntArrayList, UnifiedMap<Integer, IntArrayList>>();

  public int minModelMoves;

  //private UnifiedMap<Integer, UnifiedMap<Integer, IntArrayList>> projectedLogs = new UnifiedMap<Integer, UnifiedMap<Integer, IntArrayList>>(); //TODO: ???
  private final UnifiedMap<Integer, UnifiedMap<IntArrayList, IntArrayList>> projectedLogs = new UnifiedMap<Integer, UnifiedMap<IntArrayList, IntArrayList>>();

  public String path;

  private String model;

  public boolean doDecomposition = false;

  public boolean applySCompRule = false;

  public double avgReduction = 0;

  private final double TRThreshold = 2.0;

  public int sumRGsize = 0;

  public boolean applyTRRule = false;

  public Petrinet pnet = null;

  public IntArrayList scompPlaces = new IntArrayList();

  public IntArrayList scompTransitions = new IntArrayList();

  public IntArrayList scompArcs = new IntArrayList();

  public IntArrayList scompSize = new IntArrayList();

  public IntArrayList scompChoices = new IntArrayList();

  public IntArrayList scompParallels = new IntArrayList();

  public IntArrayList scompRGNodes = new IntArrayList();

  public IntArrayList scompRGArcs = new IntArrayList();

  public IntArrayList scompRGSize = new IntArrayList();

  private final IntObjectHashMap<UnifiedSet<IntArrayList>> componentsUniqueTraces = new IntObjectHashMap<>();

  public DecomposingTRImporter() {
  }

  public DecomposingTRImporter(String path, String model, String log) throws Exception {
    importAndDecomposeModelAndLogForConformanceChecking(path, model, log);
  }

  public void importAndDecomposeModelAndLogForConformanceChecking(String path, String model, String log)
      throws Exception {
    Object[] pnetAndMarking;
    this.path = path;
    this.model = model;

    xLog = new ImportEventLog().importEventLog(path + log);
    String fileName = path + model;

    if(model.endsWith(".bpmn")){
      BPMNDiagram diagram = new BpmnImportPlugin().importFromStreamToDiagram(new FileInputStream(new File(fileName)), fileName);
      this.importAndDecomposeModelAndLogForConformanceChecking(diagram, xLog);
    }
    else{
      pnetAndMarking = importPetriNetAndMarking(fileName);
      pnet = (Petrinet) pnetAndMarking[0];
      this.importAndDecomposeModelAndLogForConformanceChecking((Petrinet) pnetAndMarking[0], (Marking) pnetAndMarking[1], xLog);
    }
  }

  public void importModelForStatistics(String path, String model) throws Exception {
    Object[] pnetAndMarking;
    this.path = path;
    this.model = model;
    String fileName = path + model;
    if(model.endsWith(".bpmn")){
      BPMNDiagram diagram = new BpmnImportPlugin().importFromStreamToDiagram(new FileInputStream(new File(fileName)), fileName);
      this.modelFSM = createFSMfromBPMN(diagram, null, null);
    }
    else{
      pnetAndMarking = importPetriNetAndMarking(fileName);
      pnet = (Petrinet) pnetAndMarking[0];
      this.modelFSM = createFSMfromPetrinet(pnet, (Marking) pnetAndMarking[1], null, null);
    }
  }

  public void importAndDecomposeModelAndLogForConformanceChecking(BPMNDiagram diagram, XLog xlog) throws Exception{
    this.xLog = xLog;
    this.modelFSM = createFSMfromBPMN(diagram, null, null);
    parallel = new BPMNPreprocessor().getNonTrivialAndSplits(diagram).size();
    doDecomposition = parallel > 0;
    if(doDecomposition){
      decomposeBpmnDiagramIntoSComponentAutomata(diagram);
      decomposeLogIntoProjectedDafsa(xLog);
      decideSCompRule();
    }
    else{
      importer = new ImportEventLog();
      dafsa = importer.createReducedDAFSAfromLog(xLog, globalInverseLabels);
      avgReduction = importer.getReductionLength();
    }
    decideTRrule();
  }

  public void decomposeBpmnDiagramIntoSComponentAutomata(BPMNDiagram diagram){
    BPMNtoTSConverter bpmNtoTSConverter = new BPMNtoTSConverter();
    List<ReachabilityGraph> reachabilityGraphs = bpmNtoTSConverter.BPMNtoTSwithScomp(diagram);
    for(var rg: reachabilityGraphs){
      ImportProcessModel importer = new ImportProcessModel();
      Automaton fsm = importer.convertReachabilityGraphToFSM(rg, globalInverseLabels.inverse(), globalInverseLabels);
      this.sComponentImporters.add(importer);
      sComponentFSMs.add(fsm);

      IntArrayList components;
      for(Integer event : fsm.eventLabels().keySet())
      {
        if((components = labelComponentsMapping.get(event))==null)
        {
          components = new IntArrayList();
          labelComponentsMapping.put(event, components);
        }
        components.add(sComponentFSMs.size()-1);
      }
    }
  }

  public void importAndDecomposeModelAndLogForConformanceChecking(Petrinet pnet, Marking initM, XLog xLog)
      throws ConnectionCannotBeObtained {
    this.xLog = xLog;
    this.pnet = pnet;
    this.modelFSM = createFSMfromPetrinet(pnet, initM, null, null);

    if (parallel > 0) {
      doDecomposition = true;
    }
    if (doDecomposition) {
      decomposePetriNetIntoSComponentAutomata(pnet, initM);
			/*int i = 1;
			for (Automaton fsm : this.sComponentFSMs) {
				fsm.toDot(path + model.substring(0, model.length() - 5) + i + ".dot");
				SCompNetToDot(i-1, path + model.substring(0,model.length()-5) + "-" + i + ".dot");
				i++;
			}*/
      decomposeLogIntoProjectedDafsa(xLog);
      decideSCompRule();
    } else {
      //dafsa = new ImportEventLog().createDAFSAfromLog(xLog, modelFSM.inverseEventLabels());
      importer = new ImportEventLog();
      dafsa = importer.createReducedDAFSAfromLog(xLog, globalInverseLabels);
      avgReduction = importer.getReductionLength();
    }
    decideTRrule();

  }

  public void importAndDecomposeModelAndLogForConformanceChecking(Bpmn bpmn, XLog xLog)
      throws ConnectionCannotBeObtained {
    this.xLog = xLog;

//    if (parallel > 0) {
//      doDecomposition = true;
//    }
    if (doDecomposition && false) { // branch disabled
      // FIXME decompositions/parallelization not supported when converting directly from Bpmn to
      // automaton without Petri net
      //      decomposePetriNetIntoSComponentAutomata(pnet, initM);
      //      decomposeLogIntoProjectedDafsa(xLog);
      //      decideSCompRule();
    } else {
      // sequential
    }

    importer = new ImportEventLog();
    dafsa = importer.createDAFSAfromLog(xLog);
    avgReduction = importer.getReductionLength();
    // FIXME change Bpmn to BPMNDiagram and uncomment the line below
//    modelFSM = createFSMFromBPNM(bpmn, dafsa.eventLabels(), dafsa.inverseEventLabels());
    decideTRrule();
  }

  private void decideTRrule() {
    if (avgReduction >= TRThreshold) {
      applyTRRule = true;
    }
  }

  private void decideSCompRule() {
    sumRGsize = 0;
    for (int comp = 0; comp < sComponentFSMs.size(); comp++) {
      sumRGsize += sComponentImporters.get(comp).rg_size_before_tau_removal;
    }
    if (sumRGsize <= modelFSM.totalSize) {
      applySCompRule = true;
    }
  }

  public void prepareTR() {
    if (doDecomposition) {
      //ImportEventLog importer = new ImportEventLog();
      //dafsa = importer.createReducedDAFSAfromLog(xLog, globalInverseLabels);
      createReducedDAFSA();
    }
  }

  public void prepareAutomata() {
    createOriginalDAFSAafterReduction();
  }

  public DecomposingConformanceImporter prepareSComp() {
    UnifiedMap<Integer, Automaton> componentDAFSAs = new UnifiedMap<Integer, Automaton>();
    //IntObjectHashMap<IntDAFSAInt> componentFSAs = new IntObjectHashMap();
    IntDAFSAInt fsa;
    for (int component = 0; component < sComponentFSMs.size(); component++) {
      fsa = new IntDAFSAInt();
      //componentFSAs.put(component, fsa);
      for (IntArrayList trace : componentsUniqueTraces.get(component)) {
        fsa.addMinWord(trace);
      }

      componentDAFSAs.put(component, preprocessDAFSAforSComp(fsa, component));
    }
    DecomposingConformanceImporter SCompImporter = new DecomposingConformanceImporter(modelFSM, caseTracesMapping,
        labelComponentsMapping, sComponentFSMs, sComponentNets, sComponentImporters, caseIDs, componentDAFSAs, visited,
        componentsUniqueTraces, xLog, traceProjections, projectedLogs, path, model, doDecomposition,
        globalInverseLabels, globalLabelMapping);
    return SCompImporter;
  }

  private void decomposeLogIntoProjectedDafsa(XLog xLog) {
    caseTracesMapping = new UnifiedMap<>();
    IntArrayList traces;
    //traceIDtraceName = new IntObjectHashMap<String>();
    String eventName;
    String traceID;
    int translation = globalInverseLabels.size();
    IntArrayList tr;
    IntDAFSAInt fsa;
    Integer key = null;
    int it = 0;
    UnifiedMap<Integer, IntDAFSAInt> componentFSAs = new UnifiedMap<Integer, IntDAFSAInt>();
    IntArrayList components;
    UnifiedMap<Integer, IntArrayList> projectedTraces;
    IntArrayList projectedTrace;
    XTrace trace;
    int i, j;
    DecodeTandemRepeats decoder;
    UnifiedMap<IntArrayList, IntObjectHashMap<UnifiedSet<DecodeTandemRepeats>>> reductions;
    IntObjectHashMap<UnifiedSet<DecodeTandemRepeats>> equivDecoders;
    UnifiedSet<DecodeTandemRepeats> setDecoders;
    UnifiedMap<IntIntHashMap, UnifiedSet<IntArrayList>> configReducedTracesMapping;
    UnifiedSet<IntArrayList> reducedTraces;
    IntArrayList traceReductions = new IntArrayList();
    UnifiedSet<IntArrayList> compUniqueTraces;

    for (i = 0; i < xLog.size(); i++) {
      projectedTraces = new UnifiedMap<Integer, IntArrayList>();
      for (int component = 0; component < sComponentFSMs.size(); component++) {
        projectedTraces.put(component, new IntArrayList());
      }
      trace = xLog.get(i);
      traceID = ((XAttributeLiteral) trace.getAttributes().get(conceptname)).getValue();
      tr = new IntArrayList(trace.size());
      for (j = 0; j < trace.size(); j++) {
        //it++;
        eventName = ((XAttributeLiteral) trace.get(j).getAttributes().get(conceptname))
            .getValue();//xce.extractName(event);
        if ((key = (globalInverseLabels.get(eventName))) == null) {
          //labelMapping.put(translation, eventName);
          globalInverseLabels.put(eventName, translation);
          key = translation;
          translation++;
        } else if ((components = labelComponentsMapping.get(key)) != null) {
          for (int component : components.toArray()) {
            projectedTraces.get(component).add(key);
          }
        }
        tr.add(key);
      }

      if (visited.add(tr)) {
        traceProjections.put(tr, projectedTraces);
        for (Integer component : projectedTraces.keySet()) {
          projectedTrace = projectedTraces.get(component);

          if ((compUniqueTraces = this.componentsUniqueTraces.get(component)) == null) {
            compUniqueTraces = new UnifiedSet<>();
            this.componentsUniqueTraces.put(component, compUniqueTraces);
          }
          if (compUniqueTraces.add(projectedTraces.get(component))) {
            decoder = new DecodeTandemRepeats(projectedTrace, 0, projectedTrace.size());
            traceReductions.add(decoder.getReductionLength());
            if ((reductions = componentReductions.get(component)) == null) {
              reductions = new UnifiedMap<>();
              componentReductions.put(component, reductions);
            }
            if ((equivDecoders = reductions.get(decoder.reducedTrace())) == null) {
              equivDecoders = new IntObjectHashMap<>();
              reductions.put(decoder.reducedTrace(), equivDecoders);
              if ((fsa = componentFSAs.get(component)) == null) {
                fsa = new IntDAFSAInt();
                componentFSAs.put(component, fsa);
              }
              fsa.addMinWord(decoder.reducedTrace());
              if ((configReducedTracesMapping = componentConfigurationReducedTracesMapping.get(component)) == null) {
                configReducedTracesMapping = new UnifiedMap<>();
                componentConfigurationReducedTracesMapping.put(component, configReducedTracesMapping);
              }
              if ((reducedTraces = configReducedTracesMapping.get(decoder.finalReducedConfiguration)) == null) {
                reducedTraces = new UnifiedSet<>();
                configReducedTracesMapping.put(decoder.finalReducedConfiguration, reducedTraces);
              }
              reducedTraces.add(decoder.reducedTrace());
            }
            if ((setDecoders = equivDecoders.get(decoder.getReductionLength())) == null) {
              setDecoders = new UnifiedSet<>();
              equivDecoders.put(decoder.getReductionLength(), setDecoders);
            }
            setDecoders.add(decoder);
          }
        }
      }

      if ((traces = caseTracesMapping.get(tr)) == null) {
        traces = new IntArrayList();
        caseTracesMapping.put(tr, traces);
      }
      traces.add(it);
      caseIDs.put(it, traceID);
      it++;
    }
    for (IntArrayList uniqueTrace : caseTracesMapping.keySet()) {
      for (Integer component : traceProjections.get(uniqueTrace).keySet()) {
        UnifiedMap<IntArrayList, IntArrayList> projectedLog;
        if ((projectedLog = projectedLogs.get(component)) == null) {
          projectedLog = new UnifiedMap<>();
          projectedLogs.put(component, projectedLog);
        }
        projectedLog.put(traceProjections.get(uniqueTrace).get(component), caseTracesMapping.get(uniqueTrace));
      }
    }
    globalLabelMapping = globalInverseLabels.inverse();
    for (Integer component : componentFSAs.keySet()) {
      componentDAFSAs.put(component, preprocessDAFSA(componentFSAs.get(component), component));
    }
    this.avgReduction = traceReductions.average();
    //System.out.println(xLog.size());
    //System.out.println(visited.size());
    //System.out.println(globalInverseLabels);
    //System.out.println(it);
  }

  public void createOriginalDAFSAafterReduction() {
    if (doDecomposition) {
      IntDAFSAInt fsa = new IntDAFSAInt();
      for (IntArrayList trace : visited) {
        fsa.addMinWord(trace);
      }
      this.recoverOriginalDAFSA(fsa);
    } else {
      dafsa = importer.createOriginalDAFSAafterReduction();
    }
  }

  private void recoverOriginalDAFSA(IntDAFSAInt fsa) {
    int i;
    int iTransition = 0;
    int idest = 0;
    int ilabel = 0;
    int initialState = 0;
    BiMap<Integer, State> stateMapping = HashBiMap.create();
    BiMap<Integer, org.apromore.alignmentautomaton.automaton.Transition> transitionMapping = HashBiMap.create();
    IntHashSet finalStates = new IntHashSet();
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
          org.apromore.alignmentautomaton.automaton.Transition t = new org.apromore.alignmentautomaton.automaton.Transition(
              stateMapping.get(n.getNumber()), stateMapping.get(idest), ilabel);
          transitionMapping.put(iTransition, t);
          stateMapping.get(n.getNumber()).outgoingTransitions().add(t);
          stateMapping.get(idest).incomingTransitions().add(t);
        }
      }
    }
    stateMapping.get(initialState).setFinal(true);
    //Automaton logAutomaton = new Automaton(stateMapping, globalLabelMapping, globalInverseLabels, transitionMapping, initialState, finalStates, projectedLogs.get(component), caseIDs);//, concurrencyOracle);
    //Automaton logAutomaton = new Automaton(stateMapping, globalLabelMapping, globalInverseLabels, transitionMapping, initialState, finalStates, projectedLogs.get(component), caseIDs,
    //        componentReductions.get(component), componentConfigurationReducedTracesMapping.get(component));
    this.dafsa = new Automaton(stateMapping, globalLabelMapping, globalInverseLabels, transitionMapping, initialState,
        finalStates, caseTracesMapping, caseIDs);
  }

  private void createReducedDAFSA() {
    if (visited.isEmpty()) {
      return;
    }
    IntDAFSAInt fsa = new IntDAFSAInt();
    UnifiedSet<IntArrayList> visitedRed = new UnifiedSet<>();
    UnifiedMap<IntArrayList, IntObjectHashMap<UnifiedSet<DecodeTandemRepeats>>> reductions = new UnifiedMap<>();
    IntObjectHashMap<UnifiedSet<DecodeTandemRepeats>> lengthDecoderMapping;
    UnifiedSet<DecodeTandemRepeats> equivDecoders;
    UnifiedMap<IntIntHashMap, UnifiedSet<IntArrayList>> configReducedTracesMapping = new UnifiedMap<>();
    UnifiedSet<IntArrayList> reducedTraces = new UnifiedSet<>();
    for (IntArrayList trace : visited) {
      DecodeTandemRepeats decoder = new DecodeTandemRepeats(trace, 0, trace.size());
      if (visitedRed.add(decoder.reducedTrace())) {
        fsa.addMinWord(decoder.reducedTrace());
        if ((reducedTraces = configReducedTracesMapping.get(decoder.finalReducedConfiguration)) == null) {
          reducedTraces = new UnifiedSet<>();
          configReducedTracesMapping.put(decoder.finalReducedConfiguration, reducedTraces);
        }
        reducedTraces.add(decoder.reducedTrace());
      }
      if ((lengthDecoderMapping = reductions.get(decoder.reducedTrace())) == null) {
        lengthDecoderMapping = new IntObjectHashMap<>();
        reductions.put(decoder.reducedTrace(), lengthDecoderMapping);
      }
      if ((equivDecoders = lengthDecoderMapping.get(decoder.getReductionLength())) == null) {
        equivDecoders = new UnifiedSet<>();
        lengthDecoderMapping.put(decoder.getReductionLength(), equivDecoders);
      }
      equivDecoders.add(decoder);
    }

    int i;
    int iTransition = 0;
    int idest = 0;
    int ilabel = 0;
    int initialState = 0;
    BiMap<Integer, State> stateMapping = HashBiMap.create();
    BiMap<Integer, org.apromore.alignmentautomaton.automaton.Transition> transitionMapping = HashBiMap.create();
    IntHashSet finalStates = new IntHashSet();
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
          org.apromore.alignmentautomaton.automaton.Transition t = new org.apromore.alignmentautomaton.automaton.Transition(
              stateMapping.get(n.getNumber()), stateMapping.get(idest), ilabel);
          transitionMapping.put(iTransition, t);
          stateMapping.get(n.getNumber()).outgoingTransitions().add(t);
          stateMapping.get(idest).incomingTransitions().add(t);
        }
      }
    }
    stateMapping.get(initialState).setFinal(true);

    this.dafsa = new Automaton(stateMapping, globalLabelMapping, globalInverseLabels, transitionMapping, initialState,
        finalStates, caseTracesMapping, caseIDs, reductions, configReducedTracesMapping);
  }

  private Automaton preprocessDAFSAforSComp(IntDAFSAInt fsa, Integer component) {
    int i;
    int iTransition = 0;
    int idest = 0;
    int ilabel = 0;
    int initialState = 0;
    BiMap<Integer, State> stateMapping = HashBiMap.create();
    BiMap<Integer, org.apromore.alignmentautomaton.automaton.Transition> transitionMapping = HashBiMap.create();
    IntHashSet finalStates = new IntHashSet();
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
          org.apromore.alignmentautomaton.automaton.Transition t = new org.apromore.alignmentautomaton.automaton.Transition(
              stateMapping.get(n.getNumber()), stateMapping.get(idest), ilabel);
          transitionMapping.put(iTransition, t);
          stateMapping.get(n.getNumber()).outgoingTransitions().add(t);
          stateMapping.get(idest).incomingTransitions().add(t);
        }
      }
    }
    stateMapping.get(initialState).setFinal(true);
    Automaton logAutomaton = new Automaton(stateMapping, globalLabelMapping, globalInverseLabels, transitionMapping,
        initialState, finalStates, projectedLogs.get(component), caseIDs);//, concurrencyOracle);
    //long conversion = System.nanoTime();
    //System.out.println("Log Automaton creation: " + TimeUnit.MILLISECONDS.convert((automaton - start), TimeUnit.NANOSECONDS) + "ms");
    //System.out.println("Log Automaton conversion: " + TimeUnit.MILLISECONDS.convert((conversion - automaton), TimeUnit.NANOSECONDS) + "ms");
    return logAutomaton;
  }

  private Automaton preprocessDAFSA(IntDAFSAInt fsa, Integer component) {
    int i;
    int iTransition = 0;
    int idest = 0;
    int ilabel = 0;
    int initialState = 0;
    BiMap<Integer, State> stateMapping = HashBiMap.create();
    BiMap<Integer, org.apromore.alignmentautomaton.automaton.Transition> transitionMapping = HashBiMap.create();
    IntHashSet finalStates = new IntHashSet();
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
          org.apromore.alignmentautomaton.automaton.Transition t = new org.apromore.alignmentautomaton.automaton.Transition(
              stateMapping.get(n.getNumber()), stateMapping.get(idest), ilabel);
          transitionMapping.put(iTransition, t);
          stateMapping.get(n.getNumber()).outgoingTransitions().add(t);
          stateMapping.get(idest).incomingTransitions().add(t);
        }
      }
    }
    stateMapping.get(initialState).setFinal(true);
    //Automaton logAutomaton = new Automaton(stateMapping, globalLabelMapping, globalInverseLabels, transitionMapping, initialState, finalStates, projectedLogs.get(component), caseIDs);//, concurrencyOracle);
    Automaton logAutomaton = new Automaton(stateMapping, globalLabelMapping, globalInverseLabels, transitionMapping,
        initialState, finalStates, projectedLogs.get(component), caseIDs, componentReductions.get(component),
        componentConfigurationReducedTracesMapping.get(component));
    //long conversion = System.nanoTime();
    //System.out.println("Log Automaton creation: " + TimeUnit.MILLISECONDS.convert((automaton - start), TimeUnit.NANOSECONDS) + "ms");
    //System.out.println("Log Automaton conversion: " + TimeUnit.MILLISECONDS.convert((conversion - automaton), TimeUnit.NANOSECONDS) + "ms");
    return logAutomaton;
  }

  private void decomposePetriNetIntoSComponentAutomata(Petrinet pnet, Marking initM) throws ConnectionCannotBeObtained {
    PlaceInvariantCalculator calculator = new PlaceInvariantCalculator();
    PlaceInvariantSet invMarking = calculator.calculate(context, pnet);
    SComponentSet sComps = calculateSComponents(context, pnet, invMarking);

    int i = 0;
    //System.out.println();
    for (SortedSet<PetrinetNode> component : sComps) {
      Petrinet sCompNet = new PetrinetImpl("net" + i);
      for (PetrinetNode node : component) {
        if ((node.getAttributeMap().get(AttributeMap.SHAPE).getClass().getName()
            .equals("org.processmining.models.shapes.Rectangle"))) {
          Transition tr = null;
          for (Transition t : sCompNet.getTransitions()) {
            if (t.getLabel() == node.getLabel()) {
              tr = t;
              break;
            }
          }
          if (tr == null) {
            tr = sCompNet.addTransition(node.getLabel());
          }
          tr.setInvisible(((Transition) node).isInvisible());
          for (PetrinetEdge<? extends PetrinetNode, ? extends PetrinetNode> edge : node.getGraph().getOutEdges(node)) {
            if (component.contains(edge.getTarget())) {
              Place p = null;
              for (Place pl : sCompNet.getPlaces()) {
                if (pl.getLabel() == edge.getTarget().getLabel()) {
                  p = pl;
                  break;
                }
              }
              if (p == null) {
                p = sCompNet.addPlace(edge.getTarget().getLabel());
              }
              sCompNet.addArc(tr, p);
            }
          }
        } else {
          Place p = null;
          for (Place pl : sCompNet.getPlaces()) {
            if (pl.getLabel() == node.getLabel()) {
              p = pl;
              break;
            }
          }
          if (p == null) {
            p = sCompNet.addPlace(node.getLabel());
          }
          for (PetrinetEdge<? extends PetrinetNode, ? extends PetrinetNode> edge : node.getGraph().getOutEdges(node)) {
            if (component.contains(edge.getTarget())) {
              Transition tr = null;
              for (Transition t : sCompNet.getTransitions()) {
                if (t.getLabel() == edge.getTarget().getLabel()) {
                  tr = t;
                  break;
                }
              }
              if (tr == null) {
                tr = sCompNet.addTransition(edge.getTarget().getLabel());
              }
              sCompNet.addArc(p, tr);
            }
          }
        }
      }
      i++;
      Marking m = new Marking();
      for (Place p : initM) {
        for (Place p2 : sCompNet.getPlaces()) {
          if (p2.getLabel().equals(p.getLabel())) {
            m.add(p2);
          }
        }
      }
      ImportProcessModel importer = new ImportProcessModel();
      Automaton fsm = importer.createFSMfromPetrinet(sCompNet, m, globalInverseLabels.inverse(), globalInverseLabels);
      this.sComponentImporters.add(importer);
      IntArrayList components;
      sComponentFSMs.add(fsm);
      //System.out.println(fsm.eventLabels());
      //System.out.println(globalInverseLabels.inverse());
      for (Integer event : fsm.eventLabels().keySet()) {
        if ((components = labelComponentsMapping.get(event)) == null) {
          components = new IntArrayList();
          labelComponentsMapping.put(event, components);
        }
        components.add(sComponentFSMs.size() - 1);
      }
      //sComponentFSMs.get(sComponentFSMs.size()-1).toDot("/Users/daniel/Documents/workspace/paper_tests/Sepsis/" + sCompNet.getLabel() + ".dot");
      //System.out.println(globalInverseLabels);
      //System.out.println(sComponentFSMs.get(sComponentFSMs.size()-1).eventLabels());
      //System.out.println(sComponentFSMs.get(sComponentFSMs.size()-1).inverseEventLabels());
      sComponentNets.add(sCompNet);
    }

    //Object[] o = new Object[3];
    //o[0] = sComponentNets;
    //o[1] = sComponentFSMs;
    //o[2] = labelComponentsMapping;
    //System.out.println(globalInverseLabels);
    //System.out.println(labelComponentsMapping);
    //return o;
  }

  private SComponentSet calculateSComponents(PluginContext context, PetrinetGraph net, PlaceInvariantSet invMarking) {
    // initialization
    SComponentSet nodeMarking = new SComponentSet(); // to store final
    // result

    // get place invariants
    if (invMarking == null) {
      // calculate place invariants
      PlaceInvariantCalculator calculator = new PlaceInvariantCalculator();
      invMarking = calculator.calculate(context, net);
    }

    // references
    DoubleMatrix2D incidenceMatrix = IncidenceMatrixFactory.getIncidenceMatrix(context, net);
    if (context != null && context.getProgress().isCancelled()) {
      return null;
    }

    List<Place> placeList = new ArrayList<Place>(net.getPlaces());
    List<Transition> transitionList = new ArrayList<Transition>(net.getTransitions());

    // for each place invariants filter only the one with 1 or 0 as its
    // member
    invariantLoop:
    for (MultiSet<Place> set : invMarking) {

      if (context != null && context.getProgress().isCancelled()) {
        return null;
      }

      // for one set of invariant, check each element
      Set<Integer> placeIndex = new HashSet<Integer>();
      for (PetrinetNode node : set) {
        if (set.occurrences(node) == 1) {
          placeIndex.add(placeList.indexOf(node));
        } else {
          continue invariantLoop;
        }
      }

      // until here, we have an invariant which only consists of 0 and 1

      // iterate the places, generate array of integer to dice
      // incidenceMatrix
      int[] places = new int[placeIndex.size()];
      Iterator<Integer> it = placeIndex.iterator();
      int counter = 0;
      while (it.hasNext()) {
        places[counter] = it.next();
        counter++;
      }
      // iterate all of transition, generate array of integer to dice
      // incidenceMatrix
      int[] transitions = new int[transitionList.size()];
      for (int i = 0; i < transitionList.size(); i++) {
        transitions[i] = i;
      }

      // dice incidence matrix so that it only include necessary place and
      // transitions
      DoubleMatrix2D tempIncidenceMatrix = incidenceMatrix.viewSelection(places, transitions);

      Set<Integer> transitionIndex = new HashSet<Integer>(); // to store
      // result
      // for
      // transition

      // for each columns on the diced incidence matrix, there can only be
      // 2 nonzero value with the sum of 0
      cern.colt.list.IntArrayList tempTransition = new cern.colt.list.IntArrayList();
      DoubleArrayList tempTransValue = new DoubleArrayList();
      for (int i = 0; i < tempIncidenceMatrix.columns(); i++) {

        if (context != null && context.getProgress().isCancelled()) {
          return null;
        }

        tempIncidenceMatrix.viewColumn(i).getNonZeros(tempTransition, tempTransValue);

        // as only 1 ingoing and 1 outgoing arc is permitted, number of
        // element should be 2
        // as there can only be 1 ingoing and 1 outgoing, addition
        // should be 0
        if ((tempTransition.size() == 2) && (Double.compare(0.0, tempTransValue.get(0) + tempTransValue.get(1)) == 0)) {
          // add to transitionIndex
          transitionIndex.add(i);
        } else if (tempTransition.size() != 0) {
          // this invariant has invalid transition inclusion. Continue
          // to other invariants
          continue invariantLoop;
        }
      }

      // until here, we have our S-components, add all transition and
      // places as an S-component
      SortedSet<PetrinetNode> result = new TreeSet<PetrinetNode>();
      // add all places
      Set<Place> consideredPlaces = new HashSet<Place>(placeIndex.size());

      for (int tempIndex : placeIndex) {
        Place place = placeList.get(tempIndex);
        result.add(place);
        consideredPlaces.add(place);
      }
      // add transition corresponds to each place
      for (int tempIndex : transitionIndex) {
        result.add(transitionList.get(tempIndex));
      }

      // check self loop transitions only if it is Petri net
      Map<Transition, Set<Place>> selfLoopT = SelfLoopTransitionExtract.getSelfLoopTransitions(net);
      for (Map.Entry<Transition, Set<Place>> e : selfLoopT.entrySet()) {
        if (consideredPlaces.containsAll(e.getValue())) {
          result.add(e.getKey());
        }
      }

      // add to final set
      nodeMarking.add(result);
    }

    return nodeMarking;
  }

  public void gatherStatistics() {
    if (doDecomposition) {
      for (int component = 0; component < this.sComponentFSMs.size(); component++) {
        this.scompPlaces.add(this.sComponentImporters.get(component).places);
        this.scompTransitions.add(this.sComponentImporters.get(component).transitions);
        this.scompArcs.add(this.sComponentImporters.get(component).arcs);
        this.scompSize.add(this.sComponentImporters.get(component).size);
        this.scompChoices.add(this.sComponentImporters.get(component).choice);
        this.scompParallels.add(this.sComponentImporters.get(component).parallel);
        this.scompRGNodes.add(this.sComponentImporters.get(component).rg_nodes);
        this.scompRGArcs.add(this.sComponentImporters.get(component).rg_arcs);
        this.scompRGSize.add(this.sComponentImporters.get(component).rg_size);
      }
    }
  }

  public void SCompNetToDot(int i, String filename) throws FileNotFoundException {
    SCompNetToDot(i, new PrintWriter(filename));
  }

  public void SCompNetToDot(int i, PrintWriter pw) {
    pw.println("digraph fsm {");
    pw.println("rankdir=LR;");
    pw.println("node [shape=circle,style=filled, fillcolor=white]");
    Petrinet pnet = this.sComponentNets.get(i);
    for (Place p : pnet.getPlaces()) {
      pw.printf("%d [label=\"%s\"];%n", p.hashCode(), p.getLabel());
    }
    pw.println("node [shape=box,style=filled, fillcolor=white]");
    for (Transition tr : pnet.getTransitions()) {
      pw.printf("%d [label=\"%s\"];%n", tr.hashCode(), tr.getLabel());
      for (PetrinetEdge edge : pnet.getOutEdges(tr)) {
        Place target = (Place) edge.getTarget();
        pw.printf("%d -> %d;%n", tr.hashCode(), target.hashCode());
      }
    }
    for (Place p : pnet.getPlaces()) {
      for (PetrinetEdge edge : pnet.getOutEdges(p)) {
        Transition target = (Transition) edge.getTarget();
        pw.printf("%d -> %d;%n", p.hashCode(), target.hashCode());
      }
    }
    pw.println("}");
    pw.close();
  }
}
