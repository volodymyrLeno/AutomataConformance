package org.apromore.alignmentautomaton.importer;

import java.io.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
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
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;
import org.eclipse.collections.impl.set.mutable.UnifiedSet;
import org.eclipse.collections.impl.set.mutable.primitive.IntHashSet;
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
import org.processmining.plugins.petrinet.structuralanalysis.IncidenceMatrixFactory;
import org.processmining.plugins.petrinet.structuralanalysis.invariants.PlaceInvariantCalculator;
import org.processmining.plugins.petrinet.structuralanalysis.util.SelfLoopTransitionExtract;
import org.processmining.models.graphbased.directed.transitionsystem.ReachabilityGraph;

public class DecomposingConformanceImporter extends ImportProcessModel {

  public Automaton modelFSM;

  public Automaton dafsa;

  private final String conceptname = "concept:name";

  //private Map<IntArrayList, Boolean> tracesContained;
  public UnifiedMap<IntArrayList, IntArrayList> caseTracesMapping;

  //private IntObjectHashMap<String> traceIDtraceName;
  private BiMap<Integer, IntArrayList> labelComponentsMapping = HashBiMap.create();

  public List<Automaton> sComponentFSMs = new FastList<Automaton>();

  public FastList<Petrinet> sComponentNets = new FastList<Petrinet>();

  public FastList<ImportProcessModel> sComponentImporters = new FastList<>();

  public Map<Integer, String> caseIDs = new UnifiedMap<Integer, String>();

  public UnifiedMap<Integer, Automaton> componentDAFSAs = new UnifiedMap<Integer, Automaton>();

  private UnifiedSet<IntArrayList> visited = new UnifiedSet<IntArrayList>();

  private IntObjectHashMap<UnifiedSet<IntArrayList>> componentsUniqueTraces = new IntObjectHashMap<>();

  public XLog xLog;

  public UnifiedMap<IntArrayList, UnifiedMap<Integer, IntArrayList>> traceProjections = new UnifiedMap<IntArrayList, UnifiedMap<Integer, IntArrayList>>();

  public int minModelMoves;

  //private UnifiedMap<Integer, UnifiedMap<Integer, IntArrayList>> projectedLogs = new UnifiedMap<Integer, UnifiedMap<Integer, IntArrayList>>(); //TODO: ???
  private UnifiedMap<Integer, UnifiedMap<IntArrayList, IntArrayList>> projectedLogs = new UnifiedMap<Integer, UnifiedMap<IntArrayList, IntArrayList>>();

  public String path;

  private String model;

  public boolean doDecomposition = false;

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

  public IntArrayList scompRGSizeBeforeTauRemoval = new IntArrayList();

  public DecomposingConformanceImporter() {
  }

  public DecomposingConformanceImporter(Automaton modelFSM, UnifiedMap<IntArrayList, IntArrayList> caseTracesMapping,
      BiMap<Integer, IntArrayList> labelComponentsMapping, List<Automaton> sComponentFSMs,
      FastList<Petrinet> sComponentNets, FastList<ImportProcessModel> sComponentImporters, Map<Integer, String> caseIDs,
      UnifiedMap<Integer, Automaton> componentDAFSAs, UnifiedSet<IntArrayList> visited,
      IntObjectHashMap<UnifiedSet<IntArrayList>> componentsUniqueTraces, XLog xLog,
      UnifiedMap<IntArrayList, UnifiedMap<Integer, IntArrayList>> traceProjections,
      UnifiedMap<Integer, UnifiedMap<IntArrayList, IntArrayList>> projectedLogs, String path, String model,
      boolean doDecomposition, BiMap<String, Integer> globalInverseLabels, BiMap<Integer, String> globalLabelMapping) {
    this.modelFSM = modelFSM;
    this.caseTracesMapping = caseTracesMapping;
    this.labelComponentsMapping = labelComponentsMapping;
    this.sComponentFSMs = sComponentFSMs;
    this.sComponentNets = sComponentNets;
    this.sComponentImporters = sComponentImporters;
    this.caseIDs = caseIDs;
    this.componentDAFSAs = componentDAFSAs;
    this.visited = visited;
    this.componentsUniqueTraces = componentsUniqueTraces;
    this.xLog = xLog;
    this.projectedLogs = projectedLogs;
    this.path = path;
    this.model = model;
    this.doDecomposition = doDecomposition;
    this.traceProjections = traceProjections;
    this.globalInverseLabels = globalInverseLabels;
    this.globalLabelMapping = globalLabelMapping;
  }

  public void importAndDecomposeModelAndLogForConformanceChecking(String path, String model, String log)
      throws Exception {
    Object[] pnetAndMarking;
    this.path = path;
    this.model = model;
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
      pnetAndMarking = importPetriNetAndMarking(path + model);
      pnet = (Petrinet) pnetAndMarking[0];
      this.modelFSM = createFSMfromPetrinet(pnet, (Marking) pnetAndMarking[1], null, null);
    }
  }

  public void importAndDecomposeModelForStatistics(String path, String model) throws Exception {
    Object[] pnetAndMarking;
    this.path = path;
    this.model = model;
    String fileName = path + model;

    if(model.endsWith(".bpmn")){
      BPMNDiagram diagram = new BpmnImportPlugin().importFromStreamToDiagram(new FileInputStream(new File(fileName)), fileName);
      this.modelFSM = createFSMfromBPMN(diagram, null, null);
      parallel = new BPMNPreprocessor().getNonTrivialAndSplits(diagram).size();
      doDecomposition = parallel > 0;
      if(doDecomposition) decomposeBpmnDiagramIntoSComponentAutomata(diagram);
    }
    else{
      pnetAndMarking = importPetriNetAndMarking(path + model);
      pnet = (Petrinet) pnetAndMarking[0];
      Marking initM = (Marking) pnetAndMarking[1];
      this.modelFSM = createFSMfromPetrinet(pnet, (Marking) pnetAndMarking[1], null, null);
      doDecomposition = parallel > 0;
      if(doDecomposition) decomposePetriNetIntoSComponentAutomata(pnet, initM);
    }
    gatherStatistics();
  }

  public void importAndDecomposeModelAndLogForConformanceChecking(BPMNDiagram diagram, XLog xlog) throws Exception{
    this.xLog = xLog;
    this.modelFSM = createFSMfromBPMN(diagram, null, null);
    BPMNPreprocessor bpmnPreprocessor = new BPMNPreprocessor();
    parallel = bpmnPreprocessor.getNonTrivialAndSplits(diagram).size();
    doDecomposition = parallel > 0;
    if(doDecomposition){
      decomposeBpmnDiagramIntoSComponentAutomata(diagram);
      decomposeLogIntoProjectedDafsa(xLog);
    }
    else{
      dafsa = new ImportEventLog().createReducedDAFSAfromLog(xLog, modelFSM.inverseEventLabels());
    }
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
      throws Exception {
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
    } else {
      dafsa = new ImportEventLog().createDAFSAfromLog(xLog, modelFSM.inverseEventLabels());
    }
  }

  private void decomposeLogIntoProjectedDafsa(XLog xLog) throws IOException {
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
    UnifiedSet<IntArrayList> compUniqueTraces;
    XTrace trace;
    UnifiedMap<IntArrayList, IntArrayList> projectedLog;
    int i, j;
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
          if ((fsa = componentFSAs.get(component)) == null) {
            fsa = new IntDAFSAInt();
            componentFSAs.put(component, fsa);
          }
          if ((compUniqueTraces = this.componentsUniqueTraces.get(component)) == null) {
            compUniqueTraces = new UnifiedSet<>();
            this.componentsUniqueTraces.put(component, compUniqueTraces);
          }
          if (compUniqueTraces.add(projectedTraces.get(component))) {
            fsa.addMinWord(projectedTraces.get(component));
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

    //System.out.println(xLog.size());
    //System.out.println(visited.size());
    //System.out.println(globalInverseLabels);
    //System.out.println(it);
  }

  private Automaton preprocessDAFSA(IntDAFSAInt fsa, Integer component) throws IOException {
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

  private void decomposePetriNetIntoSComponentAutomata(Petrinet pnet, Marking initM) throws Exception {
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
      for (Entry<Transition, Set<Place>> e : selfLoopT.entrySet()) {
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
        this.scompRGSizeBeforeTauRemoval.add(this.sComponentImporters.get(component).rg_size_before_tau_removal);
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
