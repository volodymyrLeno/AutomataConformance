package au.qut.apromore.ScalableConformanceChecker;

import au.qut.apromore.automaton.Automaton;
import au.qut.apromore.automaton.Transition;
import au.qut.apromore.importer.DecodeTandemRepeats;
import au.qut.apromore.importer.DecomposingConformanceImporter;
import au.qut.apromore.importer.DecomposingTRImporter;
import au.qut.apromore.importer.ImportEventLog;
import com.google.common.collect.HashBiMap;
import org.apache.commons.lang3.ArrayUtils;
import org.deckfour.xes.extension.XExtension;
import org.deckfour.xes.extension.std.XConceptExtension;
import org.deckfour.xes.factory.XFactoryNaiveImpl;
import org.deckfour.xes.model.*;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.UnifiedMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntIntHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;
import org.eclipse.collections.impl.set.mutable.primitive.IntHashSet;
import org.processmining.models.graphbased.directed.petrinet.PetrinetGraph;
import org.processmining.plugins.petrinet.replayresult.PNMatchInstancesRepResult;
import org.processmining.plugins.petrinet.replayresult.PNRepResult;
import org.processmining.plugins.petrinet.replayresult.StepTypes;
import org.processmining.plugins.replayer.replayresult.AllSyncReplayResult;
import org.processmining.plugins.replayer.replayresult.SyncReplayResult;
import test.Alignments.AlignmentTest;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.*;

public class DecomposingTRConformanceChecker
{
    public DecomposingTRImporter decompositions;
    public UnifiedMap<Integer, TRConformanceChecker> componentAlignments = new UnifiedMap<Integer, TRConformanceChecker>();
    public PNMatchInstancesRepResult alignmentResult = new PNMatchInstancesRepResult(new TreeSet<AllSyncReplayResult>());
    private double minModelMoves;
    public  UnifiedMap<IntArrayList, AllSyncReplayResult> caseReplayResultMapping = new UnifiedMap<IntArrayList, AllSyncReplayResult>();
    public int conflict = 0;
    public int recovered =0;
    public double logSize = 0;
    UnifiedMap<Integer, AllSyncReplayResult> projectedAlignments = new UnifiedMap<Integer, AllSyncReplayResult>();

    public DecomposingTRConformanceChecker(DecomposingTRImporter decompositions) throws Exception
    {
        this.decompositions = decompositions;
        //long start = System.nanoTime();
        if(decompositions.doDecomposition) {
            this.checkConformanceForComponents();
            this.recomposeConformance();
        }
        else
        {
            //System.out.println(decompositions.globalInverseLabels);
            componentAlignments.put(0,new TRConformanceChecker(decompositions.dafsa, decompositions.modelFSM, Integer.MAX_VALUE));
            alignmentResult = componentAlignments.get(0).resOneOptimal();
            logSize = decompositions.xLog.size();
        }
    }

    public void checkConformanceForComponents()
    {
        double start = System.currentTimeMillis();
        decompositions.minModelMoves = new TRConformanceChecker(decompositions.modelFSM).minModelMoves;
        int component;
        //ScalableConformanceChecker fitnessChecker;
        IntIntHashMap minModelLabels = new IntIntHashMap();
        //parallelize here!
        ArrayList<Integer> compList = new ArrayList<Integer>();
        for(int pos = 0; pos < decompositions.sComponentFSMs.size(); pos++) compList.add(pos);
        compList.parallelStream().forEach
                (
                        sComp -> componentAlignments.put
                                (
                                        sComp,
                                        new TRConformanceChecker(decompositions.componentDAFSAs.get(sComp), decompositions.sComponentFSMs.get(sComp), Integer.MAX_VALUE)
                                )
                );
		/*for(int pos=0; pos < decompositions.sComponentFSMs.size(); pos++)
		{
			componentAlignments.put(pos,new ScalableConformanceChecker(decompositions.componentDAFSAs.get(pos), decompositions.sComponentFSMs.get(pos), Integer.MAX_VALUE));
		}*/
        /*for(Automaton modelFSM : decompositions.sComponentFSMs)
        {
            for(int label : modelFSM.minimalFinalConfig.keySet().toArray())
            {
                if(!minModelLabels.contains(label))
                    minModelLabels.addToValue(label, modelFSM.minimalFinalConfig.get(label));
            }
        }*/

		/*for(component=0; component < decompositions.sComponentFSMs.size(); component++)
		{
			System.out.println("Component : " + component + " - " + decompositions.sComponentFSMs.get(component).eventLabels());
			Automaton modelFSM = decompositions.sComponentFSMs.get(component);
			Automaton logFSM = decompositions.componentDAFSAs.get(component);
			fitnessChecker = new ScalableConformanceChecker(logFSM, modelFSM, Integer.MAX_VALUE);
			componentAlignments.put(component, fitnessChecker);
			for(int label : modelFSM.minimalFinalConfig.keySet().toArray())
			{
				if(!minModelLabels.contains(label))
					minModelLabels.addToValue(label, modelFSM.minimalFinalConfig.get(label));
			}
		}*/
        //this.minModelMoves = (int) minModelLabels.sum();
        //System.out.println(System.currentTimeMillis() - start + " ms");
        //this.minModelMoves = ((new SingleTraceConformanceChecker(new IntArrayList(),decompositions.modelFSM,decompositions.globalLabelMapping, decompositions.globalInverseLabels, new UnifiedMap<>())).res.getInfo().get(PNRepResult.RAWFITNESSCOST));

    }

    public void recomposeConformance() throws Exception
    {
        //System.out.println("Start recomposing: " + decompositions.traceProjections.size() + " traces");
        double start;
        UnifiedMap<Integer, IntArrayList> projectedTraces;
        int modelMoves, logMoves, matchingMoves;
        int event;
        int modelMoveEvent;
        int curEvent;
        StepTypes curStep;
        String eventLabel=null;
        List<List<Object>> listOfAlignmentsLabels;
        List<List<StepTypes>> listOfAlignmentsOperations;
        List<Object> labels;
        List<StepTypes> operations;
        AllSyncReplayResult res;
        IntArrayList relevantComponents;
        IntArrayList relevantModelMoveComponents;
        IntHashSet relevantModelLabels;
        IntArrayList coherentMoveComps;
        boolean stitchingRule1, stitchingRule2, stitchingRule3;
        int i=0;
        XFactoryNaiveImpl xFac = new XFactoryNaiveImpl();
        XLog rescueLog = xFac.createLog();
        IntObjectHashMap<IntArrayList> rescueMapping = new IntObjectHashMap<>();
        XExtension xtend = XConceptExtension.instance();
        XAttributeLiteral xAttrLiteral = null;//xFac.createAttributeLiteral("concept:name", "", xtend);
        for(IntArrayList trace : decompositions.traceProjections.keySet())
        {
            //System.out.println(++i);
            start = System.currentTimeMillis();
            projectedTraces = decompositions.traceProjections.get(trace);
            IntIntHashMap ids = new IntIntHashMap();
            for(int comp : projectedTraces.keySet())
            {
                UnifiedMap<IntArrayList, AllSyncReplayResult> test = componentAlignments.get(comp).traceAlignmentsMapping;
                projectedAlignments.put(comp, test.get(projectedTraces.get(comp)));
                ids.put(comp, 0);
            }
            listOfAlignmentsLabels = new ArrayList<List<Object>>();
            listOfAlignmentsOperations = new ArrayList<List<StepTypes>>();
            labels = new ArrayList<Object>();
            operations = new ArrayList<StepTypes>();
            listOfAlignmentsLabels.add(labels);
            listOfAlignmentsOperations.add(operations);
            res = new AllSyncReplayResult(listOfAlignmentsLabels, listOfAlignmentsOperations, -1, true);
			/*System.out.println(trace);
			//for(int ev : trace.toArray())
			//	System.out.print(decompositions.globalInverseLabels.inverse().get(ev) + ", ");
			//System.out.println();
			for(int compo : projectedAlignments.keySet())
			{
				if(!projectedAlignments.get(compo).getNodeInstanceLst().isEmpty()) {
					String alignment = "[ ";
					for (int pos = 0; pos < projectedAlignments.get(compo).getNodeInstanceLst().get(0).size(); pos++) {
						alignment += "(" + projectedAlignments.get(compo).getStepTypesLst().get(0).get(pos) + "," + decompositions.globalInverseLabels.get(projectedAlignments.get(compo).getNodeInstanceLst().get(0).get(pos)) + "), ";
					}
					//System.out.println(compo + " = " + projectedAlignments.get(compo).getNodeInstanceLst().get(0));
					//System.out.println(compo + " = " + projectedAlignments.get(compo).getStepTypesLst().get(0));
					alignment = alignment.substring(0, alignment.length() - 2) + "]";
					System.out.println(compo + " = " + alignment);
				}
			}*/
            modelMoves = 0;
            logMoves = 0;
            matchingMoves = 0;
            boolean conflictOccurred = false;
            for(int pos=0;pos<=trace.size();pos++)
            {
                conflictOccurred = false;
                if(pos<trace.size())
                    event = trace.get(pos);
                else
                    event=-10;
                relevantComponents = new IntArrayList();
				/*for(int comp : projectedTraces.keySet())
					if(!projectedAlignments.get(comp).getNodeInstanceLst().isEmpty())
						if(ids.get(comp) < projectedAlignments.get(comp).getNodeInstanceLst().get(0).size())
							if(projectedTraces.get(comp).contains(event) || event==-10)
								relevantComponents.add(comp);*/
                for(int comp : projectedAlignments.keySet())
                    if(containsLabel(comp, event, ids.get(comp)) || event==-10)
                        relevantComponents.add(comp);
                if(relevantComponents.isEmpty() && event>=0)
                {
                    labels.add(decompositions.globalLabelMapping.get(event));
                    operations.add(StepTypes.L);
                    logMoves++;
                    continue;
                }
                do
                {
                    boolean stepNecessary = false;
                    //relevantModelMoveComponents = new IntArrayList();
                    relevantModelLabels = new IntHashSet();
                    for(int comp : relevantComponents.toArray())
                    {
                        try {
                            if (ids.get(comp) < projectedAlignments.get(comp).getNodeInstanceLst().get(0).size()) {
                                eventLabel = (String) projectedAlignments.get(comp).getNodeInstanceLst().get(0).get(ids.get(comp));
                                curEvent = decompositions.globalInverseLabels.get(eventLabel);
                                curStep = projectedAlignments.get(comp).getStepTypesLst().get(0).get(ids.get(comp));
                                if ((curEvent != event && curStep == StepTypes.MREAL) || event == -10) {
                                    stepNecessary = true;
                                    //relevantModelMoveComponents.add(comp);
                                    relevantModelLabels.add(curEvent);
                                }
                            }
                        } catch(Exception e)
                        {
                            //System.out.println(e.getMessage());
                        }
                    }
                    if(!stepNecessary) break;
                    boolean stepAdded = false;
                    for (int label : relevantModelLabels.toArray())
                    {
                        boolean isCoherent = true;
                        IntArrayList actModelMoveComps = new IntArrayList();
                        for(int comp : projectedAlignments.keySet())
                        {
                            if(containsLabel(comp,label,ids.get(comp)))
                            {
                                if(projectedAlignments.get(comp).getStepTypesLst().get(0).get(ids.get(comp)) != StepTypes.MREAL || decompositions.globalInverseLabels.get(projectedAlignments.get(comp).getNodeInstanceLst().get(0).get(ids.get(comp)))!=label)
                                {
                                    isCoherent = false;
                                }
                                else actModelMoveComps.add(comp);
                            }
                        }
                        if(isCoherent)
                        {
                            int firstRelComp = actModelMoveComps.get(0);
                            labels.add(projectedAlignments.get(firstRelComp).getNodeInstanceLst().get(0).get(ids.get(firstRelComp)));
                            operations.add(projectedAlignments.get(firstRelComp).getStepTypesLst().get(0).get(ids.get(firstRelComp)));
                            for(int comp : actModelMoveComps.toArray()) ids.put(comp, ids.get(comp) + 1);
                            stepAdded = true;
                            modelMoves++;
                            break;
                        }
                    }
                    if(!stepAdded)
                    {
                        //System.out.println("Model move conflict while synchronizing : " + event);
                        conflict++;
                        //System.out.println(trace);
                        XTrace xTr = xFac.createTrace();
                        for(int ev : trace.toArray()) {
                            xAttrLiteral = xFac.createAttributeLiteral("concept:name", decompositions.globalInverseLabels.inverse().get(ev), xtend);
                            XAttributeMap xAttr = xFac.createAttributeMap();
                            xAttr.put("concept:name", xAttrLiteral);
                            XEvent xEv = xFac.createEvent(xAttr);
                            xTr.add(xEv);
                            //System.out.print(decompositions.globalInverseLabels.inverse().get(ev) + ", ");
                        }
                        rescueLog.add(xTr);
                        rescueMapping.put(rescueLog.size()-1, trace);

						/*System.out.println();
						for(int compo : projectedAlignments.keySet())
						{
							if(!projectedAlignments.get(compo).getNodeInstanceLst().isEmpty()) {
								String alignment = " [";
								for (int pos2 = 0; pos2 < projectedAlignments.get(compo).getNodeInstanceLst().get(0).size(); pos2++) {
									alignment += "(" + projectedAlignments.get(compo).getStepTypesLst().get(0).get(pos2) + "," + decompositions.globalInverseLabels.get(projectedAlignments.get(compo).getNodeInstanceLst().get(0).get(pos2)) + "), ";
								}
								//System.out.println(compo + " = " + projectedAlignments.get(compo).getNodeInstanceLst().get(0));
								//System.out.println(compo + " = " + projectedAlignments.get(compo).getStepTypesLst().get(0));
								alignment = alignment.substring(0, alignment.length() - 2) + "]";
								System.out.println(compo + " = " + alignment);
							}
						}
						String alignment = " [";
						for(int pos2=0; pos2 < res.getNodeInstanceLst().get(0).size(); pos2++)
						{
							alignment += "(" + res.getStepTypesLst().get(0).get(pos2) + "," + decompositions.globalInverseLabels.get(res.getNodeInstanceLst().get(0).get(pos2)) + "), ";
						}
						alignment = alignment.substring(0,alignment.length()-2) + "]";
						System.out.println("Recomposed alignment: " + alignment);*/
                        conflictOccurred=true;
                        break;
                    }
                }
                while(!relevantModelLabels.isEmpty());
                if(conflictOccurred || event ==-10) break;
                int it1=0;
                for(it1=0; it1 < relevantComponents.size(); it1++)
                {
                    boolean isCoherent = true;
                    int comp = relevantComponents.get(it1);
                    eventLabel = (String) projectedAlignments.get(comp).getNodeInstanceLst().get(0).get(ids.get(comp));
                    curEvent = decompositions.globalInverseLabels.get(eventLabel);
                    if (curEvent != event) { conflictOccurred = true; break; }
                    curStep = projectedAlignments.get(comp).getStepTypesLst().get(0).get(ids.get(comp));
                    for (int it2 = 0; it2 < relevantComponents.size(); it2++) {
                        int comp2 = relevantComponents.get(it2);
                        eventLabel = (String) projectedAlignments.get(comp2).getNodeInstanceLst().get(0).get(ids.get(comp2));
                        int curEvent2 = decompositions.globalInverseLabels.get(eventLabel);
                        StepTypes curStep2 = projectedAlignments.get(comp2).getStepTypesLst().get(0).get(ids.get(comp2));
                        if (curEvent2 != event || curStep != curStep2) {
                            boolean swapFound = false;
                            for(int it3=ids.get(comp2)+1;it3<projectedAlignments.get(comp2).getNodeInstanceLst().get(0).size();it3++)
                            {
                                eventLabel = (String) projectedAlignments.get(comp2).getNodeInstanceLst().get(0).get(it3);
                                int curEvent3 = decompositions.globalInverseLabels.get(eventLabel);
                                StepTypes curStep3 = projectedAlignments.get(comp2).getStepTypesLst().get(0).get(it3);
                                if(curStep3 == StepTypes.MREAL || (curStep3==StepTypes.LMGOOD && curEvent3!=event)) break;
                                else if(curStep3==StepTypes.L && curEvent3!=event) continue;
                                if (curEvent2 == curEvent3 && curEvent3 == event && curStep3 == curStep)
                                {
                                    projectedAlignments.get(comp2).getStepTypesLst().get(0).set(ids.get(comp2), curStep3);
                                    projectedAlignments.get(comp2).getStepTypesLst().get(0).set(it3, curStep2);
                                    swapFound = true;
                                }
                                break;
                            }
                            if(swapFound) continue;
                            isCoherent = false;
                            break;
                        }
                    }
                    if (isCoherent)
                    {
                        labels.add(eventLabel);
                        operations.add(curStep);
                        if (curStep == StepTypes.L) logMoves++;
                        for (int compo : relevantComponents.toArray()) ids.put(compo, ids.get(compo) + 1);
                        break;
                    }
                }
                if(it1==relevantComponents.size()) conflictOccurred=true;
                if(conflictOccurred) {
                    //System.out.println("Log move conflict while synchronizing : " + event);
                    conflict++;
                    //System.out.println(trace);
                    XTrace xTr = xFac.createTrace();
                    for(int ev : trace.toArray()) {
                        xAttrLiteral = xFac.createAttributeLiteral("concept:name", decompositions.globalInverseLabels.inverse().get(ev), xtend);
                        XAttributeMap xAttr = xFac.createAttributeMap();
                        //xAttrLiteral.setValue(decompositions.globalInverseLabels.inverse().get(ev));
                        xAttr.put("concept:name", xAttrLiteral);
                        XEvent xEv = xFac.createEvent(xAttr);
                        xTr.add(xEv);
                        //System.out.print(decompositions.globalInverseLabels.inverse().get(ev) + ", ");
                    }
                    rescueLog.add(xTr);
                    rescueMapping.put(rescueLog.size()-1, trace);
					/*System.out.println();
					for(int compo : projectedAlignments.keySet())
					{
						if(!projectedAlignments.get(compo).getNodeInstanceLst().isEmpty()) {
							String alignment = " [";
							for (int pos2 = 0; pos2 < projectedAlignments.get(compo).getNodeInstanceLst().get(0).size(); pos2++) {
								alignment += "(" + projectedAlignments.get(compo).getStepTypesLst().get(0).get(pos2) + "," + decompositions.globalInverseLabels.get(projectedAlignments.get(compo).getNodeInstanceLst().get(0).get(pos2)) + "), ";
							}
							//System.out.println(compo + " = " + projectedAlignments.get(compo).getNodeInstanceLst().get(0));
							//System.out.println(compo + " = " + projectedAlignments.get(compo).getStepTypesLst().get(0));
							alignment = alignment.substring(0, alignment.length() - 2) + "]";
							System.out.println(compo + " = " + alignment);
						}
					}
					String alignment = " [";
					for(int pos2=0; pos2 < res.getNodeInstanceLst().get(0).size(); pos2++)
					{
						alignment += "(" + res.getStepTypesLst().get(0).get(pos2) + "," + decompositions.globalInverseLabels.get(res.getNodeInstanceLst().get(0).get(pos2)) + "), ";
					}
					alignment = alignment.substring(0,alignment.length()-2) + "]";
					System.out.println("Recomposed alignment: " + alignment);*/
                    break;
                }
            }
            //if(conflictOccurred) res = new SingleTraceConformanceChecker(trace, decompositions.modelFSM, decompositions.globalInverseLabels.inverse(), decompositions.globalInverseLabels, decompositions.caseTracesMapping, decompositions.caseIDs).res;
            if(conflictOccurred) continue;
            IntHashSet toBeVisited = new IntHashSet();
            IntHashSet next;
            toBeVisited.add(decompositions.modelFSM.sourceID());
            //if(res.getNodeInstanceLst().get(0).size()==1) {
            //	if (((String) res.getNodeInstanceLst().get(0).get(0)).equals("INS_DIPLOMI_UNIV")) {
            //		System.out.print("");
            //	}
            //}
            for(int pos=0; pos < res.getNodeInstanceLst().get(0).size(); pos++)
            {
                if(toBeVisited.isEmpty())
                {
                    conflictOccurred=true;
                    conflict++;
                    XTrace xTr = xFac.createTrace();
                    for(int ev : trace.toArray()) {
                        xAttrLiteral = xFac.createAttributeLiteral("concept:name", decompositions.globalInverseLabels.inverse().get(ev), xtend);
                        XAttributeMap xAttr = xFac.createAttributeMap();
                        xAttr.put("concept:name", xAttrLiteral);
                        XEvent xEv = xFac.createEvent(xAttr);
                        xTr.add(xEv);
                    }
                    rescueLog.add(xTr);
                    rescueMapping.put(rescueLog.size()-1, trace);
                    break;
                }
                if(res.getStepTypesLst().get(0).get(pos) == StepTypes.L) continue;
                int curEventID = decompositions.modelFSM.inverseEventLabels().get(res.getNodeInstanceLst().get(0).get(pos));
                next = new IntHashSet();
                for(int curNode : toBeVisited.toArray())
                {
                    for(Transition tr : decompositions.modelFSM.states().get(curNode).outgoingTransitions())
                    {
                        if(tr.eventID()==curEventID) next.add(tr.target().id());
                    }
                }
                toBeVisited = next;
            }
            if(conflictOccurred) continue;
            boolean isCoherent = false;
            for(int state : toBeVisited.toArray())
            {
                if(decompositions.modelFSM.states().get(state).isFinal())
                {
                    isCoherent = true;
                    break;
                }
            }
            if(!isCoherent)
            {
                conflictOccurred=true;
                conflict++;
                XTrace xTr = xFac.createTrace();
                for(int ev : trace.toArray()) {
                    xAttrLiteral = xFac.createAttributeLiteral("concept:name", decompositions.globalInverseLabels.inverse().get(ev), xtend);
                    XAttributeMap xAttr = xFac.createAttributeMap();
                    xAttr.put("concept:name", xAttrLiteral);
                    XEvent xEv = xFac.createEvent(xAttr);
                    xTr.add(xEv);
                }
                rescueLog.add(xTr);
                rescueMapping.put(rescueLog.size()-1, trace);
            }
            if(conflictOccurred) continue;
            res.getTraceIndex().remove(-1);
            Integer[] relevantTraces = ArrayUtils.toObject(decompositions.caseTracesMapping.get(trace).toArray());
            res.getTraceIndex().addAll(Arrays.<Integer>asList( relevantTraces));
            res.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) res.getStepTypesLst().size());
            res.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST, (double) (modelMoves + logMoves));
            double numStates = 0;
            double queuedStates = 0;
            for(int comp : projectedAlignments.keySet())
            {
                numStates += projectedAlignments.get(comp).getInfo().get(PNMatchInstancesRepResult.NUMSTATES);
                queuedStates += projectedAlignments.get(comp).getInfo().get(PNMatchInstancesRepResult.QUEUEDSTATE);
            }
            res.addInfo(PNMatchInstancesRepResult.NUMSTATES, numStates);
            res.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE, queuedStates);
            res.addInfo(PNMatchInstancesRepResult.ORIGTRACELENGTH, (double) trace.size());
            res.addInfo(PNMatchInstancesRepResult.TIME, (double) (System.currentTimeMillis() - start));
            res.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, (double) 1-res.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) / (res.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) + this.minModelMoves));
            //if(!moveLogFitness.isEmpty())
            double percentLogMoves = (double) logMoves / (logMoves + matchingMoves);
            double moveLogFitness = 1 - (percentLogMoves);
            res.addInfo(PNRepResult.MOVELOGFITNESS, moveLogFitness);
            //if(!moveModelFitness.isEmpty())
            double percentModelMoves = (double) modelMoves / (modelMoves + matchingMoves);
            double moveModelFitness = 1 - percentModelMoves;
            res.addInfo(PNRepResult.MOVEMODELFITNESS, moveModelFitness);
            alignmentResult.add(res);
            IntArrayList traces = new IntArrayList();
            traces.addAll(decompositions.caseTracesMapping.get(trace).toArray());
            this.caseReplayResultMapping.put(traces, res);
            //System.out.println(conflict);
			/*String alignment = " [";
			for(int pos=0; pos < res.getNodeInstanceLst().get(0).size(); pos++)
			{
				alignment += "(" + res.getStepTypesLst().get(0).get(pos) + "," + decompositions.globalInverseLabels.get(res.getNodeInstanceLst().get(0).get(pos)) + "), ";
			}
			alignment = alignment.substring(0,alignment.length()-2) + "]";
			System.out.println("Recomposed alignment: " + alignment);*/
            //System.out.println(compo + " = " + projectedAlignments.get(compo).getNodeInstanceLst().get(0));
            //System.out.println(compo + " = " + projectedAlignments.get(compo).getStepTypesLst().get(0));
			/*System.out.println(res.getNodeInstanceLst().get(0));
			System.out.println(res.getStepTypesLst().get(0));
			System.out.println(res.getInfo());*/
        }
        if(conflict > 0)
        {
            //System.out.println(conflict);
            //PNRepResult rescueRes = AlignmentTest.computeCost((PetrinetGraph) decompositions.pnet, rescueLog);
            PNMatchInstancesRepResult rescueRes = new TRConformanceChecker(new ImportEventLog().createReducedDAFSAfromLog(rescueLog,decompositions.globalInverseLabels),decompositions.modelFSM, Integer.MAX_VALUE).resOneOptimal();
            //System.out.println(rescueRes.size());
            //System.out.println(rescueRes.getInfo().get(PNRepResult.RAWFITNESSCOST));
            for(AllSyncReplayResult rescueres : rescueRes)
            {
                listOfAlignmentsLabels = new ArrayList<List<Object>>();
                listOfAlignmentsOperations = new ArrayList<List<StepTypes>>();
                AllSyncReplayResult res2 = new AllSyncReplayResult(listOfAlignmentsLabels, listOfAlignmentsOperations, -1, true);
                listOfAlignmentsLabels.add(rescueres.getNodeInstanceLst().get(0));
                listOfAlignmentsOperations.add(rescueres.getStepTypesLst().get(0));
                res2.getTraceIndex().remove(-1);
                Integer[] relevantTraces = ArrayUtils.toObject(decompositions.caseTracesMapping.get(rescueMapping.get(rescueres.getTraceIndex().first())).toArray());
                res2.getTraceIndex().addAll(Arrays.<Integer>asList( relevantTraces));
                res2.setInfo(rescueres.getInfo());
                res2.getInfo().put(PNMatchInstancesRepResult.NUMALIGNMENTS, 1.0);
                alignmentResult.add(res2);
                recovered++;
            }
            //XesXmlGZIPSerializer exporter = new XesXmlGZIPSerializer();
            //try {
            //	exporter.serialize(rescueLog, new FileOutputStream(new File(decompositions.path + "rescueLog.xes.gz")));
            //} catch (IOException e) {
            //	e.printStackTrace();
            //}
        }
        //System.out.println(recovered);
        double time = 0;
        double rawFitnessCost = 0;
        double numStates = 0;
        double numAlignments = 0;
        double traceFitness = 0;
        double moveModelFitness = 0;
        double moveLogFitness = 0;
        double traceLength = 0;
        double queuedStates = 0;
        logSize =  decompositions.xLog.size();
        //System.out.println(logSize + " - " + alignmentResult.size() + " - " + decompositions.caseTracesMapping.size());
        //System.out.println(logSize);
        //for(IntArrayList trace : decompositions.caseTracesMapping.keySet())
        //{
        //	logSize += decompositions.caseTracesMapping.get(trace).size();
        //}
        int numTraces=0;
        int totTraces =0;
        for(AllSyncReplayResult result : this.alignmentResult)
        {
            if(result.isReliable())
            {
                numTraces = result.getTraceIndex().size();
                totTraces += numTraces;
                time += (result.getInfo().get(PNMatchInstancesRepResult.TIME) * numTraces);
                rawFitnessCost += (result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) * numTraces);
                numStates += (result.getInfo().get(PNMatchInstancesRepResult.NUMSTATES) * numTraces);
                numAlignments += result.getInfo().get(PNMatchInstancesRepResult.NUMALIGNMENTS);
                traceFitness += (result.getInfo().get(PNMatchInstancesRepResult.TRACEFITNESS) * numTraces);
                moveModelFitness += (result.getInfo().get(PNRepResult.MOVEMODELFITNESS) * numTraces);
                moveLogFitness += (result.getInfo().get(PNRepResult.MOVELOGFITNESS) * numTraces);
                traceLength += (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) * numTraces);
                queuedStates += (result.getInfo().get(PNMatchInstancesRepResult.QUEUEDSTATE) * numTraces);
            }
        }
        //System.out.println("Total traces: " + totTraces);
        this.alignmentResult.addInfo(PNMatchInstancesRepResult.TIME, "" + (time / logSize));
        this.alignmentResult.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST, "" + (rawFitnessCost / logSize));
        this.alignmentResult.addInfo(PNMatchInstancesRepResult.NUMSTATES, "" + (numStates / logSize));
        this.alignmentResult.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, "" + numAlignments);
        this.alignmentResult.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, "" +  (traceFitness / logSize));
        this.alignmentResult.addInfo(PNRepResult.MOVEMODELFITNESS, "" + (moveModelFitness  / logSize));
        this.alignmentResult.addInfo(PNRepResult.MOVELOGFITNESS, "" + (moveLogFitness / logSize));
        this.alignmentResult.addInfo(PNRepResult.ORIGTRACELENGTH, "" + traceLength / logSize);
        this.alignmentResult.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE, "" + queuedStates / logSize);
        //this.timeOneOptimal =TimeUnit.MILLISECONDS.convert(System.nanoTime() - start,TimeUnit.NANOSECONDS);
        //System.out.println(alignmentResult.getInfo());
        //double ratio = conflict / decompositions.caseTracesMapping.size();
        //System.out.println(conflict + " / " + decompositions.caseTracesMapping.size() + " = " + ratio);
        //System.out.println(decompositions.globalInverseLabels);
    }

    private boolean containsLabel(int comp, int label, int id)
    {
        AllSyncReplayResult alignment = projectedAlignments.get(comp);
        if(alignment.getNodeInstanceLst().isEmpty()) return false;
        int size = alignment.getNodeInstanceLst().get(0).size();
        if(size<=id) return false;
        for(int pos=id;pos<size;pos++) {
            String eventLabel = (String) alignment.getNodeInstanceLst().get(0).get(pos);
            int eventID = decompositions.globalInverseLabels.get(eventLabel);
            if(label==eventID) return true;
        }
        return false;
    }

    public void printAlignmentResults(String alignmentStatisticsFile, String caseTypeAlignmentResultsFile) throws FileNotFoundException
    {
        PrintWriter pw1 = new PrintWriter(alignmentStatisticsFile);
        PrintWriter pw2 = new PrintWriter(caseTypeAlignmentResultsFile);

        pw1.println("Average Log Alignment Statistics per Case Type:");
        pw1.println(PNMatchInstancesRepResult.RAWFITNESSCOST + "," + PNMatchInstancesRepResult.ORIGTRACELENGTH + "," + PNMatchInstancesRepResult.QUEUEDSTATE + ","
                + PNMatchInstancesRepResult.NUMSTATES + "," + PNMatchInstancesRepResult.TIME + "," + PNMatchInstancesRepResult.NUMALIGNMENTS + "," + PNMatchInstancesRepResult.TRACEFITNESS);
        pw1.println(this.alignmentResult.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) + ","
                + this.alignmentResult.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) + ","
                + this.alignmentResult.getInfo().get(PNMatchInstancesRepResult.QUEUEDSTATE) + ","
                + this.alignmentResult.getInfo().get(PNMatchInstancesRepResult.NUMSTATES) + ","
                + this.alignmentResult.getInfo().get(PNMatchInstancesRepResult.TIME) + ","
                + this.alignmentResult.getInfo().get(PNMatchInstancesRepResult.NUMALIGNMENTS) + ","
                + this.alignmentResult.getInfo().get(PNMatchInstancesRepResult.TRACEFITNESS));

        pw1.println();
        pw1.println();
        pw1.println("Alignment Statistics per Case:");
        pw1.println("Num.,"
                +	"Case Type,"
                +	"Case ID,"
                +	"Trace Index,"
                +	"isReliable,"
                +	PNMatchInstancesRepResult.RAWFITNESSCOST +","
                +	PNMatchInstancesRepResult.ORIGTRACELENGTH +","
                +	PNMatchInstancesRepResult.QUEUEDSTATE +","
                +	PNMatchInstancesRepResult.NUMSTATES +","
                +	PNMatchInstancesRepResult.TIME +","
                +	PNMatchInstancesRepResult.NUMALIGNMENTS +","
                +	PNMatchInstancesRepResult.TRACEFITNESS
        );

        pw2.println("Alignments per Case Type:");
        pw2.println("Case Type, Represented number of traces,alignment(task) #1,alignment(task) #2,alignment(task) #3,...");
        int num=1, caseType =1;
        AllSyncReplayResult res;
        for(IntArrayList traces : caseReplayResultMapping.keySet())
        {
            res = caseReplayResultMapping.get(traces);
            for(int trace : traces.toArray())
            {
                pw1.println(num++ +","
                        +	caseType + ","
                        +	decompositions.caseIDs.get(trace) + ","
                        +	trace + ","
                        +	res.isReliable() + ","
                        +	res.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) +","
                        +	res.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) +","
                        +	res.getInfo().get(PNMatchInstancesRepResult.QUEUEDSTATE) +","
                        +	res.getInfo().get(PNMatchInstancesRepResult.NUMSTATES) +","
                        +	res.getInfo().get(PNMatchInstancesRepResult.TIME) +","
                        +	res.getInfo().get(PNMatchInstancesRepResult.NUMALIGNMENTS) +","
                        +	res.getInfo().get(PNMatchInstancesRepResult.TRACEFITNESS)
                );
            }
            for(int i=0;i< res.getStepTypesLst().size();i++)
            {
                List<Object> labels = res.getNodeInstanceLst().get(i);
                List<StepTypes> ops = res.getStepTypesLst().get(i);
                pw2.println();
                pw2.print(caseType +","
                        +	res.getTraceIndex().size() + ",");
                for(int j=0;j<labels.size();j++)
                {
                    pw2.print(ops.get(j) +"( " + labels.get(j) +")");
                    if(j!=labels.size()-1)
                        pw2.print(",");
                }
            }
            caseType++;
        }

        pw1.close();
        pw2.close();
    }
}
