package au.qut.apromore.ScalableConformanceChecker;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.*;
import java.util.concurrent.Callable;
import java.util.concurrent.TimeUnit;

import au.qut.apromore.PetriNet.PetriNet;
import au.qut.apromore.importer.DecodeTandemRepeats;
import au.qut.apromore.psp.*;
import org.apache.commons.lang3.ArrayUtils;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.codehaus.jackson.map.DeserializerFactory;
import org.deckfour.xes.model.XAttributeMap;
import org.deckfour.xes.model.XEvent;
import org.deckfour.xes.model.XTrace;
import org.eclipse.collections.api.set.primitive.MutableIntSet;
import org.eclipse.collections.impl.list.mutable.FastList;
import org.eclipse.collections.impl.list.mutable.primitive.BooleanArrayList;
import org.eclipse.collections.impl.list.mutable.primitive.DoubleArrayList;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.UnifiedMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntIntHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntObjectHashMap;
import org.eclipse.collections.impl.set.mutable.UnifiedSet;
import org.eclipse.collections.impl.set.mutable.primitive.IntHashSet;
import org.processmining.plugins.petrinet.replayresult.PNMatchInstancesRepResult;
import org.processmining.plugins.petrinet.replayresult.PNRepResult;
import org.processmining.plugins.petrinet.replayresult.StepTypes;
import org.processmining.plugins.replayer.replayresult.AllSyncReplayResult;

import au.qut.apromore.automaton.Automaton;
import au.qut.apromore.automaton.State;
import au.qut.apromore.automaton.Transition;
import au.qut.apromore.importer.ImportEventLog;
import au.qut.apromore.importer.ImportProcessModel;
import lpsolve.LpSolve;
import lpsolve.LpSolveException;

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

public class TRConformanceChecker implements Callable<TRConformanceChecker> {

    /*static {
        try {
            System.loadLibrary("lpsolve55");
            System.loadLibrary("lpsolve55j");
        } catch (Exception e) {
            e.printStackTrace();
        }
    }*/

    private HashMap<String, String> idsMapping = new HashMap<>();
    private HashMap<String, List<String>> artificialGatewaysInfo = new HashMap<>();
    private Automaton logAutomaton;
    private Automaton modelAutomaton;
    private Automaton originalModelAutomaton;
    private PSP psp;
    private Map<IntArrayList, Set<Node>> prefixMemorizationTable;
    private IntObjectHashMap<Set<Configuration>> suffixMemorizationTable;
    private PNMatchInstancesRepResult resOneOptimal;
    private PNMatchInstancesRepResult resAllOptimal;
    private Map<IntArrayList, AllSyncReplayResult> caseReplayResultMapping;
    public UnifiedMap<IntArrayList, AllSyncReplayResult> traceAlignmentsMapping = new UnifiedMap<>();
    public int cost = 0;
    //public LongIntHashMap statePruning;
    IntIntHashMap visited = new IntIntHashMap();
    public long preperationLog;
    public long preperationModel;
    public long timeOneOptimal;
    public long timeAllOptimal;
    private int qStates=1;
    private boolean useVisited = true;
    private static LpSolve lp;
    public double logSize;
    private double epsilon = 0.0000000;
    public int fitnessProblemsSolved=0;
    public int minModelMoves;

    //Conformance Checker for reduced Tandem Repeat traces
    public TRConformanceChecker(String path, String log, String model, int stateLimit) throws Exception {
        long start = System.currentTimeMillis();
        this.logAutomaton = new ImportEventLog().convertLogToAutomatonWithTRFrom(path + "/" + log);
        System.out.println(logAutomaton.eventLabels());

        var ipm = new ImportProcessModel();
        modelAutomaton = ipm.createAutomatonFromPNMLorBPMNFile(path + model,logAutomaton.eventLabels(), logAutomaton.inverseEventLabels());
        originalModelAutomaton = ipm.originalModelAutomaton;
        idsMapping = ipm.idsMapping;
        artificialGatewaysInfo = ipm.artificialGatewaysInfo;

        System.out.println(modelAutomaton.eventLabels());
        psp = new PSP(logAutomaton, modelAutomaton);
        calculateOneOptimalAlignmentsWithTRreductionAndTraceEquivalence(stateLimit);
        //calculateOneOptimalAlignmentsWithTandemRepeats(stateLimit);
        this.timeOneOptimal = System.currentTimeMillis() - start;
    }

    public TRConformanceChecker(Automaton logAutomatonWithTrReductions, Automaton modelAutomaton, int stateLimit)
    {
        long start = System.currentTimeMillis();
        this.logAutomaton = logAutomatonWithTrReductions;
        this.modelAutomaton = modelAutomaton;
        psp = new PSP(logAutomaton, this.modelAutomaton);
        //calculateOneOptimalAlignmentsWithTandemRepeats(stateLimit);
        calculateOneOptimalAlignmentsWithTRreductionAndTraceEquivalence(stateLimit);
        this.timeOneOptimal = System.currentTimeMillis() - start;
    }

    public TRConformanceChecker call()
    {
        calculateOneOptimalAlignmentsWithTandemRepeats(Integer.MAX_VALUE);
        return this;
    }

    public TRConformanceChecker(Automaton modelAutomaton)
    {
        this.modelAutomaton = modelAutomaton;
        this.psp = new PSP(new Automaton(), modelAutomaton);
        DecodeTandemRepeats emptytrace = new DecodeTandemRepeats();
        ReducedResult minModelMoveResult = this.calculateReducedAlignmentFor(new IntIntHashMap(),emptytrace,Integer.MAX_VALUE);
        modelAutomaton.setMinNumberOfModelMoves((int) minModelMoveResult.getFinalNode().weight());
        minModelMoves = (int) minModelMoveResult.getFinalNode().weight();
        //System.out.println("Min model cost : " + (int) minModelMoveResult.getFinalNode().weight());
    }

    /*public ScalableConformanceChecker(Automaton logAutomaton, Automaton modelAutomaton, int stateLimit)
    {
        long start = System.currentTimeMillis();
        this.logAutomaton = logAutomaton;
        //System.out.println(logAutomaton.eventLabels());
        this.modelAutomaton = modelAutomaton;
        //System.out.println(modelAutomaton.eventLabels());
        Node source = new Node(logAutomaton.source(), modelAutomaton.source(),
                new Configuration(new IntArrayList(), new IntIntHashMap(), new IntArrayList(), new IntIntHashMap(), new FastList<au.qut.apromore.psp.Synchronization>(),
                        new IntArrayList(), new IntArrayList()), 0);
        source.configuration().logIDs().add(logAutomaton.sourceID()); source.configuration().modelIDs().add(modelAutomaton.sourceID());
        psp = new PSP(HashBiMap.create(), new UnifiedSet<Arc>(), source.hashCode(), logAutomaton, modelAutomaton);
        psp.nodes().put(source.hashCode(), source);
        calculateOneOptimalAlignments(stateLimit);
        //calculateAllOptimalAlignments(stateLimit);
        this.timeOneOptimal = System.currentTimeMillis() - start;
    }

    //Implement Standalone tool
    public ScalableConformanceChecker(String path, String log, String model, XLog xLog, Petrinet pnet, Marking marking, int stateLimit, boolean toDot, boolean doOneOptimal) throws IOException, ConnectionCannotBeObtained
    {
        long start = System.currentTimeMillis();
        //System.out.println("DAFSA creation");
        logAutomaton = new ImportEventLog().createDAFSAfromLog(xLog);
        long logTime = System.currentTimeMillis();
        if(toDot)
            logAutomaton.toDot(log.substring(0, log.indexOf(".")) + "_dafsa.dot");
        this.preperationLog = logTime - start;
        logTime = System.currentTimeMillis();
        //System.out.println("FSM creation");
        modelAutomaton = new ImportProcessModel().createFSMfromPetrinet(pnet, marking, logAutomaton.eventLabels(), logAutomaton.inverseEventLabels());
        long modelTime = System.currentTimeMillis();
        if(toDot)
            modelAutomaton.toDot(model.substring(0, model.indexOf(".")) + "_taulessRG.dot");
        Node source = new Node(logAutomaton.source(), modelAutomaton.source(),
                new Configuration(new IntArrayList(), new IntIntHashMap(), new IntArrayList(), new IntIntHashMap(), new FastList<au.qut.apromore.psp.Synchronization>(),
                        new IntArrayList(), new IntArrayList()), 0);
        source.configuration().logIDs().add(logAutomaton.sourceID()); source.configuration().modelIDs().add(modelAutomaton.sourceID());
        psp = new PSP(HashBiMap.create(), new UnifiedSet<Arc>(), source.hashCode(), logAutomaton, modelAutomaton);
        psp.nodes().put(source.hashCode(), source);
        this.preperationModel = modelTime - logTime;
        if(doOneOptimal)
            this.calculateOneOptimalAlignments(stateLimit);
        else
            this.calculateAllOptimalAlignments(stateLimit);
        if(toDot)
            psp.toDot(path + "psp.dot");
//		Double time = Double.parseDouble(this.resAllOptimal().getInfo().get(PNRepResult.TIME))  * this.logAutomaton.caseTracesMapping.size();
//		this.timeOneOptimal = time.intValue();
    }*/

    private void calculateOneOptimalAlignmentsWithTRreductionAndTraceEquivalence(int stateLimit)
    {
        long start = System.nanoTime();
        double time = 0;
        double rawFitnessCost = 0;
        double numStates = 0;
        double numAlignments = 0;
        double traceFitness = 0;
        double moveModelFitness = 0;
        double moveLogFitness = 0;
        double traceLength = 0;
        double queuedStates = 0;
        logSize =  0;
        for(IntArrayList trace : logAutomaton.caseTracesMapping.keySet())
        {
            logSize += logAutomaton.caseTracesMapping.get(trace).size();
        }
        DecodeTandemRepeats emptytrace = new DecodeTandemRepeats();
        ReducedResult minModelMoveResult = this.calculateReducedAlignmentFor(new IntIntHashMap(),emptytrace,stateLimit);
        modelAutomaton.setMinNumberOfModelMoves((int) minModelMoveResult.getFinalNode().weight());
        //System.out.println("Min model cost : " + (int) minModelMoveResult.getFinalNode().weight());
        fitnessProblemsSolved = 0;
        for(IntIntHashMap finalConfiguration : logAutomaton.getConfigDecoderMapping().keySet()) {

            for(IntArrayList reducedTrace : logAutomaton.getConfigDecoderMapping().get(finalConfiguration))
            {
                int min, max;
                double middle;
                int[] keySet = logAutomaton.reductions.get(reducedTrace).keySet().toArray();
                Arrays.sort(keySet);
                Couple<Integer,Integer> interval = new Couple<>(0,keySet.length-1);
                IntObjectHashMap<ReducedResult> results = new IntObjectHashMap<>();
                ReducedResult minResult, maxResult;
                FastList<Couple<Integer,Integer>> listIntervals = new FastList<>();
                listIntervals.add(interval);
                while(!listIntervals.isEmpty())
                {
                    interval = listIntervals.remove(0);
                    min = interval.getFirstElement();
                    max = interval.getSecondElement();
                    if((minResult=results.get(min))==null)
                    {
                        fitnessProblemsSolved++;
                        minResult = this.calculateReducedAlignmentFor(finalConfiguration, logAutomaton.reductions.get(reducedTrace).get(keySet[min]).getFirst(), stateLimit);
                        results.put(min,minResult);
                    }
                    if (min == max)
                    {
                        for(DecodeTandemRepeats decoder : logAutomaton.reductions.get(reducedTrace).get(keySet[min]))
                            this.extendReducedAlignment(finalConfiguration, decoder, minResult);
                        continue;
                    }
                    if((maxResult=results.get(max))==null)
                    {
                        fitnessProblemsSolved++;
                        maxResult = this.calculateReducedAlignmentFor(finalConfiguration, logAutomaton.reductions.get(reducedTrace).get(keySet[max]).getFirst(), stateLimit);
                        results.put(max,maxResult);
                    }
                    if(minResult.getFinalNode().configuration().equals(maxResult.getFinalNode().configuration()))
                    {
                        for(int pos = min; pos <= max; pos++)
                            for(DecodeTandemRepeats decoder : logAutomaton.reductions.get(reducedTrace).get(keySet[pos]))
                                this.extendReducedAlignment(finalConfiguration, decoder,minResult);
                        continue;
                    }
                    else
                    {
                        middle = (min / 1.0 + max / 1.0) / 2;
                        listIntervals.add(new Couple<>(min,(int) Math.floor(middle)));
                        listIntervals.add(new Couple<>((int) Math.ceil(middle),max));
                    }
                }
                //Without Binary search
                /*for(int reduction : logAutomaton.reductions.get(reducedTrace).keySet().toArray())
                {
                    ReducedResult res = this.calculateReducedAlignmentFor(finalConfiguration, logAutomaton.reductions.get(reducedTrace).get(reduction).getFirst(),stateLimit);
                    for(DecodeTandemRepeats decoder : logAutomaton.reductions.get(reducedTrace).get(reduction))
                        this.extendReducedAlignment(finalConfiguration, decoder,res);
                }*/
            }
        }
        //System.out.println("Number of Fitness problems solved : " + fitnessProblemsSolved);

        for(AllSyncReplayResult result : this.resOneOptimal())
        {

            if(result.isReliable())
            {
                time += (result.getInfo().get(PNMatchInstancesRepResult.TIME) * result.getTraceIndex().size());
                rawFitnessCost += (result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) * result.getTraceIndex().size());
                numStates += (result.getInfo().get(PNMatchInstancesRepResult.NUMSTATES) * result.getTraceIndex().size());
                numAlignments += result.getInfo().get(PNMatchInstancesRepResult.NUMALIGNMENTS);
                traceFitness += (result.getInfo().get(PNMatchInstancesRepResult.TRACEFITNESS) * result.getTraceIndex().size());
                moveModelFitness += (result.getInfo().get(PNRepResult.MOVEMODELFITNESS) * result.getTraceIndex().size());
                moveLogFitness += (result.getInfo().get(PNRepResult.MOVELOGFITNESS) * result.getTraceIndex().size());
                traceLength += (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) * result.getTraceIndex().size());
                queuedStates += (result.getInfo().get(PNMatchInstancesRepResult.QUEUEDSTATE) * result.getTraceIndex().size());
            }
        }
        cost = (int) rawFitnessCost;
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.TIME, "" + (time / logSize));
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST, "" + (rawFitnessCost / logSize));
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.NUMSTATES, "" + (numStates / logSize));
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, "" + numAlignments);
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, "" +  (traceFitness / logSize));
        this.resOneOptimal.addInfo(PNRepResult.MOVEMODELFITNESS, "" + (moveModelFitness  / logSize));
        this.resOneOptimal.addInfo(PNRepResult.MOVELOGFITNESS, "" + (moveLogFitness / logSize));
        this.resOneOptimal.addInfo(PNRepResult.ORIGTRACELENGTH, "" + traceLength / logSize);
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE, "" + queuedStates / logSize);
        this.timeOneOptimal =TimeUnit.MILLISECONDS.convert(System.nanoTime() - start,TimeUnit.NANOSECONDS);
        //System.out.println(this.resOneOptimal.getInfo());
        //System.out.println(this.timeOneOptimal + " ms");
    }

    private void calculateOneOptimalAlignmentsWithTandemRepeats(int stateLimit)
    {
        long start = System.nanoTime();
        double time = 0;
        double rawFitnessCost = 0;
        double numStates = 0;
        double numAlignments = 0;
        double traceFitness = 0;
        double moveModelFitness = 0;
        double moveLogFitness = 0;
        double traceLength = 0;
        double queuedStates = 0;
        logSize =  0;
        for(IntArrayList trace : logAutomaton.caseTracesMapping.keySet())
        {
            logSize += logAutomaton.caseTracesMapping.get(trace).size();
        }


        for(IntIntHashMap finalConfiguration : logAutomaton.getConfigDecoderMapping().keySet()) {

            for(IntArrayList reducedTrace : logAutomaton.getConfigDecoderMapping().get(finalConfiguration))
            {
                for(UnifiedSet<DecodeTandemRepeats> decoders : logAutomaton.reductions.get(reducedTrace).values()) {
                    for (DecodeTandemRepeats decoder : decoders) {
                        try {
                            this.calculatePartiallySynchronizedPathWithLeastSkipsFor(finalConfiguration, decoder, stateLimit);
                        } catch (Exception e) {
                            System.out.println(decoder.reducedTrace());
                            e.printStackTrace();
                        }
                    }
                }

            }
        }

        for(AllSyncReplayResult result : this.resOneOptimal())
        {

            if(result.isReliable())
            {
                time += (result.getInfo().get(PNMatchInstancesRepResult.TIME) * result.getTraceIndex().size());
                rawFitnessCost += (result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) * result.getTraceIndex().size());
                numStates += (result.getInfo().get(PNMatchInstancesRepResult.NUMSTATES) * result.getTraceIndex().size());
                numAlignments += result.getInfo().get(PNMatchInstancesRepResult.NUMALIGNMENTS);
                traceFitness += (result.getInfo().get(PNMatchInstancesRepResult.TRACEFITNESS) * result.getTraceIndex().size());
                moveModelFitness += (result.getInfo().get(PNRepResult.MOVEMODELFITNESS) * result.getTraceIndex().size());
                moveLogFitness += (result.getInfo().get(PNRepResult.MOVELOGFITNESS) * result.getTraceIndex().size());
                traceLength += (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) * result.getTraceIndex().size());
                queuedStates += (result.getInfo().get(PNMatchInstancesRepResult.QUEUEDSTATE) * result.getTraceIndex().size());
            }
        }
        cost = (int) rawFitnessCost;
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.TIME, "" + (time / logSize));
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST, "" + (rawFitnessCost / logSize));
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.NUMSTATES, "" + (numStates / logSize));
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, "" + numAlignments);
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, "" +  (traceFitness / logSize));
        this.resOneOptimal.addInfo(PNRepResult.MOVEMODELFITNESS, "" + (moveModelFitness  / logSize));
        this.resOneOptimal.addInfo(PNRepResult.MOVELOGFITNESS, "" + (moveLogFitness / logSize));
        this.resOneOptimal.addInfo(PNRepResult.ORIGTRACELENGTH, "" + traceLength / logSize);
        this.resOneOptimal.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE, "" + queuedStates / logSize);
        this.timeOneOptimal =TimeUnit.MILLISECONDS.convert(System.nanoTime() - start,TimeUnit.NANOSECONDS);
        System.out.println(this.resOneOptimal.getInfo());
        System.out.println(this.timeOneOptimal + " ms");
    }

    private void calculateAllOptimalAlignments(int stateLimit)
    {
        long start = System.nanoTime();
        double time = 0;
        double rawFitnessCost = 0;
        double numStates = 0;
        double numAlignments = 0;
        double traceFitness = 0;
        double moveModelFitness = 0;
        double moveLogFitness = 0;
        double traceLength = 0;
        double queuedStates = 0;
        double logSize =  logAutomaton.caseTracesMapping.size();
//		IntArrayList test = new IntArrayList();
//		test.addAll(0, 1, 2, 10, 3, 6,7);
        //System.out.println("#Final Configurations: " +logAutomaton.configCasesMapping().keySet().size());
//		int numTraces = 0;
//		for(IntIntHashMap finalConfiguration : logAutomaton.configCasesMapping().keySet())
//			numTraces += logAutomaton.configCasesMapping().get(finalConfiguration).size();
        //System.out.println("#Traces: " + numTraces);

       /* for(IntIntHashMap finalConfiguration : logAutomaton.configCasesMapping().keySet())
            for(IntArrayList trace : logAutomaton.configCasesMapping().get(finalConfiguration))
            {
                //System.out.println(trace + " - " + finalConfiguration);
                //if(trace.equals(test))
                try {
                    this.calculatePartiallySynchronizedPathsWithLeastSkipsFor(finalConfiguration, trace, stateLimit);
                } catch (Exception e)
                {
                    System.out.println(trace);
                    System.out.println(e.getMessage());
                }
            }*/
        for(IntIntHashMap finalConfiguration : logAutomaton.getConfigDecoderMapping().keySet()) {

            for(IntArrayList reducedTrace : logAutomaton.getConfigDecoderMapping().get(finalConfiguration))
            {
                for(UnifiedSet<DecodeTandemRepeats> decoders : logAutomaton.reductions.get(reducedTrace).values()) {
                    for (DecodeTandemRepeats decoder : decoders) {
                        try {
                            this.calculatePartiallySynchronizedPathsWithLeastSkipsFor(finalConfiguration, decoder, stateLimit);
                        } catch (Exception e) {
                            System.out.println(decoder.reducedTrace());
                            e.printStackTrace();
                        }
                    }
                }

            }
        }

        //int rel =0;
        //int nrel =0;
        for(AllSyncReplayResult result : this.resAllOptimal)
        {
            if(result.isReliable())
            {
                //rel++;
                time += (result.getInfo().get(PNMatchInstancesRepResult.TIME) * result.getTraceIndex().size());
                rawFitnessCost += (result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) * result.getTraceIndex().size());
                numStates += (result.getInfo().get(PNMatchInstancesRepResult.NUMSTATES) * result.getTraceIndex().size());
                numAlignments += result.getInfo().get(PNMatchInstancesRepResult.NUMALIGNMENTS);
                traceFitness += (result.getInfo().get(PNMatchInstancesRepResult.TRACEFITNESS) * result.getTraceIndex().size());
                moveModelFitness += (result.getInfo().get(PNRepResult.MOVEMODELFITNESS) * result.getTraceIndex().size());
                moveLogFitness += (result.getInfo().get(PNRepResult.MOVELOGFITNESS) * result.getTraceIndex().size());
                traceLength += (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) * result.getTraceIndex().size());
                queuedStates += (result.getInfo().get(PNMatchInstancesRepResult.QUEUEDSTATE) * result.getTraceIndex().size());
            }
            //else
            //nrel++;
        }
        //System.out.println("reliable: " + rel + " | not reliable: " + nrel);
        this.resAllOptimal.addInfo(PNMatchInstancesRepResult.TIME, "" + (time / logSize));
        this.resAllOptimal.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST, "" + (rawFitnessCost / logSize));
        this.resAllOptimal.addInfo(PNMatchInstancesRepResult.NUMSTATES, "" + (numStates / logSize));
        this.resAllOptimal.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, "" + numAlignments);
        this.resAllOptimal.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, "" +  (traceFitness / logSize));
        this.resAllOptimal.addInfo(PNRepResult.MOVEMODELFITNESS, "" + (moveModelFitness  / logSize));
        this.resAllOptimal.addInfo(PNRepResult.MOVELOGFITNESS, "" + (moveLogFitness / logSize));
        this.resAllOptimal.addInfo(PNRepResult.ORIGTRACELENGTH, "" + traceLength / logSize);
        this.resAllOptimal.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE, "" + queuedStates / logSize);
        this.timeAllOptimal = TimeUnit.MILLISECONDS.convert(System.nanoTime() - start, TimeUnit.NANOSECONDS);
    }

    // Implement new Data Structure
    private void calculatePartiallySynchronizedPathsWithLeastSkipsFor(IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder, int stateLimit)
    {
        double start = System.currentTimeMillis();
        PriorityQueue<Node> toBeVisited = new PriorityQueue<>(new NodeComparator());
        //FibonacciHeap<Node> toBeVisited = new FibonacciHeap<Node>();
        Node currentNode = psp.sourceNode();
        toBeVisited.offer(currentNode);
        //toBeVisited.enqueue(currentNode, currentNode.weight());
        UnifiedSet<Node> potentialFinalNodes = new UnifiedSet<Node>();
        double actMin = (double) (finalConfiguration.sum() + modelAutomaton.minNumberOfModelMoves());
        Node potentialNode;
        double numStates = 1;
        qStates = 1;
        //int sizeMoveOnLog;
        IntArrayList traceLabels = decoder.reducedTrace();

        Set<Node> prefixMemoization =  this.getPrefixMemoization(traceLabels);
        for(Node node : prefixMemoization)
        {
            potentialNode = this.cloneNodeForConfiguration(node, finalConfiguration, decoder);
            this.offerPotentialNode(potentialNode, actMin, toBeVisited);
        }

        while(!toBeVisited.isEmpty())
        {
            //currentNode = toBeVisited.dequeueMin().getValue();
            currentNode = toBeVisited.poll();
            numStates++;
            if(visited.containsKey(currentNode.hashCode()))
            {
                if(visited.get(currentNode.hashCode()) <= currentNode.weight())
                {
                    continue;
                }
            }
            visited.put(currentNode.hashCode(), (int) currentNode.weight());
            //visited.add(currentNode.hashCode());
            if(System.currentTimeMillis() - start >= 30000)
                break;
            if(numStates==stateLimit)
                break;
			/*if(suffixMemorizationTable!=null)
			{
				//long decodedStates = (long) currentNode.stateLogID() | ((long) currentNode.stateModelID() >> 32);
				Set<Configuration> set;
				if((set = suffixMemorizationTable.get(currentNode.hashCode())) != null)
					for(Configuration suffix : set)
					{
						potentialNode = this.createPotentialFinalNodeFrom(currentNode, suffix, finalConfiguration, traceLabels);
						this.offerPotentialNode(potentialNode, actMin, toBeVisited);
					}
			}*/
            if(qStates!=stateLimit)
                if(currentNode.tracePosition!=traceLabels.size())
                {
                    int expTraceLabel = traceLabels.get(currentNode.tracePosition);
                    for(Transition tlog : currentNode.stLog().outgoingTransitions())
                        if(tlog.eventID()==expTraceLabel)
                        {
                            //consider LHIDE
                            potentialNode = initializePotentialNode(currentNode, tlog, null, Configuration.Operation.LHIDE, finalConfiguration, false, decoder);
                            this.offerPotentialNode(potentialNode, actMin, toBeVisited);
                            //see if match is possible
                            for(Transition tmodel : currentNode.stModel().outgoingTransitions())
                                if(tlog.eventID()==tmodel.eventID())
                                {
                                    potentialNode = initializePotentialNode(currentNode, tlog, tmodel, Configuration.Operation.MATCH, finalConfiguration, false, decoder);
                                    this.offerPotentialNode(potentialNode, actMin, toBeVisited);
                                }
                            //break;
                        }
                }
            if(qStates!=stateLimit)
                for(Transition tmodel : currentNode.stModel().outgoingTransitions())
                {
                    potentialNode = initializePotentialNode(currentNode, null, tmodel, Configuration.Operation.RHIDE, finalConfiguration, false, decoder);
                    this.offerPotentialNode(potentialNode, actMin, toBeVisited);
                }

            if(		   currentNode.stLog().isFinal()
                    && currentNode.stModel().isFinal()
                    && currentNode.tracePosition==decoder.reducedTrace().size())
            {
                if(currentNode.weight()<actMin)
                {
                    potentialFinalNodes = new UnifiedSet<Node>();
                    actMin = currentNode.weight();
                }
                potentialFinalNodes.add(currentNode);
                //potentialFinalNodes.offer(currentNode);
                //actMin = potentialFinalNodes.peek().weight();
            }
            if(toBeVisited.isEmpty() && potentialFinalNodes.size()>0) break;
                //else if(actMin < toBeVisited.min().getPriority()) break;
            else if(actMin < toBeVisited.peek().weight()) break;
        }
        double end = System.currentTimeMillis();

        //report results
        List<List<Object>> lstNodeInstanceLst = new FastList<List<Object>>();
        List<List<StepTypes>> lstStepTypesLst = new FastList<List<StepTypes>>();
        //Node potentialFinalNode = null;
        DoubleArrayList moveLogFitness = new DoubleArrayList();
        DoubleArrayList moveModelFitness = new DoubleArrayList();
        //while(true)
        for(Node potentialFinalNode : potentialFinalNodes)
        {
            //potentialFinalNode = potentialFinalNodes.poll();
            List<Object> nodeInstanceLst = new FastList<Object>();
            List<StepTypes> stepTypesLst = new FastList<StepTypes>();
            double movesOnLog = 0;
            double movesMatching = 0;
            double moveModel = 0;
            double moveInvi = 0;

            for(au.qut.apromore.psp.Synchronization tr : potentialFinalNode.configuration().sequenceSynchronizations())
            {
                if(tr.operation() == Configuration.Operation.MATCH)
                {
                    nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                    movesMatching++;
                }
                else if(tr.operation() == Configuration.Operation.LHIDE)
                {
                    nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                    movesOnLog++;
                }
                else
                {
                    nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                    if(tr.eventModel()==modelAutomaton.skipEvent())
                    {
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                        moveInvi++;
                    }
                    else
                    {
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                        moveModel++;
                    }
                }
            }
            moveModelFitness.add(1-moveModel / (moveModel + movesMatching));
            moveLogFitness.add(1-movesOnLog / (movesOnLog + movesMatching + moveInvi));
            lstNodeInstanceLst.add(nodeInstanceLst);
            lstStepTypesLst.add(stepTypesLst);
            //this.insertPartiallySynchronizedPathIntoPSP(finalConfiguration, decoder, potentialFinalNode);
            //if(potentialFinalNodes.isEmpty() || potentialFinalNodes.peek().weight()>actMin) break;
        }

        AllSyncReplayResult result = new AllSyncReplayResult(lstNodeInstanceLst, lstStepTypesLst, -1, numStates!=stateLimit);
        result.getTraceIndex().remove(-1);
        Integer[] relevantTraces = ArrayUtils.toObject(logAutomaton.caseTracesMapping.get(traceLabels).toArray());
        result.getTraceIndex().addAll(Arrays.<Integer>asList( relevantTraces));
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) result.getStepTypesLst().size());
        result.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST, (double) actMin);
        result.addInfo(PNMatchInstancesRepResult.NUMSTATES, (double) numStates);
        result.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE, (double) numStates + toBeVisited.size());
        result.addInfo(PNMatchInstancesRepResult.ORIGTRACELENGTH, (double) traceLabels.size());
        result.addInfo(PNMatchInstancesRepResult.TIME, (double) (end - start));
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) lstNodeInstanceLst.size());
        result.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, (double) 1-result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) / (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) + modelAutomaton.minNumberOfModelMoves()));
        if(!moveLogFitness.isEmpty())
            result.addInfo(PNRepResult.MOVELOGFITNESS, moveLogFitness.average());
        else
            result.addInfo(PNRepResult.MOVELOGFITNESS, 0.0);
        if(!moveModelFitness.isEmpty())
            result.addInfo(PNRepResult.MOVEMODELFITNESS, moveModelFitness.average());
        else
            result.addInfo(PNRepResult.MOVEMODELFITNESS, 0.0);
        this.resAllOptimal().add(result);
        IntArrayList traces = new IntArrayList();
        traces.addAll(logAutomaton.caseTracesMapping.get(traceLabels).toArray());
        this.caseReplayResultMapping().put(traces, result);
    }

    //Get One Optimal Alignment as quick as possible -> Done! Implement new Data Structure
    private void calculatePartiallySynchronizedPathWithLeastSkipsFor(IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder, int stateLimit) throws IOException {
        double start = System.currentTimeMillis();
		/*int max=0;
		for(int i : traceLabels.distinct().toArray())
			max = Math.max(max,traceLabels.count(x->x==i));
		if(max>=2)
			max = max-1+1;*/
        //Set<Node> visited = new UnifiedSet<Node>();
		/*IntArrayList testTrace = new IntArrayList();
		FileWriter fw = null;
		testTrace.addAll(0, 1, 20, 20, 20, 20, 20, 20, 5, 20, 5, 20, 5, 20, 5, 20, 5, 3, 5);
		if(testTrace.equals(traceLabels)) {
			fw = new FileWriter("/Users/dreissner/Documents/Evaluations/SComponentPaper/LfMf/public/sm/1debug.txt", true);
			fw.append("Trace: " + traceLabels + "\n");
		}*/
        PriorityQueue<Node> toBeVisited = new PriorityQueue<>(new NodeComparator());
        //FibonacciHeap<Node> toBeVisited = new FibonacciHeap<Node>();
        Node currentNode = psp.sourceNode();
        //PriorityQueue<Node> potentialFinalNodes = new PriorityQueue<>(new NodeComparator());
        UnifiedSet<Node> potentialFinalNodes = new UnifiedSet<Node>();
        //int actMin = (int) (finalConfiguration.sum() + modelAutomaton.minNumberOfModelMoves());
        int minModelMoves = modelAutomaton.minNumberOfModelMoves();
        if(minModelMoves==0) minModelMoves=Integer.MAX_VALUE;
        double actMin = (double) (finalConfiguration.sum() + minModelMoves);
        Node potentialNode;
        //int sizeMoveOnLog;
        double numStates = 1;
        qStates = 1;
        //this.statePruning = new LongIntHashMap();
        visited = new IntIntHashMap();
		/*Set<Node> prefixMemoization =  this.getPrefixMemoization(traceLabels);
		for(Node node : prefixMemoization)
		{
			potentialNode = this.cloneNodeForConfiguration(node, finalConfiguration, traceLabels);
			this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);
		}*/
        this.offerPotentialNodeWithPruning(currentNode, actMin, toBeVisited);

        while(true)
        {
            //currentNode = toBeVisited.dequeueMin().getValue();
            if(toBeVisited.isEmpty() && useVisited)
            {
                useVisited=false;
                calculatePartiallySynchronizedPathWithLeastSkipsFor(finalConfiguration, decoder, stateLimit);
                return;
            }
            currentNode = toBeVisited.poll();
            numStates++;
			/*if(testTrace.equals(traceLabels)) {
			fw.append("Current Node: (" + currentNode.stateLogID() + "," + currentNode.stateModelID() + "); current sync: " + currentNode.configuration().printAlignment() + "; cost: " + currentNode.weight() +"\n");

			fw.append("Next moves: " + traceLabels +"\n");}*/
            //visited.add(currentNode.hashCode());
//			if(numStates > 100000)
//				System.out.println("long case");
            if(useVisited)
                if (visited.containsKey(currentNode.hashCode()))
                {
                    if (visited.get(currentNode.hashCode()) <= currentNode.weight()) {
                        continue;
                    }
                }
            visited.put(currentNode.hashCode(), (int) currentNode.weight());
            if(numStates == stateLimit)
                break;
            //if(qStates == stateLimit) break?
			/*if(suffixMemorizationTable!=null)
			{
				//long decodedStates = (long) currentNode.stateLogID() | ((long) currentNode.stateModelID() >> 32);
				Set<Configuration> set;
				if((set = suffixMemorizationTable.get(currentNode.hashCode())) != null)
					for(Configuration suffix : set)
					{
						potentialNode = this.createPotentialFinalNodeFrom(currentNode, suffix, finalConfiguration, traceLabels);
						this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);
					}
			}*/
            if(qStates!=stateLimit)
                if(currentNode.tracePosition!=decoder.reducedTrace().size())// && visited.size()<=stateLimit)
                {
                    int expTraceLabel = decoder.reducedTrace().get(currentNode.tracePosition);
                    for(Transition tlog : currentNode.stLog().outgoingTransitions())
                        if(tlog.eventID()==expTraceLabel)
                        {
                            //see if match is possible
                            for(Transition tmodel : currentNode.stModel().outgoingTransitions())
                                if(tlog.eventID()==tmodel.eventID())
                                {
                                    potentialNode = initializePotentialNode(currentNode, tlog, tmodel, Configuration.Operation.MATCH, finalConfiguration, false, decoder);
                                    this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);
								/*
								if(testTrace.equals(traceLabels)) {
								fw.append(potentialNode.configuration().printLastSync() + ": state: (" + potentialNode.stateLogID() + "," + potentialNode.stateModelID() + "); cost: " + potentialNode.weight() +"\n");}
								*/
                                }
                            //consider LHIDE
                            potentialNode = initializePotentialNode(currentNode, tlog, null, Configuration.Operation.LHIDE, finalConfiguration, false, decoder);
                            this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);
						/*if(testTrace.equals(traceLabels)) {
						fw.append(potentialNode.configuration().printLastSync() + ": state: (" + potentialNode.stateLogID() + "," + potentialNode.stateModelID() + "); cost: " + potentialNode.weight() +"\n");}
						*/
                            //break;
                        }
                }

            if(qStates!=stateLimit)
                for(Transition tmodel : currentNode.stModel().outgoingTransitions())
                {
                    potentialNode = initializePotentialNode(currentNode, null, tmodel, Configuration.Operation.RHIDE, finalConfiguration, false, decoder);
                    this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);
				/*if(testTrace.equals(traceLabels)) {
				fw.append(potentialNode.configuration().printLastSync() + ": state: (" + potentialNode.stateLogID() + "," + potentialNode.stateModelID() + "); cost: " + potentialNode.weight() + "\n");}
			*/}

            if(
                    currentNode.stLog().isFinal()
                            && currentNode.stModel().isFinal()
                            && currentNode.tracePosition == decoder.reducedTrace().size()
                    )
            {
                if(currentNode.weight()<actMin)
                {
                    potentialFinalNodes = new UnifiedSet<Node>();
                    actMin = currentNode.weight();
                }
                potentialFinalNodes.add(currentNode);
//				potentialFinalNodes.offer(currentNode);
                actMin = (double) potentialFinalNodes.getFirst().weight();
                //break;
            }
            if(toBeVisited.isEmpty()) break; //System.out.println("Screw you!");
                //if(actMin < toBeVisited.min().getPriority()) break;
            else if(toBeVisited.peek().weight() > actMin) break;
        }
        double end = System.currentTimeMillis();
		/*if(testTrace.equals(traceLabels)) {
		fw.append("Final " + currentNode.configuration().printAlignment() +"; cost: " + currentNode.weight() +"\n");
		fw.close();}*/
        List<List<Object>> lstNodeInstanceLst = new FastList<List<Object>>();
        List<List<StepTypes>> lstStepTypesLst = new FastList<List<StepTypes>>();
        DoubleArrayList moveLogFitness = new DoubleArrayList();
        DoubleArrayList moveModelFitness = new DoubleArrayList();
        double movesOnLog = 0;
        double moveModel = 0;
        if(!potentialFinalNodes.isEmpty())
        {
            //report results
            Node potentialFinalNode = null;
            potentialFinalNode = potentialFinalNodes.iterator().next();
            List<Object> nodeInstanceLst = new FastList<Object>();
            List<StepTypes> stepTypesLst = new FastList<StepTypes>();
            lstNodeInstanceLst.add(nodeInstanceLst);
            lstStepTypesLst.add(stepTypesLst);
            double movesMatching = 0;
            double moveInvi = 0;
            int tracePos=0;
            au.qut.apromore.psp.Synchronization tr;
            int posToReduce = 0;
            int lengthTandemRepeat, numberRepetitions;
            int posTandemRepeat, posAlignShift=0;
            for(int alignPos=0; alignPos < potentialFinalNode.configuration().sequenceSynchronizations().size(); alignPos++)
            {
                if(posToReduce<decoder.reductionStartPositions().size())
                {
                    lengthTandemRepeat = decoder.reductionCollapsedLength().get(posToReduce) / 2;
                    if(tracePos==decoder.reductionStartPositions().get(posToReduce)-1)
                    {
                        tr = potentialFinalNode.configuration().sequenceSynchronizations().get(alignPos);
                        while(tr.eventLog()!=decoder.reducedTrace().get(tracePos))
                        {
                            nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                            if(tr.eventModel()==modelAutomaton.skipEvent())
                            {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                moveInvi++;
                            }
                            else
                            {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                moveModel++;
                            }
                            alignPos++;
                            tr = potentialFinalNode.configuration().sequenceSynchronizations().get(alignPos);
                        }

                        numberRepetitions = decoder.reductionOriginalLength().get(posToReduce) / lengthTandemRepeat-1;
                        for(int itRepetitions=0; itRepetitions<numberRepetitions;itRepetitions++)
                        {
                            posTandemRepeat=0;
                            posAlignShift=0;
                            while(posTandemRepeat <= lengthTandemRepeat)
                            {
                                if(alignPos+posAlignShift==potentialFinalNode.configuration().sequenceSynchronizations().size()) break;
                                tr = potentialFinalNode.configuration().sequenceSynchronizations().get(alignPos+posAlignShift);
                                if(tr.operation() == Configuration.Operation.MATCH)
                                {

                                    posTandemRepeat++;
                                    if(posTandemRepeat==lengthTandemRepeat+1) break;
                                    nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                                    movesMatching++;
                                }
                                else if(tr.operation() == Configuration.Operation.LHIDE)
                                {
                                    posTandemRepeat++;
                                    if(posTandemRepeat==lengthTandemRepeat+1) break;
                                    nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                                    movesOnLog++;
                                }
                                else
                                {
                                    nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                                    if(tr.eventModel()==modelAutomaton.skipEvent())
                                    {
                                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                        moveInvi++;
                                    }
                                    else
                                    {
                                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                        moveModel++;
                                    }
                                }
                                posAlignShift++;
                            }
                        }
                        tracePos+=lengthTandemRepeat;
                        posToReduce++;
                        alignPos+=posAlignShift-1;
                    }
                    else
                    {
                        tr = potentialFinalNode.configuration().sequenceSynchronizations().get(alignPos);
                        if(tr.operation() == Configuration.Operation.MATCH)
                        {

                            nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                            movesMatching++;
                            tracePos++;
                        }
                        else if(tr.operation() == Configuration.Operation.LHIDE)
                        {
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                            movesOnLog++;
                            tracePos++;
                        }
                        else
                        {
                            nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                            if(tr.eventModel()==modelAutomaton.skipEvent())
                            {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                moveInvi++;
                            }
                            else
                            {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                moveModel++;
                            }
                        }
                    }
                }
                else
                {
                    tr = potentialFinalNode.configuration().sequenceSynchronizations().get(alignPos);
                    if(tr.operation() == Configuration.Operation.MATCH)
                    {

                        nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                        movesMatching++;
                        tracePos++;
                    }
                    else if(tr.operation() == Configuration.Operation.LHIDE)
                    {
                        nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                        movesOnLog++;
                        tracePos++;
                    }
                    else
                    {
                        nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                        if(tr.eventModel()==modelAutomaton.skipEvent())
                        {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                            moveInvi++;
                        }
                        else
                        {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                            moveModel++;
                        }
                    }
                }

            }
            moveModelFitness.add(1-moveModel / (moveModel + movesMatching));
            moveLogFitness.add(1-movesOnLog / (movesOnLog + movesMatching + moveInvi));
            //this.insertPartiallySynchronizedPathIntoPSP(finalConfiguration, decoder, potentialFinalNode);
        }
        AllSyncReplayResult result = new AllSyncReplayResult(lstNodeInstanceLst, lstStepTypesLst, -1, !potentialFinalNodes.isEmpty());
        result.getTraceIndex().remove(-1);
        Integer[] relevantTraces = ArrayUtils.toObject(logAutomaton.caseTracesMapping.get(decoder.trace()).toArray());
        result.getTraceIndex().addAll(Arrays.<Integer>asList( relevantTraces));
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) result.getStepTypesLst().size());
        result.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST, (double) movesOnLog+moveModel);
        result.addInfo(PNMatchInstancesRepResult.NUMSTATES, (double) numStates);
        result.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE, (double) numStates + toBeVisited.size());
        result.addInfo(PNMatchInstancesRepResult.ORIGTRACELENGTH, (double) decoder.trace().size());
        result.addInfo(PNMatchInstancesRepResult.TIME, (double) (end - start));
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) lstNodeInstanceLst.size());
        result.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, (double) 1-result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) / (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) + modelAutomaton.minNumberOfModelMoves()));
        if(!moveLogFitness.isEmpty())
            result.addInfo(PNRepResult.MOVELOGFITNESS, moveLogFitness.average());
        if(!moveModelFitness.isEmpty())
            result.addInfo(PNRepResult.MOVEMODELFITNESS, moveModelFitness.average());
        this.resOneOptimal().add(result);
        IntArrayList traces = new IntArrayList();
        traces.addAll(logAutomaton.caseTracesMapping.get(decoder.trace()).toArray());
        this.caseReplayResultMapping().put(traces, result);
        this.traceAlignmentsMapping.put(decoder.trace(), result);
        useVisited = true;
        //System.out.println(result.getInfo());
        //System.out.println(decoder.trace());
    }

    private ReducedResult calculateReducedAlignmentFor(IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder, int stateLimit)
    {
        double start = System.currentTimeMillis();
        PriorityQueue<Node> toBeVisited = new PriorityQueue<>(new NodeComparator());
        Node currentNode = psp.sourceNode();
        UnifiedSet<Node> potentialFinalNodes = new UnifiedSet<Node>();
        int minModelMoves = modelAutomaton.minNumberOfModelMoves();
        //if(minModelMoves==0) minModelMoves=Integer.MAX_VALUE;
        double actMin = (double) (decoder.trace().size() + minModelMoves);
        Node potentialNode;
        //int sizeMoveOnLog;
        double numStates = 1;
        qStates = 1;
        visited = new IntIntHashMap();
		/*Set<Node> prefixMemoization =  this.getPrefixMemoization(traceLabels);
		for(Node node : prefixMemoization)
		{
			potentialNode = this.cloneNodeForConfiguration(node, finalConfiguration, traceLabels);
			this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);
		}*/
        this.offerPotentialNodeWithPruning(currentNode, actMin, toBeVisited);

        while(true)
        {
            /*if(toBeVisited.isEmpty())
            {
                System.out.println("Problem");
            }*/
            currentNode = toBeVisited.poll();
            /*if(currentNode==null && useVisited)
            {
                useVisited=false;
                return calculateReducedAlignmentFor(finalConfiguration, decoder, stateLimit);
            }*/
            /*if(currentNode.weight()==actMin)
            {

            }*/
            numStates++;
            if(useVisited)
                if (visited.containsKey(currentNode.hashCode()))
                {
                    if (visited.get(currentNode.hashCode()) <= currentNode.weight()) {
                        continue;
                    }
                }
            visited.put(currentNode.hashCode(), (int) currentNode.weight());
            if(numStates == stateLimit)
                break;
            if(qStates!=stateLimit)
                if(currentNode.tracePosition!=decoder.reducedTrace().size())// && visited.size()<=stateLimit)
                {
                    int expTraceLabel = decoder.reducedTrace().get(currentNode.tracePosition);
                    for(Transition tlog : currentNode.stLog().outgoingTransitions())
                        if(tlog.eventID()==expTraceLabel)
                        {
                            //see if match is possible
                            for(Transition tmodel : currentNode.stModel().outgoingTransitions())
                                if(tlog.eventID()==tmodel.eventID())
                                {
                                    potentialNode = initializePotentialNode(currentNode, tlog, tmodel, Configuration.Operation.MATCH, finalConfiguration, false, decoder);
                                    this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);

                                }
                            //consider LHIDE
                            potentialNode = initializePotentialNode(currentNode, tlog, null, Configuration.Operation.LHIDE, finalConfiguration, false, decoder);
                            this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);
                        }
                }

            if(qStates!=stateLimit)
                for(Transition tmodel : currentNode.stModel().outgoingTransitions())
                {
                    potentialNode = initializePotentialNode(currentNode, null, tmodel, Configuration.Operation.RHIDE, finalConfiguration, false, decoder);
                    this.offerPotentialNodeWithPruning(potentialNode, actMin, toBeVisited);
				}

            if(
                    currentNode.stLog().isFinal()
                            && currentNode.stModel().isFinal()
                            && currentNode.tracePosition==decoder.reducedTrace().size()
                    )
            {
                if(currentNode.weight()<actMin)
                {
                    potentialFinalNodes = new UnifiedSet<Node>();
                    actMin = currentNode.weight();
                }
                potentialFinalNodes.add(currentNode);
//				potentialFinalNodes.offer(currentNode);
                actMin = (double) potentialFinalNodes.getFirst().weight();
                break;
            }
            if(toBeVisited.isEmpty()) break; //System.out.println("Screw you!");
                //if(actMin < toBeVisited.min().getPriority()) break;
            else if(toBeVisited.peek().weight() > actMin) break;
        }
        double end = System.currentTimeMillis();
        useVisited = true;
        if(potentialFinalNodes.isEmpty())
        {
            //System.out.println("Problem");
        }
        return new ReducedResult(potentialFinalNodes.getFirst(),numStates,numStates+toBeVisited.size(),end-start);
    }

    /*private void extendReducedAlignment(IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder, ReducedResult res)
    {
        Node finalNode = res.getFinalNode();
        List<List<Object>> lstNodeInstanceLst = new FastList<List<Object>>();
        List<List<StepTypes>> lstStepTypesLst = new FastList<List<StepTypes>>();
        DoubleArrayList moveLogFitness = new DoubleArrayList();
        DoubleArrayList moveModelFitness = new DoubleArrayList();
        double movesOnLog = 0;
        double moveModel = 0;
        List<Object> nodeInstanceLst = new FastList<Object>();
        List<StepTypes> stepTypesLst = new FastList<StepTypes>();
        lstNodeInstanceLst.add(nodeInstanceLst);
        lstStepTypesLst.add(stepTypesLst);
        double movesMatching = 0;
        double moveInvi = 0;
        int tracePos=0;
        au.qut.apromore.psp.Synchronization tr;
        int posToReduce = 0;
        int lengthTandemRepeat, reductionCollapsedLength, numberRepetitions;
        int posTandemRepeat, posAlignShift=0;
        for(int alignPos=0; alignPos < finalNode.configuration().sequenceSynchronizations().size(); alignPos++)
        {
            if(posToReduce<decoder.reductionStartPositions().size())
            {
                reductionCollapsedLength = decoder.reductionCollapsedLength().get(posToReduce);
                lengthTandemRepeat =  reductionCollapsedLength / 2;
                if(tracePos==decoder.reductionStartPositions().get(posToReduce)-1) {
                    tr = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    while (tr.eventLog() != decoder.reducedTrace().get(tracePos)) {
                        nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                        if (tr.eventModel() == modelAutomaton.skipEvent()) {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                            moveInvi++;
                        } else {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                            moveModel++;
                        }
                        alignPos++;
                        tr = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    }
                    numberRepetitions = decoder.reductionOriginalLength().get(posToReduce) / lengthTandemRepeat-1;
                    for (int itRepetitions = 0; itRepetitions < numberRepetitions; itRepetitions++) {
                        posTandemRepeat = 0;
                        posAlignShift = 0;
                        while (posTandemRepeat <= lengthTandemRepeat) {
                            if (alignPos + posAlignShift == finalNode.configuration().sequenceSynchronizations().size())
                                break;
                            tr = finalNode.configuration().sequenceSynchronizations().get(alignPos + posAlignShift);
                            if (tr.operation() == Configuration.Operation.MATCH) {

                                posTandemRepeat++;
                                if (posTandemRepeat == lengthTandemRepeat + 1) break;
                                nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                                movesMatching++;
                            } else if (tr.operation() == Configuration.Operation.LHIDE) {
                                posTandemRepeat++;
                                if (posTandemRepeat == lengthTandemRepeat + 1) break;
                                nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                                movesOnLog++;
                            } else {
                                nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                                if (tr.eventModel() == modelAutomaton.skipEvent()) {
                                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                    moveInvi++;
                                } else {
                                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                    moveModel++;
                                }
                            }
                            posAlignShift++;
                        }
                    }
                    tracePos += lengthTandemRepeat;
                    posToReduce++;
                    alignPos += posAlignShift - 1;
                }
                else
                {
                    tr = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    if(tr.operation() == Configuration.Operation.MATCH)
                    {
                        nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                        movesMatching++;
                        tracePos++;
                    }
                    else if(tr.operation() == Configuration.Operation.LHIDE)
                    {
                        nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                        movesOnLog++;
                        tracePos++;
                    }
                    else
                    {
                        nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                        if(tr.eventModel()==modelAutomaton.skipEvent())
                        {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                            moveInvi++;
                        }
                        else
                        {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                            moveModel++;
                        }
                    }
                }
            }
            else
            {
                tr = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                if(tr.operation() == Configuration.Operation.MATCH)
                {
                    nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                    movesMatching++;
                    tracePos++;
                }
                else if(tr.operation() == Configuration.Operation.LHIDE)
                {
                    nodeInstanceLst.add(logAutomaton.eventLabels().get(tr.eventLog()));
                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                    movesOnLog++;
                    tracePos++;
                }
                else
                {
                    nodeInstanceLst.add(modelAutomaton.eventLabels().get(tr.eventModel()));
                    if(tr.eventModel()==modelAutomaton.skipEvent())
                    {
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                        moveInvi++;
                    }
                    else
                    {
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                        moveModel++;
                    }
                }
            }
        }
        moveModelFitness.add(1-moveModel / (moveModel + movesMatching));
        moveLogFitness.add(1-movesOnLog / (movesOnLog + movesMatching + moveInvi));
        this.insertPartiallySynchronizedPathIntoPSP(finalConfiguration, decoder, finalNode);

        AllSyncReplayResult result = new AllSyncReplayResult(lstNodeInstanceLst, lstStepTypesLst, -1, finalNode!=null);
        result.getTraceIndex().remove(-1);
        Integer[] relevantTraces = ArrayUtils.toObject(logAutomaton.caseTracesMapping.get(decoder.trace()).toArray());
        result.getTraceIndex().addAll(Arrays.<Integer>asList( relevantTraces));
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) result.getStepTypesLst().size());
        result.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST,  movesOnLog+moveModel);
        result.addInfo(PNMatchInstancesRepResult.NUMSTATES, res.getNumStates());
        result.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE,res.getNumQueuedStates());
        result.addInfo(PNMatchInstancesRepResult.ORIGTRACELENGTH, (double) decoder.trace().size());
        result.addInfo(PNMatchInstancesRepResult.TIME, (double) res.getTime());
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) lstNodeInstanceLst.size());
        result.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, (double) 1-result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) / (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) + modelAutomaton.minNumberOfModelMoves()));
        if(!moveLogFitness.isEmpty())
            result.addInfo(PNRepResult.MOVELOGFITNESS, moveLogFitness.average());
        if(!moveModelFitness.isEmpty())
            result.addInfo(PNRepResult.MOVEMODELFITNESS, moveModelFitness.average());
        this.resOneOptimal().add(result);
        IntArrayList traces = new IntArrayList();
        traces.addAll(logAutomaton.caseTracesMapping.get(decoder.trace()).toArray());
        this.caseReplayResultMapping().put(traces, result);
        this.traceAlignmentsMapping.put(decoder, result);
    }*/

    /*private void extendReducedAlignment(IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder, ReducedResult res)
    {
        Node finalNode = res.getFinalNode();
        List<List<Object>> lstNodeInstanceLst = new FastList<List<Object>>();
        List<List<StepTypes>> lstStepTypesLst = new FastList<List<StepTypes>>();
        DoubleArrayList moveLogFitness = new DoubleArrayList();
        DoubleArrayList moveModelFitness = new DoubleArrayList();
        double movesOnLog = 0, lhideToExtend, lhideSecondPair;
        double moveModel = 0, rhideToExtend, rhideSecondPair;
        List<Object> nodeInstanceLst = new FastList<Object>(), lstToExtend, lstSecondPair;
        List<StepTypes> stepTypesLst = new FastList<StepTypes>(), lstToExtendStepTypes, lstSecondPairStepTypes;
        lstNodeInstanceLst.add(nodeInstanceLst);
        lstStepTypesLst.add(stepTypesLst);
        double movesMatching = 0, matchingToExtend, matchingSecondPair;
        double moveInvi = 0;
        int tracePos=0;
        au.qut.apromore.psp.Synchronization sync, tr2;
        int posToReduce = 0, posToExtend;
        int lengthTandemRepeat, reductionCollapsedLength, numberRepetitions;
        int posTandemRepeat, posAlignShift=0;
        for(int alignPos=0; alignPos < finalNode.configuration().sequenceSynchronizations().size(); alignPos++)
        {
            if(posToReduce<decoder.reductionStartPositions().size())
            {
                reductionCollapsedLength = decoder.reductionCollapsedLength().get(posToReduce);
                lengthTandemRepeat =  reductionCollapsedLength / 2;
                if(tracePos==decoder.reductionStartPositions().get(posToReduce)-1)
                {
                    sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    while (sync.eventLog() != decoder.reducedTrace().get(tracePos))
                    {
                        nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                        if (sync.eventModel() == modelAutomaton.skipEvent()) {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                            moveInvi++;
                        } else {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                            moveModel++;
                        }
                        alignPos++;
                        sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    }
                    numberRepetitions = decoder.reductionOriginalLength().get(posToReduce) / lengthTandemRepeat-2;
                    if(numberRepetitions==0)
                    {
                        sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                        if(sync.operation() == Configuration.Operation.MATCH)
                        {
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                            movesMatching++;
                            tracePos++;
                        }
                        else if(sync.operation() == Configuration.Operation.LHIDE)
                        {
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                            movesOnLog++;
                            tracePos++;
                        }
                        else
                        {
                            nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                            if(sync.eventModel()==modelAutomaton.skipEvent())
                            {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                moveInvi++;
                            }
                            else
                            {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                moveModel++;
                            }
                        }
                        posToReduce++;
                        continue;
                    }
                    lstToExtend = new FastList<>();
                    lstToExtendStepTypes = new FastList<>();
                    posTandemRepeat = 0;
                    posAlignShift = 0;
                    lhideToExtend=0; rhideToExtend=0; matchingToExtend=0;
                    while (posTandemRepeat <= lengthTandemRepeat) {
                        if (alignPos + posAlignShift == finalNode.configuration().sequenceSynchronizations().size())
                            break;
                        sync = finalNode.configuration().sequenceSynchronizations().get(alignPos + posAlignShift);
                        if (sync.operation() == Configuration.Operation.MATCH) {
                            posTandemRepeat++;
                            if (posTandemRepeat == lengthTandemRepeat + 1) break;
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                            movesMatching++;
                            lstToExtend.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            lstToExtendStepTypes.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                            matchingToExtend++;
                        } else if (sync.operation() == Configuration.Operation.LHIDE) {
                            posTandemRepeat++;
                            if (posTandemRepeat == lengthTandemRepeat + 1) break;
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                            movesOnLog++;
                            lstToExtend.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            lstToExtendStepTypes.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                            lhideToExtend++;
                        } else {
                            nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                            lstToExtend.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                            if (sync.eventModel() == modelAutomaton.skipEvent()) {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                lstToExtendStepTypes.add(StepTypes.MINVI);
                                moveInvi++;
                            } else {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                lstToExtendStepTypes.add(StepTypes.MREAL);
                                moveModel++;
                                rhideToExtend++;
                            }
                        }
                        posAlignShift++;
                    }
                    alignPos+=posAlignShift;
                    posAlignShift=0;
                    posToExtend=0;
                    posTandemRepeat=0;
                    StepTypes curStep = lstToExtendStepTypes.get(posToExtend);
                    lstSecondPair = new FastList<>();
                    lstSecondPairStepTypes = new FastList<>();
                    matchingSecondPair=0; lhideSecondPair =0; rhideSecondPair=0;
                    boolean changesAllowed = lhideToExtend!=lengthTandemRepeat;
                    boolean matchADDED = false, isRepeated=false;
                    while(posTandemRepeat<lengthTandemRepeat)
                    {
                        if (alignPos + posAlignShift == finalNode.configuration().sequenceSynchronizations().size())
                            break;

                        sync=finalNode.configuration().sequenceSynchronizations().get(alignPos + posAlignShift);
                        if(sync.operation()==Configuration.Operation.RHIDE)
                        {
                            rhideSecondPair++;
                            lstSecondPair.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                            lstSecondPairStepTypes.add(StepTypes.MREAL);
                        }
                        else if(sync.operation()==Configuration.Operation.MATCH)
                        {
                            *//*if(changesAllowed && curStep==StepTypes.L && posTandemRepeat<lengthTandemRepeat-1)
                            {
                                lstToExtendStepTypes.set(posToExtend,StepTypes.LMGOOD);
                                lhideToExtend--;
                                matchingToExtend++;
                                matchADDED=true;
                            }*//*
                            if(curStep==StepTypes.LMGOOD) isRepeated=true;
                            do
                            {
                                if(posToExtend<lstToExtendStepTypes.size()-1) {
                                    curStep = lstToExtendStepTypes.get(++posToExtend);
                                }
                                else
                                {
                                    break;
                                }
                            }
                            while(curStep==StepTypes.MREAL);
                            matchingSecondPair++;
                            lstSecondPair.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            lstSecondPairStepTypes.add(StepTypes.LMGOOD);
                            posTandemRepeat++;
                        }
                        else
                        {
                            //if(changesAllowed && (posToExtend==0||(posToExtend==lengthTandemRepeat-1 && matchADDED)) && curStep==StepTypes.LMGOOD)
                            if(curStep==StepTypes.LMGOOD)
                            {
                                lstToExtendStepTypes.set(posToExtend, StepTypes.L);
                                lhideToExtend++;
                                matchingToExtend--;
                            }
                            do
                            {
                                if(posToExtend<lstToExtendStepTypes.size()-1) {
                                    curStep = lstToExtendStepTypes.get(++posToExtend);
                                } else break;
                            }
                            while(curStep==StepTypes.MREAL);
                            lhideSecondPair++;
                            lstSecondPair.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            lstSecondPairStepTypes.add(StepTypes.L);
                            posTandemRepeat++;
                        }
                        posAlignShift++;
                    }
                    if(!isRepeated)
                    {
                        for(int pos=0; pos < lstToExtendStepTypes.size(); pos++)
                        {
                            if(lstToExtendStepTypes.get(pos).equals(StepTypes.MREAL))
                            {
                                lstToExtend.remove(pos);
                                lstToExtendStepTypes.remove(pos);
                                rhideToExtend--;
                                pos--;
                            }
                        }
                    }
                    for(int itRepetitions = 0; itRepetitions < numberRepetitions; itRepetitions++)
                    {
                        nodeInstanceLst.addAll(lstToExtend);
                        stepTypesLst.addAll(lstToExtendStepTypes);
                        movesMatching+=matchingToExtend;
                        movesOnLog+=lhideToExtend;
                        moveModel+=rhideToExtend;
                    }
                    nodeInstanceLst.addAll(lstSecondPair);
                    stepTypesLst.addAll(lstSecondPairStepTypes);
                    movesMatching+=matchingSecondPair;
                    movesOnLog+=lhideSecondPair;
                    moveModel+=rhideSecondPair;
                    alignPos+=posAlignShift-1;
                    tracePos+=lengthTandemRepeat*2;
                    posToReduce++;

                    *//*for (int itRepetitions = 0; itRepetitions < numberRepetitions; itRepetitions++) {
                        posTandemRepeat = 0;
                        posAlignShift = 0;
                        while (posTandemRepeat <= lengthTandemRepeat) {
                            if (alignPos + posAlignShift == finalNode.configuration().sequenceSynchronizations().size())
                                break;
                            sync = finalNode.configuration().sequenceSynchronizations().get(alignPos + posAlignShift);
                            if (sync.operation() == Configuration.Operation.MATCH) {

                                posTandemRepeat++;
                                if (posTandemRepeat == lengthTandemRepeat + 1) break;
                                nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                                movesMatching++;
                            } else if (sync.operation() == Configuration.Operation.LHIDE) {
                                posTandemRepeat++;
                                if (posTandemRepeat == lengthTandemRepeat + 1) break;
                                nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                                movesOnLog++;
                            } else {
                                nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                                if (sync.eventModel() == modelAutomaton.skipEvent()) {
                                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                    moveInvi++;
                                } else {
                                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                    moveModel++;
                                }
                            }
                            posAlignShift++;
                        }
                    }
                    tracePos += lengthTandemRepeat;
                    posToReduce++;
                    alignPos += posAlignShift - 1;*//*
                }
                else
                {
                    sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    if(sync.operation() == Configuration.Operation.MATCH)
                    {
                        nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                        movesMatching++;
                        tracePos++;
                    }
                    else if(sync.operation() == Configuration.Operation.LHIDE)
                    {
                        nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                        movesOnLog++;
                        tracePos++;
                    }
                    else
                    {
                        nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                        if(sync.eventModel()==modelAutomaton.skipEvent())
                        {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                            moveInvi++;
                        }
                        else
                        {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                            moveModel++;
                        }
                    }
                }
            }
            else
            {
                sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                if(sync.operation() == Configuration.Operation.MATCH)
                {
                    nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                    movesMatching++;
                    tracePos++;
                }
                else if(sync.operation() == Configuration.Operation.LHIDE)
                {
                    nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                    movesOnLog++;
                    tracePos++;
                }
                else
                {
                    nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                    if(sync.eventModel()==modelAutomaton.skipEvent())
                    {
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                        moveInvi++;
                    }
                    else
                    {
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                        moveModel++;
                    }
                }
            }
        }
        moveModelFitness.add(1-moveModel / (moveModel + movesMatching));
        moveLogFitness.add(1-movesOnLog / (movesOnLog + movesMatching + moveInvi));
        //this.insertPartiallySynchronizedPathIntoPSP(finalConfiguration, decoder, finalNode);

        *//*IntHashSet toBeVisited = new IntHashSet();
        IntHashSet next;
        toBeVisited.add(this.modelAutomaton.sourceID());
        boolean isReliable = true;
        //if(res.getNodeInstanceLst().get(0).size()==1) {
        //	if (((String) res.getNodeInstanceLst().get(0).get(0)).equals("INS_DIPLOMI_UNIV")) {
        //		System.out.print("");
        //	}
        //}
        for(int pos=0; pos < nodeInstanceLst.size(); pos++)
        {
            if(toBeVisited.isEmpty())
            {
                isReliable=false;
                break;
            }
            if(stepTypesLst.get(pos) == StepTypes.L) continue;
            int curEventID = this.modelAutomaton.inverseEventLabels().get(nodeInstanceLst.get(pos));
            next = new IntHashSet();
            for(int curNode : toBeVisited.toArray())
            {
                for(Transition tr1 : this.modelAutomaton.states().get(curNode).outgoingTransitions())
                {
                    if(tr1.eventID()==curEventID) next.add(tr1.target().id());
                }
            }
            toBeVisited = next;
        }*//*

        AllSyncReplayResult result = new AllSyncReplayResult(lstNodeInstanceLst, lstStepTypesLst, -1, finalNode!=null);
        result.getTraceIndex().remove(-1);
        Integer[] relevantTraces = ArrayUtils.toObject(logAutomaton.caseTracesMapping.get(decoder.trace()).toArray());
        result.getTraceIndex().addAll(Arrays.<Integer>asList( relevantTraces));
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) result.getStepTypesLst().size());
        result.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST,  movesOnLog+moveModel);
        result.addInfo(PNMatchInstancesRepResult.NUMSTATES, res.getNumStates());
        result.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE,res.getNumQueuedStates());
        result.addInfo(PNMatchInstancesRepResult.ORIGTRACELENGTH, (double) decoder.trace().size());
        result.addInfo(PNMatchInstancesRepResult.TIME, (double) res.getTime());
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) lstNodeInstanceLst.size());
        result.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, (double) 1-result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) / (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) + modelAutomaton.minNumberOfModelMoves()));
        if(!moveLogFitness.isEmpty())
            result.addInfo(PNRepResult.MOVELOGFITNESS, moveLogFitness.average());
        if(!moveModelFitness.isEmpty())
            result.addInfo(PNRepResult.MOVEMODELFITNESS, moveModelFitness.average());
        this.resOneOptimal().add(result);
        IntArrayList traces = new IntArrayList();
        traces.addAll(logAutomaton.caseTracesMapping.get(decoder.trace()).toArray());
        this.caseReplayResultMapping().put(traces, result);
        this.traceAlignmentsMapping.put(decoder.trace(), result);
    }*/

    private void extendReducedAlignment(IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder, ReducedResult res)
    {
        Node finalNode = res.getFinalNode();
        List<List<Object>> lstNodeInstanceLst = new FastList<List<Object>>();
        List<List<StepTypes>> lstStepTypesLst = new FastList<List<StepTypes>>();
        DoubleArrayList moveLogFitness = new DoubleArrayList();
        DoubleArrayList moveModelFitness = new DoubleArrayList();
        double movesOnLog = 0, lhideToExtend, lhideSecondPair;
        double moveModel = 0, rhideToExtend, rhideSecondPair;
        List<Object> nodeInstanceLst = new FastList<Object>(), lstFirstCopy, lstFirstCopyStepTypes, lstToExtend, lstSecondPair;
        List<StepTypes> stepTypesLst = new FastList<StepTypes>(), lstToExtendStepTypes, lstSecondPairStepTypes;
        lstNodeInstanceLst.add(nodeInstanceLst);
        lstStepTypesLst.add(stepTypesLst);
        double movesMatching = 0, matchingToExtend, matchingSecondPair;
        double moveInvi = 0;
        int tracePos=0;
        au.qut.apromore.psp.Synchronization sync, tr2;
        int posToReduce = 0, posToExtend;
        int lengthTandemRepeat, reductionCollapsedLength, numberRepetitions;
        int posTandemRepeat, posAlignShift=0;
        for(int alignPos=0; alignPos < finalNode.configuration().sequenceSynchronizations().size(); alignPos++)
        {
            if(posToReduce<decoder.reductionStartPositions().size())
            {
                reductionCollapsedLength = decoder.reductionCollapsedLength().get(posToReduce);
                lengthTandemRepeat =  reductionCollapsedLength / 2;
                if(tracePos==decoder.reductionStartPositions().get(posToReduce)-1)
                {
                    sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    while (sync.eventLog() != decoder.reducedTrace().get(tracePos))
                    {
                        nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                        if (sync.eventModel() == modelAutomaton.skipEvent()) {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                            moveInvi++;
                        } else {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                            moveModel++;
                        }
                        alignPos++;
                        sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    }
                    numberRepetitions = decoder.reductionOriginalLength().get(posToReduce) / lengthTandemRepeat-2;
                    if(numberRepetitions==0)
                    {
                        sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                        if(sync.operation() == Configuration.Operation.MATCH)
                        {
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                            movesMatching++;
                            tracePos++;
                        }
                        else if(sync.operation() == Configuration.Operation.LHIDE)
                        {
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                            movesOnLog++;
                            tracePos++;
                        }
                        else
                        {
                            nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                            if(sync.eventModel()==modelAutomaton.skipEvent())
                            {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                moveInvi++;
                            }
                            else
                            {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                moveModel++;
                            }
                        }
                        posToReduce++;
                        continue;
                    }
                    lstToExtend = new FastList<>();
                    lstToExtendStepTypes = new FastList<>();
                    posTandemRepeat = 0;
                    posAlignShift = 0;
                    lhideToExtend=0; rhideToExtend=0; matchingToExtend=0;
                    while (posTandemRepeat <= lengthTandemRepeat) {
                        if (alignPos + posAlignShift == finalNode.configuration().sequenceSynchronizations().size())
                            break;
                        sync = finalNode.configuration().sequenceSynchronizations().get(alignPos + posAlignShift);
                        if (sync.operation() == Configuration.Operation.MATCH) {
                            posTandemRepeat++;
                            if (posTandemRepeat == lengthTandemRepeat + 1) break;
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                            movesMatching++;
                            lstToExtend.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            lstToExtendStepTypes.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                            matchingToExtend++;
                        } else if (sync.operation() == Configuration.Operation.LHIDE) {
                            posTandemRepeat++;
                            if (posTandemRepeat == lengthTandemRepeat + 1) break;
                            nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                            movesOnLog++;
                            lstToExtend.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            lstToExtendStepTypes.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                            lhideToExtend++;
                        } else {
                            nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                            lstToExtend.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                            if (sync.eventModel() == modelAutomaton.skipEvent()) {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                                lstToExtendStepTypes.add(StepTypes.MINVI);
                                moveInvi++;
                            } else {
                                stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                                lstToExtendStepTypes.add(StepTypes.MREAL);
                                moveModel++;
                                rhideToExtend++;
                            }
                        }
                        posAlignShift++;
                    }
                    alignPos+=posAlignShift;
                    posAlignShift=0;
                    posToExtend=0;
                    posTandemRepeat=0;
                    StepTypes curStep = lstToExtendStepTypes.get(posToExtend);
                    lstSecondPair = new FastList<>();
                    lstSecondPairStepTypes = new FastList<>();
                    matchingSecondPair=0; lhideSecondPair =0; rhideSecondPair=0;
                    boolean changesAllowed = lhideToExtend!=lengthTandemRepeat;
                    boolean matchADDED = false, isRepeated=false;
                    while(posTandemRepeat<lengthTandemRepeat)
                    {
                        if (alignPos + posAlignShift == finalNode.configuration().sequenceSynchronizations().size())
                            break;

                        sync=finalNode.configuration().sequenceSynchronizations().get(alignPos + posAlignShift);
                        if(sync.operation()==Configuration.Operation.RHIDE)
                        {
                            rhideSecondPair++;
                            lstSecondPair.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                            lstSecondPairStepTypes.add(StepTypes.MREAL);
                        }
                        else if(sync.operation()==Configuration.Operation.MATCH)
                        {
                            /*if(changesAllowed && curStep==StepTypes.L && posTandemRepeat<lengthTandemRepeat-1)
                            {
                                lstToExtendStepTypes.set(posToExtend,StepTypes.LMGOOD);
                                lhideToExtend--;
                                matchingToExtend++;
                                matchADDED=true;
                            }*/
                            if(curStep==StepTypes.LMGOOD && !isRepeated)
                            {
                                isRepeated=true;
                                for(int pos2=0;pos2<posToExtend;pos2++)
                                {
                                    if(lstToExtendStepTypes.get(0)==StepTypes.LMGOOD)
                                        matchingToExtend--;
                                    else if(lstToExtendStepTypes.get(0)==StepTypes.L)
                                        lhideToExtend--;
                                    else rhideToExtend--;
                                    lstToExtend.remove(0);
                                    lstToExtendStepTypes.remove(0);
                                }
                                lstToExtend.addAll(0,lstSecondPair);
                                lstToExtendStepTypes.addAll(0,lstSecondPairStepTypes);
                                matchingToExtend+=matchingSecondPair;
                                lhideToExtend+=lhideSecondPair;
                                rhideToExtend+=rhideSecondPair;
                            }
                            do
                            {
                                if(posToExtend<lstToExtendStepTypes.size()-1) {
                                    curStep = lstToExtendStepTypes.get(++posToExtend);
                                }
                                else
                                {
                                    break;
                                }
                            }
                            while(curStep==StepTypes.MREAL);
                            matchingSecondPair++;
                            lstSecondPair.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            lstSecondPairStepTypes.add(StepTypes.LMGOOD);
                            posTandemRepeat++;
                        }
                        else
                        {
                            //if(changesAllowed && (posToExtend==0||(posToExtend==lengthTandemRepeat-1 && matchADDED)) && curStep==StepTypes.LMGOOD)
                            //if(curStep==StepTypes.LMGOOD)
                            //{
                            //    lstToExtendStepTypes.set(posToExtend, StepTypes.L);
                            //    lhideToExtend++;
                            //    matchingToExtend--;
                            //}
                            do
                            {
                                if(posToExtend<lstToExtendStepTypes.size()-1) {
                                    curStep = lstToExtendStepTypes.get(++posToExtend);
                                } else break;
                            }
                            while(curStep==StepTypes.MREAL);
                            lhideSecondPair++;
                            lstSecondPair.add(logAutomaton.eventLabels().get(sync.eventLog()));
                            lstSecondPairStepTypes.add(StepTypes.L);
                            posTandemRepeat++;
                        }
                        posAlignShift++;
                    }
                    if(!isRepeated)
                    {
                        for(int pos=0; pos < lstToExtendStepTypes.size(); pos++)
                        {
                            if(lstToExtendStepTypes.get(pos).equals(StepTypes.MREAL))
                            {
                                lstToExtend.remove(pos);
                                lstToExtendStepTypes.remove(pos);
                                rhideToExtend--;
                                pos--;
                            }
                            else if(lstToExtendStepTypes.get(pos).equals(StepTypes.LMGOOD))
                            {
                                lhideToExtend++;
                                matchingToExtend--;
                                lstToExtendStepTypes.set(pos,StepTypes.L);
                            }
                        }
                    }
                    for(int itRepetitions = 0; itRepetitions < numberRepetitions; itRepetitions++)
                    {
                        nodeInstanceLst.addAll(lstToExtend);
                        stepTypesLst.addAll(lstToExtendStepTypes);
                        movesMatching+=matchingToExtend;
                        movesOnLog+=lhideToExtend;
                        moveModel+=rhideToExtend;
                    }
                    nodeInstanceLst.addAll(lstSecondPair);
                    stepTypesLst.addAll(lstSecondPairStepTypes);
                    movesMatching+=matchingSecondPair;
                    movesOnLog+=lhideSecondPair;
                    moveModel+=rhideSecondPair;
                    alignPos+=posAlignShift-1;
                    tracePos+=lengthTandemRepeat*2;
                    posToReduce++;
                }
                else
                {
                    sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                    if(sync.operation() == Configuration.Operation.MATCH)
                    {
                        nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                        movesMatching++;
                        tracePos++;
                    }
                    else if(sync.operation() == Configuration.Operation.LHIDE)
                    {
                        nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                        movesOnLog++;
                        tracePos++;
                    }
                    else
                    {
                        nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                        if(sync.eventModel()==modelAutomaton.skipEvent())
                        {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                            moveInvi++;
                        }
                        else
                        {
                            stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                            moveModel++;
                        }
                    }
                }
            }
            else
            {
                sync = finalNode.configuration().sequenceSynchronizations().get(alignPos);
                if(sync.operation() == Configuration.Operation.MATCH)
                {
                    nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.LMGOOD);
                    movesMatching++;
                    tracePos++;
                }
                else if(sync.operation() == Configuration.Operation.LHIDE)
                {
                    nodeInstanceLst.add(logAutomaton.eventLabels().get(sync.eventLog()));
                    stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.L);
                    movesOnLog++;
                    tracePos++;
                }
                else
                {
                    nodeInstanceLst.add(modelAutomaton.eventLabels().get(sync.eventModel()));
                    if(sync.eventModel()==modelAutomaton.skipEvent())
                    {
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MINVI);
                        moveInvi++;
                    }
                    else
                    {
                        stepTypesLst.add(org.processmining.plugins.petrinet.replayresult.StepTypes.MREAL);
                        moveModel++;
                    }
                }
            }
        }
        moveModelFitness.add(1-moveModel / (moveModel + movesMatching));
        moveLogFitness.add(1-movesOnLog / (movesOnLog + movesMatching + moveInvi));
        //this.insertPartiallySynchronizedPathIntoPSP(finalConfiguration, decoder, finalNode);

        /*IntHashSet toBeVisited = new IntHashSet();
        IntHashSet next;
        toBeVisited.add(this.modelAutomaton.sourceID());
        boolean isReliable = true;
        //if(res.getNodeInstanceLst().get(0).size()==1) {
        //	if (((String) res.getNodeInstanceLst().get(0).get(0)).equals("INS_DIPLOMI_UNIV")) {
        //		System.out.print("");
        //	}
        //}
        for(int pos=0; pos < nodeInstanceLst.size(); pos++)
        {
            if(toBeVisited.isEmpty())
            {
                isReliable=false;
                break;
            }
            if(stepTypesLst.get(pos) == StepTypes.L) continue;
            int curEventID = this.modelAutomaton.inverseEventLabels().get(nodeInstanceLst.get(pos));
            next = new IntHashSet();
            for(int curNode : toBeVisited.toArray())
            {
                for(Transition tr1 : this.modelAutomaton.states().get(curNode).outgoingTransitions())
                {
                    if(tr1.eventID()==curEventID) next.add(tr1.target().id());
                }
            }
            toBeVisited = next;
        }*/

        AllSyncReplayResult result = new AllSyncReplayResult(lstNodeInstanceLst, lstStepTypesLst, -1, finalNode!=null);
        result.getTraceIndex().remove(-1);
        Integer[] relevantTraces = ArrayUtils.toObject(logAutomaton.caseTracesMapping.get(decoder.trace()).toArray());
        result.getTraceIndex().addAll(Arrays.<Integer>asList( relevantTraces));
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) result.getStepTypesLst().size());
        result.addInfo(PNMatchInstancesRepResult.RAWFITNESSCOST,  movesOnLog+moveModel);
        result.addInfo(PNMatchInstancesRepResult.NUMSTATES, res.getNumStates());
        result.addInfo(PNMatchInstancesRepResult.QUEUEDSTATE,res.getNumQueuedStates());
        result.addInfo(PNMatchInstancesRepResult.ORIGTRACELENGTH, (double) decoder.trace().size());
        result.addInfo(PNMatchInstancesRepResult.TIME, (double) res.getTime());
        result.addInfo(PNMatchInstancesRepResult.NUMALIGNMENTS, (double) lstNodeInstanceLst.size());
        result.addInfo(PNMatchInstancesRepResult.TRACEFITNESS, (double) 1-result.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) / (result.getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) + modelAutomaton.minNumberOfModelMoves()));
        if(!moveLogFitness.isEmpty())
            result.addInfo(PNRepResult.MOVELOGFITNESS, moveLogFitness.average());
        if(!moveModelFitness.isEmpty())
            result.addInfo(PNRepResult.MOVEMODELFITNESS, moveModelFitness.average());
        this.resOneOptimal().add(result);
        IntArrayList traces = new IntArrayList();
        traces.addAll(logAutomaton.caseTracesMapping.get(decoder.trace()).toArray());
        this.caseReplayResultMapping().put(traces, result);
        this.traceAlignmentsMapping.put(decoder.trace(), result);
    }

    /*private void insertPartiallySynchronizedPathIntoPSP(IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder, Node finalNode)
    {
        Set<Node> commutativeFinalNodes = null;
        IntArrayList traceLabels = decoder.reducedTrace();
        if((commutativeFinalNodes = psp.commutativePaths().get(traceLabels))==null)
        {
            commutativeFinalNodes = new UnifiedSet<Node>();
            psp.commutativePaths().put(traceLabels, commutativeFinalNodes);
        }
        commutativeFinalNodes.add(finalNode);

        Node currentNode = psp.sourceNode();
        Node potentialNode = currentNode;
        for(au.qut.apromore.psp.Synchronization transition : finalNode.configuration().sequenceSynchronizations())
        {
            if(transition.operation() == Configuration.Operation.MATCH )
            {
                for(Transition tlog : currentNode.stLog().outgoingTransitions())
                {
                    for(Transition tmodel : currentNode.stModel().outgoingTransitions())
                    {
                        if(tlog.eventID() == transition.eventLog()
                                && tmodel.eventID() == transition.eventModel()
                                && tlog.target().id() == transition.targetLog()
                                && tmodel.target().id() == transition.targetModel())
                        {
                            potentialNode = initializePotentialNode(currentNode, tlog, tmodel, Configuration.Operation.MATCH, finalConfiguration, true, decoder);
                            break;
                        }
                    }
                    if(!(potentialNode.stateLogID() == currentNode.stateLogID())) break;
                }
            }
            else if (transition.operation() == Configuration.Operation.LHIDE)
            {
                for(Transition tlog : currentNode.stLog().outgoingTransitions())
                {
                    if(tlog.eventID() == transition.eventLog() && tlog.target().id() == transition.targetLog())
                    {
                        potentialNode = initializePotentialNode(currentNode, tlog, null, Configuration.Operation.LHIDE, finalConfiguration, true, decoder); //, pw);
                        break;
                    }
                }
            }
            else
            {
                for(Transition tmodel : currentNode.stModel().outgoingTransitions())
                {
                    if(tmodel.eventID() == transition.eventModel() && tmodel.target().id() == transition.targetModel())
                    {
                        potentialNode = initializePotentialNode(currentNode, null, tmodel, Configuration.Operation.RHIDE, finalConfiguration, true, decoder); //, pw);
                        break;
                    }
                }
            }
            if(!(potentialNode.stLog().isSource()) && potentialNode.stLog().outgoingTransitions().size()>1)
            {
                if(prefixMemorizationTable==null)
                    prefixMemorizationTable = new UnifiedMap<IntArrayList, Set<Node>>();
                Set<Node> relevantPrefix = null;
                if((relevantPrefix = prefixMemorizationTable.get(potentialNode.configuration().moveOnLog())) == null)
                {
                    relevantPrefix = new HashSet<Node>();
                    prefixMemorizationTable.put(potentialNode.configuration().moveOnLog(), relevantPrefix);
                }
                relevantPrefix.add(potentialNode);
            }
            if(!(potentialNode.stLog().isFinal()) && potentialNode.stLog().incomingTransitions().size()>1)
            {
                if(suffixMemorizationTable==null)
                    suffixMemorizationTable = new IntObjectHashMap<Set<Configuration>>();
                Set<Configuration> relevantConfiguration = null;
                if((relevantConfiguration = suffixMemorizationTable.get(potentialNode.hashCode()))==null)
                {
                    relevantConfiguration = new UnifiedSet<Configuration>();
                    suffixMemorizationTable.put(potentialNode.hashCode(), relevantConfiguration);
                }
                relevantConfiguration.add(finalNode.configuration().calculateSuffixFrom(potentialNode.configuration()));
            }
            currentNode = potentialNode;
        }

        finalNode.isFinal(true);
        psp.finalNodes().add(finalNode);
    }*/

    private Node initializePotentialNode(Node currentNode, Transition tlog, Transition tmodel, Configuration.Operation operation,
                                         IntIntHashMap finalConfiguration, boolean insertToPSP, DecodeTandemRepeats decoder) //, PrintWriter pw)
    {
        Configuration potentialConfiguration;
        Node potentialNode;
        if(operation == Configuration.Operation.MATCH)
        {
            potentialConfiguration = currentNode.configuration().cloneConfiguration();
            //potentialConfiguration.moveOnLog().add(tlog.eventID());
            //potentialConfiguration.moveOnModel().add(tmodel.eventID());
            //potentialConfiguration.moveMatching().add(new Couple<Integer, Integer>(tlog.eventID(), tmodel.eventID()));
            //potentialConfiguration.setMoveOnLog().addToValue(tlog.eventID(), 1);
            //potentialConfiguration.setMoveOnModel().addToValue(tmodel.eventID(), 1);
            potentialConfiguration.sequenceSynchronizations().add(new au.qut.apromore.psp.Synchronization(Configuration.Operation.MATCH, tlog.eventID(), tmodel.eventID(), tlog.target().id(), tmodel.target().id(), currentNode.hashCode()));
            //potentialConfiguration.logIDs().add(tlog.target().id());
            //potentialConfiguration.modelIDs().add(tmodel.target().id());
            if(insertToPSP)
                potentialNode = new Node(tlog.target(), tmodel.target(), potentialConfiguration, currentNode.tracePosition+1, currentNode.weight());
                        //calculateCost(potentialConfiguration, finalConfiguration, tlog.target(), tmodel.target(), decoder));
            else
            {
                potentialNode = new Node(tlog.target(), tmodel.target(), potentialConfiguration, currentNode.tracePosition + 1, currentNode.weight());
                //calculateCost(potentialConfiguration, finalConfiguration, tlog.target(), tmodel.target(), decoder));
                if(decoder.doCompression) potentialNode.getTracePenalties().putAll(currentNode.getTracePenalties());
            }
        }
        else if (operation == Configuration.Operation.LHIDE)
        {
            potentialConfiguration = currentNode.configuration().cloneConfiguration();
            //potentialConfiguration.moveOnLog().add(tlog.eventID());
            //potentialConfiguration.setMoveOnLog().addToValue(tlog.eventID(), 1);
            //potentialConfiguration.adjustSetMoveOnLog();
            potentialConfiguration.sequenceSynchronizations().add(new au.qut.apromore.psp.Synchronization(Configuration.Operation.LHIDE, tlog.eventID(), -1, tlog.target().id(), -1, currentNode.hashCode()));
            //potentialConfiguration.logIDs().add(tlog.target().id());
            if(insertToPSP) {
                potentialNode = new Node(tlog.target(), currentNode.stModel(), potentialConfiguration, currentNode.tracePosition + 1, currentNode.weight() + decoder.adjustedCost().get(currentNode.tracePosition));
                        //calculateCost(potentialConfiguration, finalConfiguration, tlog.target(), currentNode.stModel(), decoder));
            }
            else
            {
                int posFutPenalty = -1;
                boolean penaltyAlreadyPaid = false;
                double weight = currentNode.weight() + 1.0;
                if(decoder.isReduced().get(currentNode.tracePosition))
                {
                    if (decoder.isFirstTRelement().get(currentNode.tracePosition))
                    {
                        posFutPenalty = decoder.getSecondTRpositions().get(currentNode.tracePosition);
                        penaltyAlreadyPaid = true;
                        weight += decoder.adjustedCost().get(currentNode.tracePosition);
                    }
                    else if(!currentNode.getTracePenalties().get(currentNode.tracePosition))
                    {
                        weight += decoder.adjustedCost().get(currentNode.tracePosition);
                    }
                }
                potentialNode = new Node(tlog.target(), currentNode.stModel(), potentialConfiguration, currentNode.tracePosition+1, weight,posFutPenalty,penaltyAlreadyPaid);
                        //calculateCost(potentialConfiguration, finalConfiguration, tlog.target(), currentNode.stModel(), decoder));
                if(decoder.doCompression) potentialNode.getTracePenalties().putAll(currentNode.getTracePenalties());
            }
        } else
        {
            potentialConfiguration = currentNode.configuration().cloneConfiguration();
            //potentialConfiguration.moveOnModel().add(tmodel.eventID());
            //potentialConfiguration.setMoveOnModel().addToValue(tmodel.eventID(), 1);
            //potentialConfiguration.adjustSetMoveOnModel();
            potentialConfiguration.sequenceSynchronizations().add(new au.qut.apromore.psp.Synchronization(Configuration.Operation.RHIDE, -1, tmodel.eventID()));
            //potentialConfiguration.modelIDs().add(tmodel.target().id());
            if(insertToPSP)
                potentialNode = new Node(currentNode.stLog(), tmodel.target(), potentialConfiguration, currentNode.tracePosition, currentNode.weight() + decoder.adjustedRHIDECost().get(currentNode.tracePosition));
                        //calculateCost(potentialConfiguration, finalConfiguration, currentNode.stLog(), tmodel.target(), decoder));
            else {
                potentialNode = new Node(currentNode.stLog(), tmodel.target(), potentialConfiguration, currentNode.tracePosition, currentNode.weight() + decoder.adjustedRHIDECost().get(currentNode.tracePosition));
                //calculateCost(potentialConfiguration, finalConfiguration, currentNode.stLog(), tmodel.target(), decoder));
                if(decoder.doCompression) potentialNode.getTracePenalties().putAll(currentNode.getTracePenalties());
            }
        }

		/*if(insertToPSP)
		{
			Arc potentialArc;
			*//*if(psp.nodes().containsValue(potentialNode))
			{
				potentialNode = psp.nodes().get(potentialNode.hashCode());
			}
			else*//*
			psp.nodes().put(potentialNode.hashCode(), potentialNode);

			if(operation == Configuration.Operation.RHIDE)
				potentialArc = new Arc(new au.qut.apromore.psp.Synchronization(Configuration.Operation.RHIDE, -1, tmodel.eventID(), -1, tmodel.target().id(), currentNode.hashCode()), currentNode, potentialNode);
			else if(operation==Configuration.Operation.LHIDE)
				potentialArc = new Arc(new au.qut.apromore.psp.Synchronization(operation, tlog.eventID(), -1, tlog.target().id(),-1, currentNode.hashCode()), currentNode, potentialNode);
			else
				potentialArc = new Arc(new au.qut.apromore.psp.Synchronization(operation, tlog.eventID(), tmodel.eventID(), tlog.target().id(),tmodel.target().id(), currentNode.hashCode()), currentNode, potentialNode);
			if(currentNode.outgoingArcs().add(potentialArc))
				psp.arcs().add(potentialArc);
		}*/
        return potentialNode;
    }

    public Set<Node> getPrefixMemoization(IntArrayList traceLabels)
    {
        Set<Node> prefixMemo = new UnifiedSet<Node>();
        if(prefixMemorizationTable==null) return prefixMemo;
        IntArrayList prefix = new IntArrayList();
        Set<Node> memo;
        for(int i=0; i<traceLabels.size();i++)
        {
            prefix.add(traceLabels.get(i));
            if((memo = prefixMemorizationTable.get(prefix))!=null)
            {
                prefixMemo.addAll(memo);
            }
        }
        return prefixMemo;
    }

    private Node cloneNodeForConfiguration(Node source, IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder)
    {
        return new Node(source.stLog(), source.stModel(), source.configuration().cloneConfiguration(), this.calculateCost(source.configuration(), finalConfiguration, source.stLog(), source.stModel(), decoder));
    }

    private Node createPotentialFinalNodeFrom(Node currentNode, Configuration suffixConfiguration, IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder ) {
        Configuration configuration = currentNode.configuration().cloneConfiguration();
        configuration.addSuffixFrom(suffixConfiguration);
        if (configuration.setMoveOnLog().equals(finalConfiguration))
            return new Node(logAutomaton.states().get(suffixConfiguration.logIDs().getLast()), modelAutomaton.states().get(suffixConfiguration.modelIDs().getLast()), configuration,
                    this.calculateCost(configuration, finalConfiguration, logAutomaton.states().get(suffixConfiguration.logIDs().getLast()),
                            modelAutomaton.states().get(suffixConfiguration.modelIDs().getLast()), decoder));
        else {
            return new Node(logAutomaton.states().get(suffixConfiguration.logIDs().getLast()), modelAutomaton.states().get(suffixConfiguration.modelIDs().getLast()), configuration, Integer.MAX_VALUE);
        }
    }

    private double calculateCost(Configuration configuration, IntIntHashMap finalConfiguration, State stLog, State stModel, DecodeTandemRepeats decoder) //, PrintWriter pw)//, int stateLogID, int stateModelID, int finalState)
    {
        //int futureCost = futureCost(configuration, finalConfiguration, stLog, stModel, decoder);
        //if(futureCost==Integer.MAX_VALUE)
            //return Integer.MAX_VALUE;
        return currentCost(configuration, finalConfiguration, decoder);// + futureCost;
    }

    private double currentCost(Configuration configuration, IntIntHashMap finalConfiguration) //, PrintWriter pw)
    {
        double currentCost = 0;
        for(Synchronization sync : configuration.sequenceSynchronizations())
        {
            if((sync.operation()==Configuration.Operation.RHIDE || sync.operation()== Configuration.Operation.LHIDE) && sync.eventModel()!=this.modelAutomaton.skipEvent())
            {
                currentCost +=1;
                if(modelAutomaton.getParallelLabels().contains(sync.eventModel()))// || modelAutomaton.getParallelLabels().contains(sync.eventLog()))
                    currentCost += this.epsilon;
            }
        }
        return currentCost;
        //IntArrayList moveOnModelWithoutTau = new IntArrayList();
        //moveOnModelWithoutTau.addAll(configuration.moveOnModel());
        //moveOnModelWithoutTau.removeAll(modelAutomaton.skipEvent());
        //return configuration.moveOnLog().size() + moveOnModelWithoutTau.size() - 2 * configuration.moveMatching().size();// + finalConfigurationViolations.size();
    }

    private double currentCost(Configuration configuration, IntIntHashMap finalConfiguration, DecodeTandemRepeats decoder) //, PrintWriter pw)
    {
        /*IntArrayList moveOnModelWithoutTau = new IntArrayList();
        moveOnModelWithoutTau.addAll(configuration.moveOnModel());
        moveOnModelWithoutTau.removeAll(modelAutomaton.skipEvent());
        return configuration.moveOnLog().size() + moveOnModelWithoutTau.size() - 2 * configuration.moveMatching().size();// + finalConfigurationViolations.size();*/
        double currentCost = 0;
        int tracePos = 0, trPos=0;
        BooleanArrayList addTRpenalty = new BooleanArrayList();
        for(int TR = 0; TR < decoder.reductionStartPositions().size(); TR++)
        {
            addTRpenalty.add(false);
        }
        for(Synchronization sync : configuration.sequenceSynchronizations())
        {
            if(sync.operation()==Configuration.Operation.MATCH) {
                tracePos++;
            }
            else if(sync.operation()==Configuration.Operation.RHIDE) {
                currentCost += decoder.adjustedRHIDECost().get(tracePos);
                //currentCost+=1;
            }
            else
            {
                //if(decoder.reductionStartPositions().get(trPos))
                currentCost+=decoder.adjustedCost().get(tracePos);
                //currentCost+=1;
                tracePos++;
            }
        }
        return currentCost;

    }

    //TO: Store heuristics values to speed up!
    private int futureCost(Configuration configuration, IntIntHashMap finalConfigurationLog, State stLog, State stModel, IntArrayList trace, DecodeTandemRepeats decoder)
    {
        return 0;
		/*int skips = 0;
		int count_log;
		int count_model;
		IntIntHashMap finalConfigLog = this.mapDifference(finalConfigurationLog, configuration.setMoveOnLog());
		if(stLog.isFinal() && finalConfigLog.isEmpty() && stModel.isFinal())
			return 0;
		int futureSkips = Integer.MAX_VALUE;//(int) finalConfigLog.sum();
		int loopSkips =0;
		*//*if(stModel.hasLoopFuture() && trace.size()>=10)
		{
			try {
				loopSkips = this.calcLoopSkips(finalConfigLog, stModel.futureLoops());
			} catch (LpSolveException e) {
				// TODO Auto-generated catch block
				//e.printStackTrace();
			}
		}*//*
		for(IntIntHashMap optimalModelFuture : stModel.possibleFutures())
		{
			int pos = 0;
			int[] list = new int[finalConfigLog.size() + optimalModelFuture.size()];
			MutableIntSet set = finalConfigLog.keySet();
			for(int a : set.toArray()) {
				list[pos] = a;
				pos++;
			}
			for(int a : optimalModelFuture.keySet().toArray()) {
				if(!set.contains(a)) {
					list[pos] = a;
					pos++;
				}
			}
			skips=loopSkips;
			for(int i = 0; i < pos; i++)
			{
				int key = list[i];
				if(key == modelAutomaton.skipEvent()) continue;
				count_model = optimalModelFuture.get(key);
				count_log = finalConfigLog.get(key);
				if(count_model >= 200)
				{
					skips += Math.max(count_model%200-count_log, 0);
				}
				else
				{
					skips += Math.abs(count_log - count_model);
				}
			}
			*//*for(int i = 0; i < pos; i++)
			{
				int key = list[i];
				if(key == modelAutomaton.skipEvent()) continue;
				count_model = optimalModelFuture.get(key);
				count_log = finalConfigLog.get(key);
				if(count_model >= 200)
				{
					skips += Math.pow(Math.max(count_model%200-count_log, 0),2);
				}
				else
				{
					skips += Math.pow((count_log - count_model),2);
				}
			}*//*
			//skips = (int) Math.round(Math.sqrt(skips));
			futureSkips = Math.min(futureSkips, skips);
			if(futureSkips==0) break;
		}
		if(futureSkips==Integer.MAX_VALUE)
			futureSkips = 0; //(int) finalConfigLog.sum();
		return (int) futureSkips;*/
    }



    public int calcLoopSkips(IntIntHashMap conf, Set<IntIntHashMap> loops) throws LpSolveException
    {
        int pos = 0;
        for(IntIntHashMap loop : loops)
            pos+=loop.size();
        int[] list = new int[pos];
        pos=0;
        MutableIntSet set = new IntHashSet();
        for(IntIntHashMap loop : loops)
        {
            for(int a : loop.keySet().toArray()) {
                if(set.add(a)) {
                    list[pos] = a;
                    pos++;
                }
            }
        }
        int Ncol, i, j, rh1, rh2, ret = 0;

        Ncol = pos + loops.size();

        int[] colno1 = new int[Ncol];
        int[] colno2 = new int[Ncol];
        double[] row1 = new double[Ncol];
        double[] row2 = new double[Ncol];
        int col_val;
        double row_val;
        int val_key;

        if(lp==null)
        {
            lp = LpSolve.makeLp(pos*2, Ncol);
            lp.setAddRowmode(true);
            for(int key = 0; key < pos; key++)
            {
                for(i = 0; i < Ncol;i++)
                {
                    row1[i] = 0;
                    row2[i] = 0;
                    colno1[i] = 0;
                    colno2[i] = 0;
                }
                j = 0;
                val_key = list[key];
                col_val = key+1;
                row_val = -1;
                colno1[j] = col_val;
                row1[j] = row_val;
                colno2[j] = col_val;
                row2[j++] = row_val;
                i=1;
                for(IntIntHashMap loop : loops)
                {
                    col_val = pos + i++;
                    row_val = loop.get(val_key);
                    colno1[j] = col_val;
                    row1[j] = -row_val;
                    colno2[j] = col_val;
                    row2[j++] = row_val;
                }
                col_val = conf.get(val_key);
                rh1 = -col_val;
                rh2 = col_val;
                lp.addConstraintex(j, row1, colno1, LpSolve.LE, rh1);
                lp.addConstraintex(j, row2, colno2, LpSolve.LE, rh2);
            }
            lp.setAddRowmode(false);
            j = 0;
            for(i=1; i<=pos; i++)
            {
                colno1[j] = i;
                row1[j++] = 1;
            }
            for(int loop=1;loop<=loops.size();loop++)
            {
                colno1[j] = i++;
                row1[j++] = 0;
            }
            lp.setObjFnex(j, row1, colno1);

        }
        else
        {
            for(int key = 1; key <= lp.getNorigRows(); key++)
                lp.delConstraint(key);
            for(int key = 0; key < pos; key++)
            {
                for(i = 0; i < Ncol;i++)
                {
                    row1[i] = 0;
                    row2[i] = 0;
                    colno1[i] = 0;
                    colno2[i] = 0;
                }
                j = 0;
                val_key = list[key];
                col_val = key+1;
                row_val = -1;
                colno1[j] = col_val;
                row1[j] = row_val;
                colno2[j] = col_val;
                row2[j++] = row_val;
                i=1;
                for(IntIntHashMap loop : loops)
                {
                    col_val = pos + i++;
                    row_val = loop.get(val_key);
                    colno1[j] = col_val;
                    row1[j] = -row_val;
                    colno2[j] = col_val;
                    row2[j++] = row_val;
                }
                col_val = conf.get(val_key);
                rh1 = -col_val;
                rh2 = col_val;
                lp.addConstraintex(j, row1, colno1, LpSolve.LE, rh1);
                lp.addConstraintex(j, row2, colno2, LpSolve.LE, rh2);
            }
            j = 0;
            for(i=1; i<=pos; i++)
            {
                colno1[j] = i;
                row1[j++] = 1;
            }

            for(int loop=1;loop<=loops.size();loop++)
            {
                colno1[j] =i++;
                row1[j++] = 0;
            }

            lp.setObjFnex(j, row1, colno1);
        }

        if(ret == 0) {
            lp.defaultBasis();
            lp.setMinim();
            lp.setVerbose(LpSolve.IMPORTANT);
            ret = lp.solve();
        }
        ret = (int) lp.getObjective();
        return(ret);
    }

    //TODO: Implement Pruning
    private void offerPotentialNodeWithPruning(Node potentialNode, double actMin, Queue<Node> toBeVisited)
    //private void offerPotentialNodeWithPruning(Node potentialNode, int actMin, FibonacciHeap<Node> toBeVisited, Set<Node> visited)
    {
//		int pruningCost;
//		if(statePruning.containsKey((long) potentialNode.stateLogID() | ((long) potentialNode.stateModelID() << 32)))
//			pruningCost = statePruning.get((long) potentialNode.stateLogID() | ((long) potentialNode.stateModelID() << 32));
//		else
//		{
//			pruningCost = actMin;
//			statePruning.put((long) potentialNode.stateLogID() | ((long) potentialNode.stateModelID() << 32), pruningCost);
//		}
        //if(potentialNode.weight()<pruningCost && visited.add(potentialNode))
        if(visited.containsKey(potentialNode.hashCode()))
        {
            if(visited.get(potentialNode.hashCode()) <= potentialNode.weight()) return;
        }
        qStates++;
        //toBeVisited.enqueue(potentialNode, potentialNode.weight());

        toBeVisited.offer(potentialNode);
    }

    private void offerPotentialNode(Node potentialNode, double actMin, Queue<Node> toBeVisited)
    //private void offerPotentialNode(Node potentialNode, int actMin, FibonacciHeap<Node> toBeVisited, Set<Node> visited)
    {
        if(visited.contains(potentialNode.hashCode())) return;
        if(potentialNode.weight()<=actMin)
        {
            //toBeVisited.enqueue(potentialNode, potentialNode.weight());
            toBeVisited.add(potentialNode);
            qStates++;
        }
    }

    public PSP psp()
    {
        return this.psp;
    }

    public PNMatchInstancesRepResult resOneOptimal()
    {
        if(this.resOneOptimal==null)
            this.resOneOptimal = new PNMatchInstancesRepResult(new TreeSet<AllSyncReplayResult>());
        return this.resOneOptimal;
    }

    public PNMatchInstancesRepResult resAllOptimal()
    {
        if(this.resAllOptimal==null)
            this.resAllOptimal = new PNMatchInstancesRepResult(new TreeSet<AllSyncReplayResult>());
        return this.resAllOptimal;
    }

    public int futureSkips(IntIntHashMap log, IntIntHashMap model)
    {
        int futureSkips = 0;
        int count;
        for(int key : log.keySet().toArray())
            futureSkips += Math.max(log.get(key) - model.get(key), 0);
        for(int key : model.keySet().toArray())
        {
            if(key == modelAutomaton.skipEvent()) continue;
            if((count = model.get(key)) >= 200) count = 1;
            //count -= subtraction.get(key);
            futureSkips += Math.max(count - log.get(key), 0);
        }
        return futureSkips;
    }
    public int mapLogDifference(IntIntHashMap base, IntIntHashMap subtraction)
    {
//		IntIntHashMap mapDifference = new IntIntHashMap();
//		for(int key : mapDifference.keySet().toArray())
//		{
//			mapDifference.addToValue(key, -subtraction.get(key));
//			if(mapDifference.get(key)<0) mapDifference.put(key, 0);
//			if(mapDifference.get(key)==0) mapDifference.remove(key);
//		}
        int sum = 0;
        //int count;
        for(int key : base.keySet().toArray())
        {
//			count = base.get(key) - subtraction.get(key);
//			if(count>0)
//				mapDifference.put(key, count);
            sum += Math.max(base.get(key) - subtraction.get(key), 0);
        }
        //return mapDifference;
        return sum;
    }

    public IntIntHashMap mapDifference(IntIntHashMap base, IntIntHashMap subtraction)
    {
        IntIntHashMap mapDifference = new IntIntHashMap();
//		for(int key : mapDifference.keySet().toArray())
//		{
//			mapDifference.addToValue(key, -subtraction.get(key));
//			if(mapDifference.get(key)<0) mapDifference.put(key, 0);
//			if(mapDifference.get(key)==0) mapDifference.remove(key);
//		}
//		int sum = 0;
        int count;
        for(int key : base.keySet().toArray())
        {
            count = base.get(key) - subtraction.get(key);
            if(count>0)
                mapDifference.put(key, count);
//			sum += Math.abs(base.get(key) - subtraction.get(key));
        }
        return mapDifference;
//		return sum;
    }

    public IntIntHashMap mapModelDifference(IntIntHashMap base, IntIntHashMap subtraction)
    {
        IntIntHashMap mapDifference = new IntIntHashMap();
        int count;
        for(int key : base.keySet().toArray())
        {
            if((count=base.get(key))>=200) {mapDifference.put(key, 200); continue;}
            count = count - subtraction.get(key);
            if(count>0)
                mapDifference.put(key, count);
        }
        return mapDifference;
    }

    public int mapSpecialDifference(IntIntHashMap base, IntIntHashMap subtraction)
    {
//		IntIntHashMap mapDifference = new IntIntHashMap();
//		for(int key : mapDifference.keySet().toArray())
//		{
//			mapDifference.addToValue(key, -subtraction.get(key));
//			if(mapDifference.get(key)<0) mapDifference.put(key, 0);
//			if(mapDifference.get(key)==0) mapDifference.remove(key);
//		}
        int count;
        int sum = 0;
        for(int key : base.keySet().toArray())
        {
            if(key == modelAutomaton.skipEvent()) continue;
            if((count = base.get(key)) >= 200) count = 1;
            //count -= subtraction.get(key);
            sum += Math.max(count - subtraction.get(key), 0);
//			if(count > 0)
//				mapDifference.put(key, count);
        }
        //return mapDifference;
        return sum;
    }

    public Map<IntArrayList, AllSyncReplayResult> caseReplayResultMapping()
    {
        if(this.caseReplayResultMapping==null)
            this.caseReplayResultMapping = new UnifiedMap<IntArrayList, AllSyncReplayResult>();
        return this.caseReplayResultMapping;
    }

    public void printAlignmentResults(String alignmentStatisticsFile, String caseTypeAlignmentResultsFile) throws FileNotFoundException
    {
        PrintWriter pw1 = new PrintWriter(alignmentStatisticsFile);
        PrintWriter pw2 = new PrintWriter(caseTypeAlignmentResultsFile);

        pw1.println("Average Log Alignment Statistics per Case Type:");
        pw1.println(PNMatchInstancesRepResult.RAWFITNESSCOST + "," + PNMatchInstancesRepResult.ORIGTRACELENGTH + "," + PNMatchInstancesRepResult.QUEUEDSTATE + ","
                + PNMatchInstancesRepResult.NUMSTATES + "," + PNMatchInstancesRepResult.TIME + "," + PNMatchInstancesRepResult.NUMALIGNMENTS + "," + PNMatchInstancesRepResult.TRACEFITNESS);
        pw1.println(this.resAllOptimal().getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST) + ","
                + this.resAllOptimal().getInfo().get(PNMatchInstancesRepResult.ORIGTRACELENGTH) + ","
                + this.resAllOptimal().getInfo().get(PNMatchInstancesRepResult.QUEUEDSTATE) + ","
                + this.resAllOptimal().getInfo().get(PNMatchInstancesRepResult.NUMSTATES) + ","
                + this.resAllOptimal().getInfo().get(PNMatchInstancesRepResult.TIME) + ","
                + this.resAllOptimal().getInfo().get(PNMatchInstancesRepResult.NUMALIGNMENTS) + ","
                + this.resAllOptimal().getInfo().get(PNMatchInstancesRepResult.TRACEFITNESS));

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
                        +	this.logAutomaton.caseIDs.get(trace) + ","
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

    public Automaton getOriginalModelAutomaton() { return originalModelAutomaton; }

    public Automaton getModelAutomaton() { return modelAutomaton; }

    public HashMap<String, String> getIdsMapping() { return idsMapping; }

    public HashMap<String, List<String>> getArtificialGatewaysInfo(){ return artificialGatewaysInfo; }
}
