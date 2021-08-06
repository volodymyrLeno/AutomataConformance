package au.qut.apromore.importer;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

import java.util.*;
import java.util.stream.Collectors;

import au.qut.apromore.PetriNet.PetriNet;
import au.qut.apromore.automaton.Automaton;

import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Activity;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Event;
import org.apromore.processmining.models.graphbased.directed.bpmn.elements.Gateway;
import org.eclipse.collections.impl.list.mutable.FastList;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.primitive.IntIntHashMap;
import org.eclipse.collections.impl.set.mutable.UnifiedSet;
import org.eclipse.collections.impl.set.mutable.primitive.IntHashSet;

import org.processmining.framework.connections.ConnectionCannotBeObtained;
import org.processmining.models.connections.petrinets.behavioral.FinalMarkingConnection;
import org.processmining.models.connections.petrinets.behavioral.InitialMarkingConnection;
import org.processmining.models.graphbased.AttributeMap;
import org.processmining.models.graphbased.directed.petrinet.Petrinet;
import org.processmining.models.graphbased.directed.petrinet.PetrinetEdge;
import org.processmining.models.graphbased.directed.petrinet.PetrinetNode;
import org.processmining.models.graphbased.directed.petrinet.elements.Place;
import org.processmining.models.graphbased.directed.transitionsystem.ReachabilityGraph;
import org.processmining.models.graphbased.directed.transitionsystem.State;
import org.processmining.models.graphbased.directed.transitionsystem.Transition;
import org.processmining.models.semantics.petrinet.Marking;
import org.apromore.processmining.models.graphbased.directed.bpmn.BPMNDiagram;
import org.processmining.plugins.bpmn.dialogs.BpmnSelectDiagramDialog;
import org.processmining.plugins.petrinet.behavioralanalysis.TSGenerator;
import org.processmining.plugins.pnml.exporting.PnmlExportNetToPNML;
import org.processmining.plugins.pnml.importing.PnmlImportNet;

import org.apromore.processmining.plugins.bpmn.plugins.BpmnImportPlugin;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;

import com.raffaeleconforti.context.FakePluginContext;
import com.raffaeleconforti.conversion.bpmn.BPMNToPetriNetConverter;

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

public class ImportProcessModel 
{
	protected FakePluginContext context = new FakePluginContext();
	private BiMap<String, Integer> stateLabelMapping;
	public au.qut.apromore.automaton.Automaton modelAutomaton;
	public au.qut.apromore.automaton.Automaton originalModelAutomaton;
	public HashMap<String, String> idsMapping = new HashMap<>();
	public HashMap artificialGatewaysInfo = new HashMap<>();
	public BiMap<Integer, String> globalLabelMapping = HashBiMap.create();
	public BiMap<String, Integer> globalInverseLabels = HashBiMap.create();
	protected BiMap<Integer, String> eventLabelMapping;
	protected BiMap<String, Integer> inverseEventLabelMapping;
	private BiMap<Integer, au.qut.apromore.automaton.State> stateMapping;
	private BiMap<Integer, au.qut.apromore.automaton.Transition> transitionMapping;
	private IntHashSet finalStates;
	public IntHashSet parallelLabels = new IntHashSet();
	private UnifiedSet<String> pLabels = new UnifiedSet<>();
	private int iSource = 0;
	private final int skipEvent = -2;
	private final String tau = "tau";
	private final String cTau = "Tau";
	private final String invisible = "invisible";
	private final String strRegEx = "([Tt])(\\d+)";
	private final String emptyStr = "";
	private final String empty = "empty";
	public int places=0;
	public int transitions=0;
	public int arcs =0;
	public int size=0;
	public int choice=0;
	public int parallel=0;
	public int rg_nodes = 0;
	public int rg_arcs = 0;
	public int rg_size = 0;
	public int rg_size_before_tau_removal = 0;

	public au.qut.apromore.automaton.Automaton createAutomatonAlternative(String fileName) throws Exception
	{
		PetriNet pNet = ImportPetriNet.createPetriNetFromFile(fileName);
		this.places = pNet.getPlaces().size();
		this.transitions = pNet.getTransitions().size();
		return calculateReachabilityGraph(pNet);
	}

	public au.qut.apromore.automaton.Automaton calculateReachabilityGraph(PetriNet pNet)
	{
		stateMapping = HashBiMap.create();
		transitionMapping = HashBiMap.create();
		finalStates = new IntHashSet();
		IntIntHashMap stateIDMarkingMapping = new IntIntHashMap();
		Integer rkey;
		IntHashSet modelEventLabels = new IntHashSet();
		IntIntHashMap marking = pNet.getInitialMarking();
		au.qut.apromore.automaton.Transition tr;
		au.qut.apromore.automaton.State state = new au.qut.apromore.automaton.State(pNet.getMarkingLabel(marking),true,false), target;
		iSource=state.id();
		stateMapping.put(state.id(),state);
		stateIDMarkingMapping.put(PetriNet.compress(marking),state.id());
		int iEvent = globalInverseLabels.size();
		if(!globalInverseLabels.containsKey(tau))
			globalInverseLabels.put(tau,skipEvent);

		FastList<IntIntHashMap> toBeVisited = new FastList<>();
		IntHashSet visited = new IntHashSet();
		toBeVisited.add(marking);
		while(!toBeVisited.isEmpty())
		{
			marking = toBeVisited.remove(0);
			state = stateMapping.get(stateIDMarkingMapping.get(PetriNet.compress(marking)));
			visited.add(PetriNet.compress(marking));
			int[] enabledTransitions = pNet.getEnabledTransitions(marking).toArray();
			if(enabledTransitions.length==0)
			{
				state.setFinal(true);
				finalStates.add(state.id());
			}
			else for (int enabled : enabledTransitions)
			{
				au.qut.apromore.PetriNet.Transition transition = pNet.getTransitions().get(enabled);
				IntIntHashMap targetMarking = pNet.fireUnchecked(enabled,marking);
				if((target = stateMapping.get(stateIDMarkingMapping.get(PetriNet.compress(targetMarking))))==null)
				{
					target = new au.qut.apromore.automaton.State(pNet.getMarkingLabel(targetMarking),false,false);
					stateIDMarkingMapping.put(PetriNet.compress(targetMarking), target.id());
					stateMapping.put(target.id(),target);
				}

				String tLabel = transition.label();
				if(!transition.isVisible()) tLabel = tau;
				if(tLabel.contains(cTau) || tLabel.contains(tau) || tLabel.contains(invisible)
						|| tLabel.contains(empty) || tLabel.equals(emptyStr) || tLabel.matches(strRegEx))
					tLabel = tau;

				if((rkey = this.globalInverseLabels.get(tLabel)) == null)
				{
					rkey = iEvent;
					this.globalInverseLabels.put(tLabel, iEvent);
					iEvent++;
				}
				modelEventLabels.add(rkey);

				tr = new au.qut.apromore.automaton.Transition(state, target, rkey);
				if(!this.transitionMapping.containsValue(tr))
					this.transitionMapping.put(transition.id(), tr);
				state.outgoingTransitions().add(tr);
				target.incomingTransitions().add(tr);
				if(visited.add(PetriNet.compress(targetMarking)))
					toBeVisited.add(targetMarking);
			}
		}
		this.eventLabelMapping = HashBiMap.create(this.globalInverseLabels.inverse());
		Set<Integer> keySet = new UnifiedSet<Integer>();
		keySet.addAll(this.eventLabelMapping.keySet());
		for(int key : keySet)
			if(!modelEventLabels.contains(key))
				this.eventLabelMapping.remove(key);
		this.inverseEventLabelMapping = this.eventLabelMapping.inverse();
		this.rg_size_before_tau_removal = this.stateMapping.size() + this.transitionMapping.size();
		this.removeTauArcs();
		modelAutomaton = new au.qut.apromore.automaton.Automaton(this.stateMapping, this.eventLabelMapping, this.inverseEventLabelMapping, this.transitionMapping, iSource, this.finalStates, skipEvent);//, globalInverseLabels.inverse());//, ImportPetriNet.readFile());
		this.rg_nodes = modelAutomaton.numberNodes;
		this.rg_arcs = modelAutomaton.numberArcs;
		this.rg_size = modelAutomaton.totalSize;
		return modelAutomaton;
	}

	public au.qut.apromore.automaton.Automaton createAutomatonFromPNMLorBPMNFile(String fileName, BiMap<Integer, String> eventLabelMapping, BiMap<String, Integer> inverseEventLabelMapping) throws Exception
	{
		String extension = fileName.substring(fileName.length()-5);
		if(extension.equals(".pnml")) {
			return createFSMfromPNMLFile(fileName, eventLabelMapping, inverseEventLabelMapping);
		}
		else if(extension.equals(".bpmn")) {
			return createFSMfromBPMNFile(fileName, eventLabelMapping, inverseEventLabelMapping);
		}
		else throw new Exception("Wrong filetype - Only .pnml or .bpmn process models are supported");

	}

	public Object[] importPetriNetAndMarking(String fileName) throws Exception
	{
		FakePluginContext context = new FakePluginContext();
		PnmlImportNet imp = new PnmlImportNet();
		Object[] obj =  (Object[]) imp.importFile(context, fileName);
		Petrinet pnet = (Petrinet) obj[0];
		int i = pnet.getNodes().size();
		for(org.processmining.models.graphbased.directed.petrinet.elements.Transition tr : pnet.getTransitions())
		{
			if(tr.getLabel().equals(""))
			{
				tr.getAttributeMap().put(AttributeMap.LABEL, "empty_" + ++i);
			}
		}
		obj[0] = pnet;
		return obj;
	}
	
	public Object[] importPetrinetFromBPMN(String fileName) throws Exception
	{
		FakePluginContext context = new FakePluginContext();
		org.processmining.plugins.bpmn.Bpmn bpmn = (org.processmining.plugins.bpmn.Bpmn) new org.processmining.plugins.bpmn.plugins.BpmnImportPlugin().importFile(context, fileName);
		org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters parameters = new org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters();
		@SuppressWarnings("unused")
		BpmnSelectDiagramDialog dialog = new BpmnSelectDiagramDialog(bpmn.getDiagrams(), parameters);
		org.processmining.models.graphbased.directed.bpmn.BPMNDiagram newDiagram = org.processmining.models.graphbased.directed.bpmn.BPMNDiagramFactory.newBPMNDiagram("");
		Map<String, org.processmining.models.graphbased.directed.bpmn.BPMNNode> id2node = new HashMap<>();
		Map<String, org.processmining.models.graphbased.directed.bpmn.elements.Swimlane> id2lane = new HashMap<>();
		if (parameters.getDiagram() == org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters.NODIAGRAM) {
			bpmn.unmarshall(newDiagram, id2node, id2lane);
		} else {
			Collection<String> elements = parameters.getDiagram().getElements();
			bpmn.unmarshall(newDiagram, elements, id2node, id2lane);
		}
		Object[] object = BPMNToPetriNetConverter.convert(newDiagram);
		Petrinet pnet = (Petrinet) object[0];
		
		int count = 1;
		for(Place p : pnet.getPlaces()) {
			if(p.getLabel().isEmpty()) {
				p.getAttributeMap().put(AttributeMap.LABEL, "_empty_" + count++);
			}
		}
		return object;
	}
	
	public au.qut.apromore.automaton.Automaton createFSMfromPetrinet(Petrinet pnet, Marking marking, BiMap<Integer, String> eventLabelMapping, BiMap<String, Integer> inverseEventLabelMapping) throws ConnectionCannotBeObtained, IOException
	{
		int i=0;
		for(PetrinetNode transition : pnet.getTransitions())
		{
			transitions++;
			if(transition.getLabel().isEmpty())
				transition.getAttributeMap().put(AttributeMap.LABEL, "empty_" + (i++));
			if(pnet.getOutEdges(transition).size()>=2) {
				parallel++;
				for(PetrinetEdge outEdge : pnet.getOutEdges((transition)))
				{
					PetrinetNode target = (PetrinetNode) outEdge.getTarget();
					for(PetrinetEdge outEdge2 : pnet.getOutEdges(target))
					{
						org.processmining.models.graphbased.directed.petrinet.elements.Transition tr = (org.processmining.models.graphbased.directed.petrinet.elements.Transition) outEdge2.getTarget();
						pLabels.add(tr.getLabel());
					}
				}
			}
		}
		for(PetrinetNode node : pnet.getPlaces())
		{
			places++;
			if(node.getLabel().isEmpty())
				node.getAttributeMap().put(AttributeMap.LABEL, "empty_" + (i++));
			if(pnet.getOutEdges(node).size()>=2) {
					choice++;
			}
		}
		arcs=pnet.getEdges().size();
		size = arcs + places + transitions;
		context.addConnection(new InitialMarkingConnection(pnet, marking));
		Object[] object = new TSGenerator().calculateTS(context, pnet, marking);
		if(object==null)
			System.exit(1);
		ReachabilityGraph pnet_rg = (ReachabilityGraph) object [0];
		modelAutomaton = convertReachabilityGraphToFSM(pnet, pnet_rg, eventLabelMapping, inverseEventLabelMapping);
		for(String tLabel : pLabels)
		{
			if(!(tLabel.contains(cTau) || tLabel.contains(tau) || tLabel.contains(invisible)
					|| tLabel.contains(empty) || tLabel.equals(emptyStr) || tLabel.matches(strRegEx))) {
				parallelLabels.add(globalInverseLabels.get(tLabel));
			}
		}
		modelAutomaton.setParallelLabels(parallelLabels);
		return modelAutomaton;
	}
	
	public au.qut.apromore.automaton.Automaton createFSMfromPNMLFile(String fileName, BiMap<Integer, String> eventLabelMapping, BiMap<String, Integer> inverseEventLabelMapping) throws Exception
	{
		PnmlImportNet imp = new PnmlImportNet();
		Object[] object = (Object[]) imp.importFile(context, fileName);
		Petrinet pnet = (Petrinet) object[0];
		Marking marking = (Marking) object[1];
		modelAutomaton = createFSMfromPetrinet(pnet, marking, eventLabelMapping, inverseEventLabelMapping);
		return modelAutomaton;
	}

	public void transformAndExportPetriNetFromBPMNFile(String fileName, String exportFileName) throws Exception
	{
		org.processmining.plugins.bpmn.Bpmn bpmn = (org.processmining.plugins.bpmn.Bpmn) new org.processmining.plugins.bpmn.plugins.BpmnImportPlugin().importFile(context, fileName);
		org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters parameters = new org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters();
		@SuppressWarnings("unused")
		BpmnSelectDiagramDialog dialog = new BpmnSelectDiagramDialog(bpmn.getDiagrams(), parameters);
		org.processmining.models.graphbased.directed.bpmn.BPMNDiagram newDiagram = org.processmining.models.graphbased.directed.bpmn.BPMNDiagramFactory.newBPMNDiagram("");
		Map<String, org.processmining.models.graphbased.directed.bpmn.BPMNNode> id2node = new HashMap<>();
		Map<String, org.processmining.models.graphbased.directed.bpmn.elements.Swimlane> id2lane = new HashMap<>();
		if (parameters.getDiagram() == org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters.NODIAGRAM) {
			bpmn.unmarshall(newDiagram, id2node, id2lane);
		} else {
			Collection<String> elements = parameters.getDiagram().getElements();
			bpmn.unmarshall(newDiagram, elements, id2node, id2lane);
		}
		Object[] object = BPMNToPetriNetConverter.convert(newDiagram);
		Petrinet pnet = (Petrinet) object[0];
		int count = 1;
		for(Place p : pnet.getPlaces()) {
			if(p.getLabel().isEmpty()) {
				p.getAttributeMap().put(AttributeMap.LABEL, "_empty_" + count++);
			}
		}

		Marking initialMarking = (Marking) object[1];
		context.addConnection(new InitialMarkingConnection(pnet,initialMarking));
		new PnmlExportNetToPNML().exportPetriNetToPNMLFile(context, pnet, new File(exportFileName));
	}

	public au.qut.apromore.automaton.Automaton createFSMfromBPNMFileWithConversion(String fileName, BiMap<Integer, String> eventLabelMapping, BiMap<String, Integer> inverseEventLabelMapping) throws Exception
	{
		org.processmining.plugins.bpmn.Bpmn bpmn = (org.processmining.plugins.bpmn.Bpmn) new org.processmining.plugins.bpmn.plugins.BpmnImportPlugin().importFile(context, fileName);
		org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters parameters = new org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters();
		@SuppressWarnings("unused")
		BpmnSelectDiagramDialog dialog = new BpmnSelectDiagramDialog(bpmn.getDiagrams(), parameters);
		org.processmining.models.graphbased.directed.bpmn.BPMNDiagram newDiagram = org.processmining.models.graphbased.directed.bpmn.BPMNDiagramFactory.newBPMNDiagram("");
		Map<String, org.processmining.models.graphbased.directed.bpmn.BPMNNode> id2node = new HashMap<>();
		Map<String, org.processmining.models.graphbased.directed.bpmn.elements.Swimlane> id2lane = new HashMap<>();
		if (parameters.getDiagram() == org.processmining.plugins.bpmn.parameters.BpmnSelectDiagramParameters.NODIAGRAM) {
			bpmn.unmarshall(newDiagram, id2node, id2lane);
		} else {
			Collection<String> elements = parameters.getDiagram().getElements();
			bpmn.unmarshall(newDiagram, elements, id2node, id2lane);
		}
		Object[] object = BPMNToPetriNetConverter.convert(newDiagram);
		Petrinet pnet = (Petrinet) object[0];

		int count = 1;
		for(Place p : pnet.getPlaces()) {
			if(p.getLabel().isEmpty()) {
				p.getAttributeMap().put(AttributeMap.LABEL, "_empty_" + count++);
			}
		}

		Marking initialMarking = (Marking) object[1];
		context.addConnection(new InitialMarkingConnection(pnet, initialMarking));
		context.addConnection(new FinalMarkingConnection(pnet, (Marking) object[2]));
		object = new TSGenerator().calculateTS(context, pnet, initialMarking);
		ReachabilityGraph pnet_rg = (ReachabilityGraph) object [0];
		modelAutomaton = convertReachabilityGraphToFSM(pnet, pnet_rg, eventLabelMapping, inverseEventLabelMapping);
		return modelAutomaton;
	}
	
	public au.qut.apromore.automaton.Automaton convertReachabilityGraphToFSM(Petrinet pnet, ReachabilityGraph pnet_rg, BiMap<Integer, String> eventLabels, BiMap<String, Integer> inverseEventLabelMapping) throws IOException
	{
		au.qut.apromore.automaton.State.UNIQUE_ID = 0;
		int iEvent;
		this.stateLabelMapping = HashBiMap.create();
		if(eventLabels==null)
		{
			iEvent = 0;
			this.eventLabelMapping = HashBiMap.create();
		}
		else
		{
			iEvent = eventLabels.size()+1;
			this.eventLabelMapping = HashBiMap.create(eventLabels);
		}
		if(inverseEventLabelMapping==null) {
			this.inverseEventLabelMapping = HashBiMap.create();
			this.globalInverseLabels.put("tau",skipEvent);
		}
		else
		{
			this.inverseEventLabelMapping = HashBiMap.create(inverseEventLabelMapping);
			this.globalInverseLabels.putAll(inverseEventLabelMapping);
			if(!this.globalInverseLabels.containsKey("tau"))
				this.globalInverseLabels.put("tau",skipEvent);
		}
		this.stateMapping = HashBiMap.create();
		this.transitionMapping = HashBiMap.create();
		
		this.finalStates = new IntHashSet();
		
		//int iState = -1;
		//int iTransition = 0;
		IntHashSet modelEventLabels = new IntHashSet();
		Integer rkey;
		au.qut.apromore.automaton.State state;
		au.qut.apromore.automaton.State source;
		au.qut.apromore.automaton.State target;
		au.qut.apromore.automaton.Transition transition;
		UnifiedSet invLabels = new UnifiedSet();
		for (State s : pnet_rg.getNodes())
		{
			if(!this.stateMapping.containsKey(this.stateLabelMapping.get(s.getLabel())))
			{
				//iState++;
				state = new au.qut.apromore.automaton.State(s.getLabel(), 
						s.getGraph().getInEdges(s).isEmpty(), s.getGraph().getOutEdges(s).isEmpty());
				this.stateMapping.put(state.id(), state);
				this.stateLabelMapping.put(s.getLabel(), state.id());
				if(state.isSource() && iSource==0){iSource=state.id();}
				if(state.isFinal()){this.finalStates.add(state.id());}
			}
			
			for(Transition t : s.getGraph().getOutEdges(s))
			{
				if(!this.stateMapping.containsKey(this.stateLabelMapping.get(t.getTarget().getLabel())))
				{
					state = new au.qut.apromore.automaton.State(t.getTarget().getLabel(), 
							t.getGraph().getInEdges(t.getTarget()).isEmpty(), t.getGraph().getOutEdges(t.getTarget()).isEmpty());
					this.stateMapping.put(state.id(), state);
					this.stateLabelMapping.put(t.getTarget().getLabel(), state.id());
					if(state.isSource() && iSource==0){iSource=state.id();}
					if(state.isFinal()){this.finalStates.add(state.id());}
				}

				for(org.processmining.models.graphbased.directed.petrinet.elements.Transition tr : pnet.getTransitions()) 
				{
					if(tr.isInvisible())
					{
						if(t.getLabel().equals(tr.getLabel()))
						{
							invLabels.add(t.getLabel());
							t.setLabel(tau);
							break;
						}
					}
				}
				String tLabel = t.getLabel();
				if(tLabel.contains(cTau) || tLabel.contains(tau) || tLabel.contains(invisible) 
						|| tLabel.contains(empty) || tLabel.equals(emptyStr) || tLabel.matches(strRegEx)) {
					invLabels.add(tLabel);
					tLabel = tau;
				}
				
				if((rkey = this.globalInverseLabels.get(tLabel)) == null)
				{
					rkey = iEvent;
					//this.eventLabelMapping.put(iEvent, tLabel);
					this.globalInverseLabels.put(tLabel, iEvent);
					//this.inverseEventLabelMapping.put(tLabel, iEvent);
					//if(tLabel.equals(tau))
					//	skipEvent = iEvent;
					iEvent++;
				}
				modelEventLabels.add(rkey);
				
				//iTransition++;
				source = this.stateMapping.get(this.stateLabelMapping.get(s.getLabel()));
				target = this.stateMapping.get(this.stateLabelMapping.get(t.getTarget().getLabel()));
				transition = new au.qut.apromore.automaton.Transition(source, target, rkey);
				if(!this.transitionMapping.containsValue(transition))
					this.transitionMapping.put(transition.id(), transition);
				source.outgoingTransitions().add(transition);
				target.incomingTransitions().add(transition);
			}	
		}
		//System.out.println(invLabels);
		this.eventLabelMapping = HashBiMap.create(this.globalInverseLabels.inverse());
		Set<Integer> keySet = new UnifiedSet<>();
		keySet.addAll(this.eventLabelMapping.keySet()); 
		for(int key : keySet)
			if(!modelEventLabels.contains(key))
				this.eventLabelMapping.remove(key);
		this.inverseEventLabelMapping=this.eventLabelMapping.inverse();
		this.rg_size_before_tau_removal = this.stateMapping.size() + this.transitionMapping.size();
		this.removeTauArcs();
		modelAutomaton = new au.qut.apromore.automaton.Automaton(this.stateMapping, this.eventLabelMapping, this.inverseEventLabelMapping, this.transitionMapping, iSource, this.finalStates, skipEvent);//, globalInverseLabels.inverse());//, ImportPetriNet.readFile());
		this.rg_nodes = modelAutomaton.numberNodes;
		this.rg_arcs = modelAutomaton.numberArcs;
		this.rg_size = modelAutomaton.totalSize;
		return modelAutomaton;
	}

	/* ############ MY CODE STARTS ############ */


	public au.qut.apromore.automaton.Automaton createFSMfromBPMNFile(String fileName, BiMap<Integer, String> eventLabelMapping, BiMap<String, Integer> inverseEventLabelMapping) throws Exception {
		BPMNDiagram bpmnDiagram = new BpmnImportPlugin().importFromStreamToDiagram(new FileInputStream(new File(fileName)), fileName);
		BPMNtoTSConverter bpmnToFSMConverter = new BPMNtoTSConverter();
		ReachabilityGraph rg = bpmnToFSMConverter.BPMNtoTS(bpmnDiagram);
		idsMapping = getIdsMapping(bpmnDiagram);
		artificialGatewaysInfo = bpmnToFSMConverter.artificialGatewaysInfo;
		modelAutomaton = convertReachabilityGraphToFSM(rg, eventLabelMapping, inverseEventLabelMapping);
		return modelAutomaton;
	}

	public au.qut.apromore.automaton.Automaton createFSMfromBPMN(BPMNDiagram diagram, BiMap<Integer, String> eventLabelMapping, BiMap<String, Integer> inverseEventLabelMapping){
		BPMNtoTSConverter bpmnToFSMConverter = new BPMNtoTSConverter();
		ReachabilityGraph rg = bpmnToFSMConverter.BPMNtoTS(diagram);
		idsMapping = getIdsMapping(diagram);
		artificialGatewaysInfo = bpmnToFSMConverter.artificialGatewaysInfo;
		modelAutomaton = convertReachabilityGraphToFSM(rg, eventLabelMapping, inverseEventLabelMapping);
		return modelAutomaton;
	}

	public Automaton convertReachabilityGraphToFSM(ReachabilityGraph rg, BiMap<Integer, String> eventLabels, BiMap<String, Integer> inverseEventLabelMapping) {
		LinkedHashMap<Integer, au.qut.apromore.automaton.State> originalStateMapping = new LinkedHashMap<>();
		LinkedHashMap<Integer, au.qut.apromore.automaton.Transition> originalTransitionMapping = new LinkedHashMap<>();

		au.qut.apromore.automaton.State.UNIQUE_ID = 0;
		int iEvent;
		this.stateLabelMapping = HashBiMap.create();

		if(eventLabels==null)
		{
			iEvent = 0;
			this.eventLabelMapping = HashBiMap.create();
		}
		else
		{
			iEvent = eventLabels.size() + 1;
			this.eventLabelMapping = HashBiMap.create(eventLabels);
		}

		if(inverseEventLabelMapping==null) {
			this.inverseEventLabelMapping = HashBiMap.create();
			this.globalInverseLabels.put("tau",skipEvent);
		}
		else
		{
			this.inverseEventLabelMapping = HashBiMap.create(inverseEventLabelMapping);
			this.globalInverseLabels.putAll(inverseEventLabelMapping);
		}

		this.stateMapping = HashBiMap.create();
		this.transitionMapping = HashBiMap.create();
		this.finalStates = new IntHashSet();

		IntHashSet modelEventLabels = new IntHashSet();
		Integer rkey;
		au.qut.apromore.automaton.State state;
		au.qut.apromore.automaton.State source;
		au.qut.apromore.automaton.State target;
		au.qut.apromore.automaton.Transition transition;
		List<Integer> tauIdxs = new ArrayList<>();

		for (State s : rg.getNodes())
		{
			if(!this.stateMapping.containsKey(this.stateLabelMapping.get(s.getLabel())))
			{
				state = new au.qut.apromore.automaton.State(s.getLabel(),
						s.getGraph().getInEdges(s).isEmpty(), s.getGraph().getOutEdges(s).isEmpty());
				this.stateMapping.put(state.id(), state);
				this.stateLabelMapping.put(s.getLabel(), state.id());

				originalStateMapping.put(state.id(), new au.qut.apromore.automaton.State(state)); //

				if(state.isSource() && iSource==0){iSource=state.id();}
				if(state.isFinal()){this.finalStates.add(state.id());}
			}

			for(Transition t : s.getGraph().getOutEdges(s))
			{
				if(!this.stateMapping.containsKey(this.stateLabelMapping.get(t.getTarget().getLabel())))
				{
					state = new au.qut.apromore.automaton.State(t.getTarget().getLabel(),
							t.getGraph().getInEdges(t.getTarget()).isEmpty(), t.getGraph().getOutEdges(t.getTarget()).isEmpty());
					this.stateMapping.put(state.id(), state);

					originalStateMapping.put(state.id(), new au.qut.apromore.automaton.State(state)); //

					this.stateLabelMapping.put(t.getTarget().getLabel(), state.id());
					if(state.isSource() && iSource==0){iSource=state.id();}
					if(state.isFinal()){this.finalStates.add(state.id());}
				}

				String tLabel = t.getLabel();

				if((rkey = this.globalInverseLabels.get(tLabel)) == null)
				{
					rkey = iEvent;
					this.globalInverseLabels.put(tLabel, iEvent);
					iEvent++;
				}
				modelEventLabels.add(rkey);

				source = this.stateMapping.get(this.stateLabelMapping.get(s.getLabel()));
				target = this.stateMapping.get(this.stateLabelMapping.get(t.getTarget().getLabel()));
				transition = new au.qut.apromore.automaton.Transition(source, target, rkey);
				if(!this.transitionMapping.containsValue(transition))
					this.transitionMapping.put(transition.id(), transition);
				source.outgoingTransitions().add(transition);
				target.incomingTransitions().add(transition);

				var originalSource = originalStateMapping.get(this.stateLabelMapping.get(s.getLabel()));
				var originalTarget = originalStateMapping.get(this.stateLabelMapping.get(t.getTarget().getLabel()));
				var originalTransition = new au.qut.apromore.automaton.Transition(transition.id(), originalSource, originalTarget, rkey);
				if(!originalTransitionMapping.containsValue(originalTransition))
					originalTransitionMapping.put(originalTransition.id(), originalTransition);
				originalSource.outgoingTransitions().add(originalTransition);
				originalTarget.incomingTransitions().add(originalTransition);
			}
		}

		for(Map.Entry<String, Integer> entry: globalInverseLabels.entrySet()){
			if(entry.getKey().startsWith("gateway "))
				tauIdxs.add(entry.getValue());
		}

		this.eventLabelMapping = HashBiMap.create(this.globalInverseLabels.inverse());
		Set<Integer> keySet = new UnifiedSet<>();
		keySet.addAll(this.eventLabelMapping.keySet());
		for(int key : keySet)
			if(!modelEventLabels.contains(key))
				this.eventLabelMapping.remove(key);
		this.inverseEventLabelMapping=this.eventLabelMapping.inverse();

		HashMap<Integer, String> originalEventLabelMapping = new HashMap<>();
		for(Map.Entry<Integer, String> entry : eventLabelMapping.entrySet())
			originalEventLabelMapping.put(entry.getKey(), entry.getValue());

		HashMap<String, Integer> originalInverseEventLabelMapping = new HashMap<>(originalEventLabelMapping.entrySet().stream().
				collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey)));

		IntHashSet originalFinalStates = new IntHashSet(this.finalStates);

		originalModelAutomaton = new Automaton(originalStateMapping, HashBiMap.create(originalEventLabelMapping),
				HashBiMap.create(originalInverseEventLabelMapping), originalTransitionMapping, iSource, originalFinalStates, skipEvent);

		this.rg_size_before_tau_removal = this.stateMapping.size() + this.transitionMapping.size();

		for(var key: transitionMapping.keySet()){
			var trs = transitionMapping.get(key);

			Integer eventID = trs.eventID();

			if(tauIdxs.contains(eventID)){
				eventLabelMapping.remove(eventID);
				trs.setEventID(skipEvent);
			}
		}

		if(!this.eventLabelMapping.containsKey(skipEvent))
			this.eventLabelMapping.put(skipEvent, "tau");

		this.removeTauArcs();
		modelAutomaton = new au.qut.apromore.automaton.Automaton(this.stateMapping, this.eventLabelMapping, this.inverseEventLabelMapping, this.transitionMapping, iSource, this.finalStates, skipEvent);//, globalInverseLabels.inverse());//, ImportPetriNet.readFile());
		this.rg_nodes = modelAutomaton.numberNodes;
		this.rg_arcs = modelAutomaton.numberArcs;
		this.rg_size = modelAutomaton.totalSize;
		return modelAutomaton;
	}

	private HashMap<String, String> getIdsMapping(BPMNDiagram diagram){
		HashMap<String, String> idsMapping = new HashMap<>();

		for(var node: diagram.getNodes().stream().filter(node -> node instanceof Event ||
				node instanceof Activity || node instanceof Gateway).collect(Collectors.toList())){
			idsMapping.put(node.getLabel(), node.getAttributeMap().get("Original id").toString());
		}

		return idsMapping;
	}

	/* ############ MY CODE ENDS ############ */
	
	public void removeTauArcs()
	{
		IntArrayList toBeVisited = new IntArrayList();
		IntHashSet visited = new IntHashSet();
		toBeVisited.add(this.iSource);
		
		while(!toBeVisited.isEmpty())
		{
			au.qut.apromore.automaton.State state = this.stateMapping.get(toBeVisited.removeAtIndex(0));
			UnifiedSet<au.qut.apromore.automaton.Transition> in = new UnifiedSet<au.qut.apromore.automaton.Transition>(state.incomingTransitions());
			for(au.qut.apromore.automaton.Transition tr : in)
			{
				if(tr.eventID()==this.skipEvent)
					replaceTauArc(tr, state, new UnifiedSet<>());
			}
			if(!state.isFinal())
			{
				Iterator<au.qut.apromore.automaton.Transition> it = state.incomingTransitions().iterator();
				while(it.hasNext())
				{
					au.qut.apromore.automaton.Transition tr = it.next();
					if(tr.eventID()==this.skipEvent)
					{
						it.remove();
						tr.source().outgoingTransitions().remove(tr);
						this.transitionMapping.remove(tr.id());
						//this.transitionMapping.inverse().remove(tr);
					}
				}
			}
			for(au.qut.apromore.automaton.Transition tr : state.outgoingTransitions())
				if(visited.add(tr.target().id()))
					toBeVisited.add(tr.target().id());
		}
		boolean notFinished = true;
		while(notFinished)
		{
			notFinished = false;
			Iterator<au.qut.apromore.automaton.State> it = this.stateMapping.values().iterator();
			while(it.hasNext())
			{
				au.qut.apromore.automaton.State state = it.next();
				if(state.incomingTransitions().isEmpty()&& !state.isSource())
				{
					for(au.qut.apromore.automaton.Transition tr : state.outgoingTransitions())
					{
						tr.target().incomingTransitions().remove(tr);
						this.transitionMapping.remove(tr.id());
						//this.transitionMapping.inverse().remove(tr);
					}
					it.remove();
					notFinished = true;
					break;
				} else if(state.outgoingTransitions().isEmpty() && !state.isFinal())
				{
					for(au.qut.apromore.automaton.Transition tr : state.incomingTransitions())
					{
						tr.source().outgoingTransitions().remove(tr);
						this.transitionMapping.remove(tr.id());
						//this.transitionMapping.inverse().remove(tr);
					}
					it.remove();
					notFinished = true;
					break;
				}
			}
		}
		for(int finalState : this.finalStates.toArray())
		{
			au.qut.apromore.automaton.State state = this.stateMapping.get(finalState);
			UnifiedSet<au.qut.apromore.automaton.Transition> in = new UnifiedSet<>(state.incomingTransitions());
			for(au.qut.apromore.automaton.Transition tr : in)
			{
				if(tr.eventID()==this.skipEvent)
				{
					if(tr.source().isSource())
					{
						tr.source().setFinal(true);
						continue;
					}
					for(au.qut.apromore.automaton.Transition replace : tr.source().incomingTransitions())
					{
						au.qut.apromore.automaton.Transition repTr = new au.qut.apromore.automaton.Transition(replace.source(), tr.target(), replace.eventID());
						if(!this.transitionMapping.containsValue(repTr))
						{
							replace.source().outgoingTransitions().add(repTr);
							tr.target().incomingTransitions().add(repTr);
							this.transitionMapping.put(repTr.id(), repTr);
						}
					}
				}
			}

			Iterator<au.qut.apromore.automaton.Transition> it = state.incomingTransitions().iterator();
			while(it.hasNext())
			{
				au.qut.apromore.automaton.Transition tr = it.next();
				if(tr.eventID()==this.skipEvent)
				{
					it.remove();
					tr.source().outgoingTransitions().remove(tr);
					this.transitionMapping.remove(tr.id());
					//this.transitionMapping.inverse().remove(tr);
				}
			}
		}
		notFinished = true;
		while(notFinished)
		{
			notFinished = false;
			Iterator<au.qut.apromore.automaton.State> it = this.stateMapping.values().iterator();
			while(it.hasNext())
			{
				au.qut.apromore.automaton.State state = it.next();
				if(state.incomingTransitions().isEmpty()&& !state.isSource())
				{
					for(au.qut.apromore.automaton.Transition tr : state.outgoingTransitions())
					{
						tr.target().incomingTransitions().remove(tr);
						this.transitionMapping.remove(tr.id());
						//this.transitionMapping.inverse().remove(tr);
					}
					it.remove();
					notFinished = true;
					break;
				} else if(state.outgoingTransitions().isEmpty() && !state.isFinal())
				{
					for(au.qut.apromore.automaton.Transition tr : state.incomingTransitions())
					{
						tr.source().outgoingTransitions().remove(tr);
						this.transitionMapping.remove(tr.id());
						//this.transitionMapping.inverse().remove(tr);
					}
					it.remove();
					notFinished = true;
					break;
				}
			}
		}
	}
	
	private void replaceTauArc(au.qut.apromore.automaton.Transition tau, au.qut.apromore.automaton.State state, Set<au.qut.apromore.automaton.State> closed)
	{
		if(state.isFinal())
		{
			au.qut.apromore.automaton.Transition repTr = new au.qut.apromore.automaton.Transition(tau.source(), state, this.skipEvent);
			if(!transitionMapping.containsValue(repTr))
			{
				transitionMapping.put(repTr.id(), repTr);
				tau.source().outgoingTransitions().add(repTr);
				state.incomingTransitions().add(repTr);
			}
			return;
		}
		UnifiedSet<au.qut.apromore.automaton.Transition> out = new UnifiedSet<>(state.outgoingTransitions());
		for(au.qut.apromore.automaton.Transition tr : out)
		{
			if(tr.eventID()==this.skipEvent)
			{
				if(closed.add(tr.target()))
					replaceTauArc(tau, tr.target(), closed);
			}
			else
			{
				au.qut.apromore.automaton.Transition repTr = new au.qut.apromore.automaton.Transition(tau.source(), tr.target(), tr.eventID());
				if(!this.transitionMapping.containsValue(repTr))
				{
					tau.source().outgoingTransitions().add(repTr);
					tr.target().incomingTransitions().add(repTr);
					this.transitionMapping.put(repTr.id(), repTr);
				}
			}
		}
	}
}
