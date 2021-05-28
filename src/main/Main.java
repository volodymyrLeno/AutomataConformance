package main;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import au.qut.apromore.ScalableConformanceChecker.DecomposingTRConformanceChecker;
import au.qut.apromore.ScalableConformanceChecker.TRConformanceChecker;
import au.qut.apromore.automaton.State;
import au.qut.apromore.importer.*;
import event.InfrequentBehaviourFilter;
import org.deckfour.xes.classification.XEventClassifier;
import org.deckfour.xes.classification.XEventNameClassifier;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.out.XMxmlGZIPSerializer;
import org.deckfour.xes.out.XSerializer;
import org.deckfour.xes.out.XesXmlGZIPSerializer;
import org.eclipse.collections.impl.list.mutable.FastList;
import org.eclipse.collections.impl.list.mutable.primitive.IntArrayList;
import org.eclipse.collections.impl.map.mutable.primitive.IntBooleanHashMap;
import org.eclipse.collections.impl.map.mutable.primitive.IntIntHashMap;
import org.eclipse.collections.impl.set.mutable.UnifiedSet;
import org.jbpt.petri.Flow;
import org.jbpt.petri.NetSystem;
import org.jbpt.petri.Node;
import org.jbpt.petri.PetriNet;
import org.jbpt.petri.Place;
import org.jbpt.petri.Transition;
import org.jbpt.petri.io.PNMLSerializer;
import org.jbpt.petri.unfolding.BPNode;
import org.jbpt.petri.unfolding.CompletePrefixUnfolding;
import org.jbpt.petri.unfolding.Condition;
import org.jbpt.petri.unfolding.Event;
import org.jbpt.petri.unfolding.IOccurrenceNet;
import org.jbpt.petri.unfolding.OccurrenceNet;
import org.processmining.log.models.XEventClassifierList;
import org.processmining.models.connections.petrinets.behavioral.InitialMarkingConnection;
import org.processmining.models.graphbased.directed.petrinet.Petrinet;
import org.processmining.models.semantics.petrinet.Marking;
import org.processmining.plugins.petrinet.replayresult.PNMatchInstancesRepResult;
import org.processmining.plugins.petrinet.replayresult.StepTypes;
import org.processmining.plugins.pnml.exporting.PnmlExportNetToPNML;

import com.raffaeleconforti.context.FakePluginContext;

import au.qut.apromore.ScalableConformanceChecker.DecomposingConformanceChecker;
import au.qut.apromore.ScalableConformanceChecker.ScalableConformanceChecker;
import au.qut.apromore.automaton.Automaton;
import org.processmining.plugins.replayer.replayresult.AllSyncReplayResult;

import javax.swing.plaf.synth.SynthEditorPaneUI;


public class Main {
	public static void main(String[] args) throws Exception
	{
		String filePath = "C:/Volodymyr/diagram12.bpmn";
		ImportProcessModel ipm = new ImportProcessModel();

		ipm.createAutomatonFromPNMLorBPMNFile(filePath,null,null);
		System.out.println();


		/*FastList<String> paths = new FastList<>();
		paths.add("/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/public/IM/");
		paths.add("/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/public/SM/");
		paths.add("/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/private/IM/");
		paths.add("/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/private/SM/");
		IntArrayList publicModels = new IntArrayList();
		for(int i=1;i<18;i++) publicModels.add(i);
		IntArrayList privateModels = new IntArrayList();
		privateModels.addAll(1,2,3,4,6,7,9,10);

		String model, log;
		IntArrayList models;
		for(String path : paths)
		{
			if(path.contains("public")) models = publicModels;
			else models = privateModels;
			for(int i : models.toArray())
			{*/



				//System.out.println(path + " - " + i);


				//log = i + ".xes.gz";
				//model = i + ".pnml";


				//if(((i==13||i==15) && path=="/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/public/IM/") || (i==2 && path=="/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/private/IM/") ) continue;
				//TRImporter stats = new TRImporter(path, log, model);
				//stats.recordStatistics();
				//ScalableConformanceChecker confChecker = new ScalableConformanceChecker(path, log, model, Integer.MAX_VALUE);
				//confChecker.printAlignmentStatistics(path + i + ".csv");
				//ImportProcessModel imp = new ImportProcessModel();
				//imp.createAutomatonFromPNMLorBPMNFile(path+i+".pnml",null,null);
				//TRImporter importer = new TRImporter(path, log, model);
				//importer.createAutomata();
				//importer.gatherTRStatistics();


				/*DecomposingConformanceImporter importer = new DecomposingConformanceImporter();
				importer.importAndDecomposeModelForStatistics(path, model);
				if(importer.scompRGSizeBeforeTauRemoval.isEmpty()) importer.scompRGSizeBeforeTauRemoval.add(0);
				System.out.println(importer.scompRGSizeBeforeTauRemoval.average());*/
			//}
		//}

		/*String path = "/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/public/IM/";
		String log = "4.xes.gz";
		String model = "4.pnml";
		ScalableConformanceChecker ac = new ScalableConformanceChecker(path, log, model, Integer.MAX_VALUE);
		TRConformanceChecker tr = new TRConformanceChecker(path, log, model, Integer.MAX_VALUE);
		PNMatchInstancesRepResult resTR = tr.resOneOptimal();
		PNMatchInstancesRepResult resAC = ac.resOneOptimal();
		int caseID, problemTraces = 0;

		System.out.println(resTR.getInfo());
		System.out.println(resAC.getInfo());
		for(AllSyncReplayResult alTR : resTR)
		{
			caseID = alTR.getTraceIndex().first();
			for(AllSyncReplayResult alAC : resAC)
			{
				if(alAC.getTraceIndex().contains(caseID))
				{
					if(!alTR.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST).equals(alAC.getInfo().get(PNMatchInstancesRepResult.RAWFITNESSCOST)))
					{
						problemTraces++;
						System.out.println("Result TR: " + alTR.getInfo());
						System.out.println("Result AC: " + alAC.getInfo());
						printAlignment(alTR);
						printAlignment(alAC);
					}
					break;
				}
			}
		}
		System.out.println(problemTraces);*/

		/*FastList<StepTypes> lstToExtendStepTypes = new FastList<>();
		lstToExtendStepTypes.add(StepTypes.L);
		lstToExtendStepTypes.add(StepTypes.L);
		lstToExtendStepTypes.add(StepTypes.MREAL);
		lstToExtendStepTypes.add(StepTypes.L);
		lstToExtendStepTypes.add(StepTypes.MREAL);
		lstToExtendStepTypes.add(StepTypes.LMGOOD);
		lstToExtendStepTypes.add(StepTypes.LMGOOD);
		lstToExtendStepTypes.add(StepTypes.MREAL);
		int rhideToExtend=3;
		for(int pos=0; pos < lstToExtendStepTypes.size(); pos++)
		{
			if(lstToExtendStepTypes.get(pos).equals(StepTypes.MREAL))
			{
				//lstToExtend.remove(pos);
				lstToExtendStepTypes.remove(pos);
				rhideToExtend--;
				pos--;
			}
		}
		System.out.println(lstToExtendStepTypes);
		System.out.println(rhideToExtend);*/

		/*IntBooleanHashMap test = new IntBooleanHashMap();
		test.put(18,false);
		test.put(19,true);
		System.out.println(test.get(18));
		System.out.println(test.get(19));
		System.out.println(test.get(20));
		System.out.println(test.get(30));*/

		//String path = "/Users/dreissner/Documents/Evaluations/S-Components/alignment/bpi12/";
		//String model = "bpi12.pnml";
		//String log = "bpi12.xes";
		/*for(int i=14;i<18;i++) {
			String fileName = "/Users/dreissner/Downloads/splitminer/outputs/" + i + ".bpmn";
			String exportFileName = "/Users/dreissner/Downloads/splitminer/outputs/" + i + ".pnml";
			new ImportProcessModel().transformAndExportPetriNetFromBPMNFile(fileName, exportFileName);
		}*/
		//String path = "/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/public/IM/";
		/*String path = args[0];
		path = "/Users/dreissner/Downloads/splitminer/outputs/";
		String model = "13.pnml";
		String log = "13.xes.gz";
		for(int l = 13 ; l<=17; l++) {
			*//*log = l + ".xes.gz";
			ImportEventLog importer = new ImportEventLog();
			XLog xLog = importer.importEventLog(path + log);
			XLog filteredLog = importer.filterLogSimple(xLog, 0.01);
			//InfrequentBehaviourFilter filter = new InfrequentBehaviourFilter(new XEventNameClassifier());
			//XLog filteredLog = filter.filterLog(xLog);
			FileOutputStream out = new FileOutputStream(path + log.substring(0, log.length() - 7) + "_f.xes.gz");
			XSerializer logSerializer = new XesXmlGZIPSerializer();
			logSerializer.serialize(filteredLog, out);
			out.close();
			System.out.println("Log " + log.substring(0, log.length() - 7) + "_f.xes.gz created");*//*
			//XLog newLog = importer.importEventLog(path + l + "_f.xes.gz");
			model = l + ".bpmn";
			ImportProcessModel importer = new ImportProcessModel();
			Object[] obj = importer.importPetrinetFromBPMN(path+model);
			PnmlExportNetToPNML exporter = new PnmlExportNetToPNML();
			FakePluginContext context = new FakePluginContext();
			Petrinet pnet = (Petrinet) obj[0];
			Marking initMarking = (Marking) obj[1];
			context.addConnection(new InitialMarkingConnection(pnet,initMarking));
			exporter.exportPetriNetToPNMLFile(new FakePluginContext(),pnet,new File(path + l + ".pnml"));
		}*/
		/*TRImporter importer = new TRImporter(path, log, model);
		importer.createAutomata();
		TRConformanceChecker conf = new TRConformanceChecker(importer.logAutomaton,importer.modelAutomaton, Integer.MAX_VALUE);
		System.out.println(conf.resOneOptimal().getInfo());*/
		/*DecomposingTRImporter importer = new DecomposingTRImporter();
		importer.importAndDecomposeModelAndLogForConformanceChecking(path, model, log);
		DecomposingTRConformanceChecker conf = new DecomposingTRConformanceChecker(importer);
		System.out.println(conf.alignmentResult.getInfo());*/
		/*ImportProcessModel importer = new ImportProcessModel();
		importer.createAutomatonAlternative(path + model);
		System.out.println(importer.rg_nodes);
		System.out.println(importer.rg_arcs);
		System.out.println(importer.rg_size);*/
		/*UnifiedSet<UnifiedSet<String>> sets = new UnifiedSet<>();
		for(State st : importer.model.states().values())
		{
			String[] places = st.label().split(",");
			UnifiedSet<String> pl = new UnifiedSet<>();
			for(String place : places) {
				place = place.replace("[","");
				place = place.replace("]","");
				pl.add(place);
			}
			System.out.println(pl);
			if(sets.add(pl))
				System.out.println("New");
			else
				System.out.println("Copy");
		}*/
		/*ImportProcessModel importer2 = new ImportProcessModel();
		importer2.createAutomatonFromPNMLorBPMNFile(path+model,null,null);
		System.out.println(importer2.rg_nodes);
		System.out.println(importer2.rg_arcs);
		System.out.println(importer2.rg_size);*/
		/*sets = new UnifiedSet<>();
		for(State st : importer2.model.states().values())
		{
			String[] places = st.label().split(",");
			UnifiedSet<String> pl = new UnifiedSet<>();
			for(String place : places) {
				place = place.replace("[","");
				place = place.replace("]","");
				pl.add(place);
			}
			System.out.println(pl);
			if(sets.add(pl))
				System.out.println("New");
			else
				System.out.println("Copy");
		}*/
		//importer.model.toDot(path+"13.dot");
		/*String path = "/Users/dreissner/Documents/Evaluations/TandemRepeatsPaper/";
		FastList<String> directories = new FastList<String>();
		//directories.add("public/IM/");
		directories.add("public/SM/");
		directories.add("private/IM/");
		directories.add("private/SM/");
		IntArrayList datasets;
		for(String directory : directories)
		{
			datasets = new IntArrayList();
			if(directory.contains("public"))
			{
				for(int i=16; i<18;i++)
					if(directory.contains("IM") && i==13) continue;
					else datasets.add(i);
			}
			else datasets.addAll(1,2,3,4,6,7,9,10);
			for(int dataset : datasets.toArray())
			{
				TRImporter importer = new TRImporter(path + directory,dataset + ".xes.gz", dataset + ".pnml");
				importer.recordStatistics();
			}
		}*/
		//PrecisionImporter imp = new PrecisionImporter();
		//imp.importAndDecomposeModelAndLogForConformanceChecking(path, model, log);
		//new TRConformanceChecker(path,log,model,100000);
		//DecomposingConformanceImporter imp = new DecomposingConformanceImporter();
		//imp.importAndDecomposeModelAndLogForConformanceChecking(path, model, log);
//		Automaton dfa = null;
//		int max = -1;
//		int j=0;;
//		for(int i = 0; i < imp.sComponentFSMs.size(); i++)
//		{
//			Automaton a = imp.sComponentFSMs.get(i);
//			if(a.loops > max){
//				j=i;
//				max = a.loops; dfa = a;
//			}
//		}
//		Automaton dafsa = imp.componentDAFSAs.get(j);
//		IntIntHashMap conf = null;
//		max = -1;
//		for(IntIntHashMap c : dafsa.configCasesMapping().keySet())
//		{
//			if(c.sum()>max)
//			{
//				max=(int) c.sum();
//				conf = c;
//			}
//		}
//		Set<IntIntHashMap> fLoops = dfa.source().futureLoops();
//		System.out.println(conf);
//		System.out.println(fLoops);
//		ScalableConformanceChecker ch = new ScalableConformanceChecker(); 
		//long start = System.nanoTime();
//		for(int i = 0; i < 1000000; i++)
//			ch.calcLoopSkips(conf, fLoops);
//		System.out.println(TimeUnit.NANOSECONDS.toMillis(System.nanoTime()-start));
			
		
		//Automaton dafsa = new ImportEventLog().convertLogToAutomatonFrom(path + log);
		//Automaton dfa = new ImportProcessModel().createFSMfromPNMLFile(path + model, dafsa.eventLabels(), dafsa.inverseEventLabels());
		
		//ScalableConformanceChecker proConf = new ScalableConformanceChecker(dafsa, dfa, 100000);
		//DecomposingConformanceChecker proConf = new DecomposingConformanceChecker(imp);
		//DecomposingConformanceImporter decomposer = new DecomposingConformanceImporter();
		//decomposer.importAndDecomposeModelAndLogForConformanceChecking(path, model, log);
//		System.out.println("Time: " + TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - start) + " ms");
		//long start = System.nanoTime();
		//DecomposingConformanceChecker pro =  new DecomposingConformanceChecker(decomposer);
		//System.out.println("Time: " + TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - start) + " ms");
		//pro.printAlignmentResults(path + "statistics.csv", path + "results.csv");
		
		
		//start = System.nanoTime();
		//pro.printAlignmentResults("/Users/daniel/Documents/workspace/paper_tests/Sepsis/statistics.csv", "/Users/daniel/Documents/workspace/paper_tests/Sepsis/caseTypes.csv");
		//System.out.println("Time: " + TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - start) + " ms");
//		int i = 1;
//		for(Petrinet pnet : decomposer.sComponentNets)
//		{
//			//fsm.toDot("/Users/daniel/Documents/workspace/paper_tests/BPIC2012/net" + i++ + ".dot");
//			try {
//				new PnmlExportNetToPNML().exportPetriNetToPNMLFile(new FakePluginContext(), pnet, new File("/Users/daniel/Documents/workspace/paper_tests/BPIC2012/net" + i++ + ".pnml"));
//			} catch (IOException e) {
//				e.printStackTrace();
//			}
//		}
//		i=0;
//		for(IntArrayList trace : decomposer.caseTracesMapping.keySet())
//		{
//			if(trace.size()>=170)
//			{
//				i++;
//				System.out.println("Trace size: " + trace.size());
//				System.out.println(trace);
//				for(int key : decomposer.traceProjections.get(trace).keySet())
//				{
//					System.out.println(key + " - " + decomposer.traceProjections.get(trace).get(key));
//				}
//			}
//		}
//		System.out.println(i);
		
		
		
//		PNMLSerializer importer = new PNMLSerializer();
//		NetSystem pnet = importer.parse("/Users/daniel/Documents/workspace/paper_tests/BPIC2012/net4.pnml");
//		CompletePrefixUnfolding unfolder = new CompletePrefixUnfolding(pnet);
//		for(Transition tr : pnet.getTransitions())
//			System.out.println(tr.getLabel() + " - " + unfolder.getEvents(tr));
//		
//		System.out.println(unfolder.getEvents());
//		OccurrenceNet onet = (OccurrenceNet) unfolder.getOccurrenceNet();
//		PrintWriter pw = new PrintWriter("/Users/daniel/Documents/workspace/paper_tests/BPIC2012/net4unfolding.dot");
//		pw.print(onet.toDOT());
//		pw.close();
		//System.out.println(onet.toDOT());
		
		//DecomposingConformanceImporter decomposer = new DecomposingConformanceImporter();
		//Object[] pnetAndMarking = decomposer.importPetriNetAndMarking("/Users/daniel/Documents/workspace/paper_tests/BPIC2012/net4.pnml");
		
	}

	public static void printAlignment(AllSyncReplayResult res)
	{
		String al = "Alignment = [";
		for(int pos = 0; pos < res.getNodeInstanceLst().get(0).size();pos++)
		{
			al += "(" + res.getStepTypesLst().get(0).get(pos) + ", " + res.getNodeInstanceLst().get(0).get(pos) +"), ";
		}
		al = al.substring(0, al.length()-2) + "]";
		System.out.println(al);
	}
}