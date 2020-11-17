package SFT;

import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.AfterClass;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;

import java.util.List;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Collection;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.Scanner;
import java.util.HashMap;

import theory.characters.*;
import transducers.sft.SFT;
import transducers.sft.SFTMove;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTEpsilon;
import transducers.sft.SFTProduct;
import transducers.sft.SFTProductInputMove;
import automata.Move;
import automata.sfa.SFA;
import automata.sfa.SFAEpsilon;
import automata.sfa.SFAMove;
import automata.sfa.SFAInputMove;

import theory.intervals.UnaryCharIntervalSolver;

/** 
* Examples for SFT Repair
* 
* Merge or remove this file later
*/

public class SFTRepExamples {
	
	// what does this do?
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFT<CharPred, CharFunc, Character> mySFT10;
	private static SFT<CharPred, CharFunc, Character> mySFT11;
	private static SFT<CharPred, CharFunc, Character> mySFT12;
	private static SFA<CharPred, Character> mySFA00;
	private static SFA<CharPred, Character> mySFA01;
	
	@BeforeClass
	public static void beforeClass() throws Exception {
		
		// SFT1.0: SFT that reads a+ and outputs ab*
		List<SFTMove<CharPred, CharFunc, Character>> transitions10 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output101 = new ArrayList<CharFunc>();
		output101.add(new CharConstant('a'));
		transitions10.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 2, new CharPred('a'), output101));
		List<CharFunc> output102 = new ArrayList<CharFunc>();
		output102.add(new CharConstant('b'));
		transitions10.add(new SFTInputMove<CharPred, CharFunc, Character>(2, 2, new CharPred('a'), output102));
		Map<Integer, Set<List<Character>>> finStatesAndTails10 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails10.put(2, new HashSet<List<Character>>());
		mySFT10 = SFT.MkSFT(transitions10, 1, finStatesAndTails10, ba);
		
		// SFT1.1: SFT that reads ab* and outputs a(bc)*
		List<SFTMove<CharPred, CharFunc, Character>> transitions11 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output111 = new ArrayList<CharFunc>();
		output111.add(new CharConstant('a'));
		transitions11.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 2, new CharPred('a'), output111));
		List<CharFunc> output112 = new ArrayList<CharFunc>();
		output112.add(new CharConstant('b'));
		output112.add(new CharConstant('c'));
		transitions11.add(new SFTInputMove<CharPred, CharFunc, Character>(2, 2, new CharPred('b'), output112));
		Map<Integer, Set<List<Character>>> finStatesAndTails11 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails11.put(2, new HashSet<List<Character>>());
		mySFT11 = SFT.MkSFT(transitions11, 1, finStatesAndTails11, ba);
		System.out.println(mySFT11.toString());
		
		// SFT1.2: SFT that reads ab* and outputs ac*
		List<SFTMove<CharPred, CharFunc, Character>> transitions12 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output121 = new ArrayList<CharFunc>();
		output121.add(new CharConstant('a'));
		transitions12.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 2, new CharPred('a'), output121));
		List<CharFunc> output122 = new ArrayList<CharFunc>();
		output122.add(new CharConstant('c'));
		transitions12.add(new SFTInputMove<CharPred, CharFunc, Character>(2, 2, new CharPred('b'), output122));
		Map<Integer, Set<List<Character>>> finStatesAndTails12 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails12.put(2, new HashSet<List<Character>>());
		mySFT12 = SFT.MkSFT(transitions12, 1, finStatesAndTails12, ba);
		
		// SFA0.0: SFA that reads a(bc)*
		List<SFAMove<CharPred, Character>> transitions00 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions00.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('a')));
		transitions00.add(new SFAInputMove<CharPred, Character>(2, 2, new CharPred('b', 'c')));
		List<Integer> finStates00 = new LinkedList<Integer>();
		finStates00.add(2);
		mySFA00 = SFA.MkSFA(transitions00, 1, finStates00, ba);
		
		// SFA0.1: SFA that reads ac*
		List<SFAMove<CharPred, Character>> transitions01 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions01.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions01.add(new SFAInputMove<CharPred, Character>(1, 1, new CharPred('c')));
		List<Integer> finStates01 = new LinkedList<Integer>();
		finStates01.add(1);
		mySFA01 = SFA.MkSFA(transitions01, 0, finStates01, ba);
	}
	
	@AfterClass
	public static void afterClass() throws Exception {
	}
	
	public static boolean CheckOutputInclusion(SFT<CharPred, CharFunc, Character> given, SFA<CharPred, Character> desired) 
			throws Exception {
		SFA<CharPred, Character> output = given.getOutputSFA(ba); 
		return output.includedIn(desired, ba);
	}
	
	@Test
	public void testRepairTransducer() throws Exception {
		
		if (!CheckOutputInclusion(mySFT10, mySFA01)) { 
			// call to repair function 
			// mySFT10.repair(mySFA00) 
			
			SFT<CharPred, CharFunc, Character> repairedSFT10 = mySFT10.composeWith(mySFT12, ba);
			SFA<CharPred, Character> outputSFT10 = (repairedSFT10).getOutputSFA(ba);
			// System.out.println(repairedSFT10.toString());
			assertTrue(outputSFT10.includedIn(mySFA01, ba));
		} 
	}
	
	public static String callSolver(String regex1, String regex2, int[] fraction) throws IOException {
		ProcessBuilder pb = new ProcessBuilder();
		// replace w/ your Python path
		pb.command("/Users/anvaygrover/anaconda3/bin/python3", "solver.py", regex1, regex2, Integer.toString(fraction[0]), Integer.toString(fraction[1]));
		pb.directory(new File("../../regexToDFA/src"));
		pb.redirectErrorStream(true);
		Process p = pb.start(); // throws Exception
		
		BufferedReader reader = new BufferedReader(new InputStreamReader(p.getInputStream()));
		StringBuilder builder = new StringBuilder();
		String line = null;
		while ((line = reader.readLine()) != null) {
			builder.append(line);
			builder.append("\n");
		}
		String result = builder.toString();
		
		return result;
	}
	
	public static String formatSFAForSolver(SFA<CharPred, Character> aut) throws Exception {
		Collection<SFAMove<CharPred, Character>> transitions = aut.getTransitions();
		Collection<Integer> finalStates = aut.getFinalStates();
		StringBuilder sb = new StringBuilder();
		
		for (Move<CharPred, Character> transition : transitions) {
			sb.append(transition.from + " ");
			sb.append(transition.to + " ");
			int pred = (int) transition.getWitness(ba);		// throws TimeoutException
			sb.append(pred + " " + pred + "\n"); 	
		}
		
		for (Integer state : finalStates) {
			sb.append(":acc" + " " + state + "\n");
		}	
		
		return sb.toString();
	}
	
	// Returns state denoted by input string as an integer
	// TODO: rename
	public static String getIntFromStateStr(String str) {
		int closingQuote = str.lastIndexOf('"');
		// System.out.println(str + ": " + closingQuote);
		String stateStr = str.substring(1, closingQuote);
		return stateStr;
	}
	
	public static String[] getInputs(String str) {
		String[] inputStrs = str.split("-");
		return inputStrs;	// For input: each string in the array should have 1 char
	}
	
	public static String[] getOutputs(String str) {
		String[] outputStrs = str.split("-");
		String[] outputs = new String[outputStrs.length];
		
		for (int i = 0; i < outputStrs.length; i++) {
			String currStr = outputStrs[i];
			String[] strs = currStr.split(";");
			
			StringBuilder buildOutput = new StringBuilder();
			for (int j = 0; j < strs.length; j++) {
				buildOutput.append(strs[j]);
			}
			outputs[i] = buildOutput.toString();
		}
		
		return outputs;
	}
	
	// Construct SFT from string output of solver
	public static SFT<CharPred, CharFunc, Character> parseTransducer(String transducer) throws Exception {
		List<SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		Scanner scanner = new Scanner(transducer);
		
		HashMap<String, Integer> stateToState = new HashMap<String, Integer>();
		int stateCounterSFT = 0;
		
		scanner.nextLine(); 		// digraph
		while (scanner.hasNextLine()) {
			String line = scanner.nextLine();
			line = line.trim();
			// System.out.println(line);
			
			if (!line.contains("->") && !line.contains("node") && !line.contains("}")) {
				String[] splitStr = line.split(" ", 2);
				String stateStr = splitStr[0];
				stateStr = getIntFromStateStr(stateStr);
				stateToState.put(stateStr, stateCounterSFT);
				stateCounterSFT++;
				// System.out.println(stateToState.toString());
							
			} else if (line.contains("->") && !line.contains("node")) {
				// TODO
				String[] transitionStr = line.split(" ", 4);
				String fromStr = transitionStr[0];
				String toStr = transitionStr[2];
				fromStr = getIntFromStateStr(fromStr);
				toStr = getIntFromStateStr(toStr);
				
				// SFT from and to states
				int fromState = stateToState.get(fromStr);
				int toState = stateToState.get(toStr);
				
				String label = transitionStr[transitionStr.length - 1];
				int openingQuote = label.indexOf('"');
				int closingQuote = label.lastIndexOf('"');
				String transition = label.substring(openingQuote + 1, closingQuote);
				String[] inputOutput = transition.split(" / ", -1); // intputOutput should have length 2
				
				// get input char(s)
				String[] inputs = getInputs(inputOutput[0]);
				
				// get output char(s)
				String[] outputs = getOutputs(inputOutput[1]);
				
				// make transitions
				for (int i = 0; i < inputs.length; i++) {
					for (int j = 0; j < outputs.length; j++) {
						// input char
						CharPred input = new CharPred(inputs[i].charAt(0));
						
						// output char(s)
						List<CharFunc> output = new ArrayList<CharFunc>();
						String outputStr = outputs[i];
						for (int k = 0; k < outputStr.length(); k++) {
							// System.out.println(outputStr.charAt(k));
							output.add(new CharConstant(outputStr.charAt(k)));
						}
						
						transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(fromState, toState, input, output));		
					}
				}
			}				
		}
		
		scanner.close();
		Map<Integer, Set<List<Character>>> finStates = new HashMap<Integer, Set<List<Character>>>();
		finStates.put(1, new HashSet<List<Character>>());		// TODO: fix
		SFT<CharPred, CharFunc, Character> mySFT = SFT.MkSFT(transitions, 1, finStates, ba);
		System.out.println(mySFT.toString());
		return mySFT;
	}
	
	@Test
	public void callSolverTest() throws IOException {
		String regex1 = "a+";
		String regex2 = "ab+";
		int[] fraction = new int[]{1, 1};
		
		String transducer = callSolver(regex1, regex2, fraction);
		System.out.println(transducer);
		assertTrue(true);
	}
	
	@Test
	public void formatSFAForSolverTest() throws Exception {
		String formatted = formatSFAForSolver(mySFA01);
		System.out.println(formatted);
	}
	
	@Test
	public void parserTest() throws Exception {
		String regex1 = "a+";
		String regex2 = "ab+";
		int[] fraction = new int[]{1, 1};
		
		String result = callSolver(regex1, regex2, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseTransducer(result);
	}
	
	@Test
	public void SFTtoDotTest() throws Exception {
		System.out.println(mySFT10.toDotString(ba));
	}
	
	/* 
	 * Using (.+\".+\".+)+ produces a very large transducer
	 */
	@Test
	public void escapeQuotes() throws IOException {
		String regex1 = "(a+\"a+\"a+)+";
		String regex2 = "(a+\\\\\"a+\\\\\"a+)+";
		int[] fraction = new int[]{2, 5};
		
		String transducer = callSolver(regex1, regex2, fraction);
		// System.out.println(transducer);
		
		
		
		String longExample = "abba\"abbaba\"ababba\"abaa\"aa";
		regex1 = "((a|b)*\"(a|b)*\"(a|b)*)*";
		regex2 = "((a|b)*\\\\\"(a|b)*\\\\\"(a|b)*)*";
		fraction = new int[]{1, 1};
	}
	
	/* 
	 * GetTags: extracts from a given stream of characters all sub-streams 
	 * of the form <x>, where x != '<'. [POPL'12]
	 * 
	 * "<<s><<>><f><t" goes to "<s><>><f>"
	 * 
	 */
	@Test
	public void getTags() throws IOException {
		String regex1 = "<<s><<>><f><t>";
		String regex2 = "(<((a-z)|>)>)*";
		int[] fraction = new int[]{1, 1};
		
		String transducer = callSolver(regex1, regex2, fraction);
	}
	
	/*
	 * Assumes balanced brackets
	 * 
	 * Challenges: coming up with regexes and edit-distance to give to solver
	 * Question: specifying arbitrary characters
	 */
	@Test
	public void escapeBrackets() throws IOException {
		String regex1 = "(a*<a*>a*)+";
		String regex2 = "(a*&lt;a*&gt;a*)+";
		int[] fraction = new int[]{4, 1};
		
		String transducer = callSolver(regex1, regex2, fraction);
		// System.out.println(transducer);
	}
	
}




