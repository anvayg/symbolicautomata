package SFT;

import org.junit.Test;
import org.sat4j.specs.TimeoutException;
import org.junit.BeforeClass;
import org.junit.AfterClass;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;

import java.util.List;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Collection;
import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.Scanner;
import java.util.HashMap;

import theory.BooleanAlgebraSubst;
import theory.characters.*;
import transducers.sft.SFT;
import transducers.sft.SFTMove;
import transducers.sft.SFTInputMove;
import transducers.sft.SFTEpsilon;
import transducers.sft.SFTProduct;
import transducers.sft.SFTProductInputMove;
import utilities.Pair;
import utilities.Triple;
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
	
	private static UnaryCharIntervalSolver ba = new UnaryCharIntervalSolver();
	
	private static SFT<CharPred, CharFunc, Character> mySFT10;
	private static SFT<CharPred, CharFunc, Character> mySFT11;
	private static SFT<CharPred, CharFunc, Character> mySFT12;
	private static SFT<CharPred, CharFunc, Character> mySFT13;
	private static SFT<CharPred, CharFunc, Character> mySFT14;
	private static SFT<CharPred, CharFunc, Character> mySFT15;
	private static SFT<CharPred, CharFunc, Character> mySFT16;
	private static SFT<CharPred, CharFunc, Character> mySFT17;
	private static SFT<CharPred, CharFunc, Character> mySFT18;
	private static SFT<CharPred, CharFunc, Character> mySFT19;
	private static SFT<CharPred, CharFunc, Character> mySFT20;
	private static SFT<CharPred, CharFunc, Character> mySFT21;
	private static SFT<CharPred, CharFunc, Character> mySFT22;
	private static SFA<CharPred, Character> mySFA00;
	private static SFA<CharPred, Character> mySFA01;
	private static SFA<CharPred, Character> mySFA02;
	private static SFA<CharPred, Character> mySFA03;
	private static SFA<CharPred, Character> mySFA04;
	private static SFA<CharPred, Character> mySFA05;
	private static SFA<CharPred, Character> mySFA06;
	private static SFA<CharPred, Character> mySFA07;
	private static SFA<CharPred, Character> mySFA08;
	private static SFA<CharPred, Character> mySFA09;
	private static SFA<CharPred, Character> mySFA101;
	private static SFA<CharPred, Character> mySFA102;
	private static SFA<CharPred, Character> mySFA103;
	
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
		
		// SFT1.3: escapequotes_buggy
		List<SFTMove<CharPred, CharFunc, Character>> transitions13 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output131 = new ArrayList<CharFunc>();
		output131.add(new CharConstant('a'));
		transitions13.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('a'), output131));
		List<CharFunc> output132 = new ArrayList<CharFunc>();
		output132.add(new CharConstant('\\'));
		output132.add(new CharConstant('\''));
		transitions13.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('\''), output132));
		List<CharFunc> output133 = new ArrayList<CharFunc>();
		output133.add(new CharConstant('\\'));
		output133.add(new CharConstant('\"'));
		transitions13.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('\"'), output133));
		List<CharFunc> output134 = new ArrayList<CharFunc>();
		output134.add(new CharConstant('\\'));
		output134.add(new CharConstant('\\'));
		transitions13.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, new CharPred('\\'), output134));
		List<CharFunc> output135 = new ArrayList<CharFunc>();
		output135.add(new CharConstant('\\'));
		output135.add(new CharConstant('\\'));
		transitions13.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred('\\'), output135)); // bug here
		List<CharFunc> output136 = new ArrayList<CharFunc>();
		output136.add(new CharConstant('a'));
		transitions13.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred('a'), output136));
		List<CharFunc> output137 = new ArrayList<CharFunc>();
		output137.add(new CharConstant('\''));
		transitions13.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred('\''), output137));
		List<CharFunc> output138 = new ArrayList<CharFunc>();
		output138.add(new CharConstant('\"'));
		transitions13.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred('\"'), output138));
		Map<Integer, Set<List<Character>>> finStatesAndTails13 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails13.put(0, new HashSet<List<Character>>());
		finStatesAndTails13.put(1, new HashSet<List<Character>>());
		mySFT13 = SFT.MkSFT(transitions13, 0, finStatesAndTails13, ba);
		
		// SFT1.4: escapequotes
		List<SFTMove<CharPred, CharFunc, Character>> transitions14 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output141 = new ArrayList<CharFunc>();
		output141.add(new CharConstant('a'));
		transitions14.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('a'), output141));
		List<CharFunc> output142 = new ArrayList<CharFunc>();
		output142.add(new CharConstant('\\'));
		output142.add(new CharConstant('\''));
		transitions14.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('\''), output142));
		List<CharFunc> output143 = new ArrayList<CharFunc>();
		output143.add(new CharConstant('\\'));
		output143.add(new CharConstant('\"'));
		transitions14.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('\"'), output143));
		List<CharFunc> output144 = new ArrayList<CharFunc>();
		output144.add(new CharConstant('\\'));
		output144.add(new CharConstant('\\'));
		transitions14.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, new CharPred('\\'), output144));
		List<CharFunc> output145 = new ArrayList<CharFunc>();
		output145.add(new CharConstant('\\'));
		transitions14.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred('\\'), output145)); 
		List<CharFunc> output146 = new ArrayList<CharFunc>();
		output146.add(new CharConstant('a'));
		transitions14.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred('a'), output146));
		List<CharFunc> output147 = new ArrayList<CharFunc>();
		output147.add(new CharConstant('\''));
		transitions14.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred('\''), output147));
		List<CharFunc> output148 = new ArrayList<CharFunc>();
		output148.add(new CharConstant('\"'));
		transitions14.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, new CharPred('\"'), output148));
		Map<Integer, Set<List<Character>>> finStatesAndTails14 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails14.put(0, new HashSet<List<Character>>());
		finStatesAndTails14.put(1, new HashSet<List<Character>>());
		mySFT14 = SFT.MkSFT(transitions14, 0, finStatesAndTails14, ba);
		
		// SFT1.5: SFT that reads ab* and outputs ab*
		List<SFTMove<CharPred, CharFunc, Character>> transitions15 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output151 = new ArrayList<CharFunc>();
		output151.add(new CharConstant('a'));
		transitions15.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 2, new CharPred('a'), output151));
		List<CharFunc> output152 = new ArrayList<CharFunc>();
		output152.add(new CharConstant('b'));
		transitions15.add(new SFTInputMove<CharPred, CharFunc, Character>(2, 2, new CharPred('b'), output152));
		Map<Integer, Set<List<Character>>> finStatesAndTails15 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails15.put(2, new HashSet<List<Character>>());
		mySFT15 = SFT.MkSFT(transitions15, 1, finStatesAndTails15, ba);
		
		// SFT1.6: escapequotes_buggy
		// https://rise4fun.com/Bek/escapequotes_buggy
		List<SFTMove<CharPred, CharFunc, Character>> transitions16 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output161 = new ArrayList<CharFunc>();
		output161.add(CharOffset.IDENTITY);
		CharPred quotes = ba.MkOr(new CharPred('\''), new CharPred('\"'));
		CharPred backslash = new CharPred('\\');
		CharPred notQuotesAndBackslash = ba.MkAnd(ba.MkNot(quotes), ba.MkNot(backslash));
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, notQuotesAndBackslash, output161));
		List<CharFunc> output162 = new ArrayList<CharFunc>();
		output162.add(new CharConstant('\\'));
		output162.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, quotes, output162));
		List<CharFunc> output163 = new ArrayList<CharFunc>();
		output163.add(CharOffset.IDENTITY);
		output163.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, backslash, output163));
		List<CharFunc> output164 = new ArrayList<CharFunc>();
		output164.add(CharOffset.IDENTITY);
		output164.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, backslash, output164)); // bug here
		List<CharFunc> output165 = new ArrayList<CharFunc>();
		output165.add(CharOffset.IDENTITY);
		transitions16.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, ba.MkNot(backslash), output165));
		Map<Integer, Set<List<Character>>> finStatesAndTails16 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails16.put(0, new HashSet<List<Character>>());
		// finStatesAndTails16.put(1, new HashSet<List<Character>>());
		mySFT16 = SFT.MkSFT(transitions16, 0, finStatesAndTails16, ba);
		
		// SFT1.7: escapequotes_correct
		List<SFTMove<CharPred, CharFunc, Character>> transitions17 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output171 = new ArrayList<CharFunc>();
		output171.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, notQuotesAndBackslash, output171));
		List<CharFunc> output172 = new ArrayList<CharFunc>();
		output172.add(new CharConstant('\\'));
		output172.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, quotes, output172));
		List<CharFunc> output173 = new ArrayList<CharFunc>();
		output173.add(CharOffset.IDENTITY); // corrected
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 1, backslash, output173));
		List<CharFunc> output174 = new ArrayList<CharFunc>();
		output174.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, backslash, output174)); // corrected
		List<CharFunc> output175 = new ArrayList<CharFunc>();
		output175.add(CharOffset.IDENTITY);
		transitions17.add(new SFTInputMove<CharPred, CharFunc, Character>(1, 0, ba.MkNot(backslash), output175));
		Map<Integer, Set<List<Character>>> finStatesAndTails17 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails17.put(0, new HashSet<List<Character>>());
		// finStatesAndTails17.put(1, new HashSet<List<Character>>());
		mySFT17 = SFT.MkSFT(transitions17, 0, finStatesAndTails17, ba);
		
		// SFT1.8: SFT that deletes spaces
		List<SFTMove<CharPred, CharFunc, Character>> transitions18 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output181 = new ArrayList<CharFunc>();
		output181.add(CharOffset.IDENTITY);
		transitions18.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.ALPHA_NUM, output181));
		List<CharFunc> output182 = new ArrayList<CharFunc>();
		transitions18.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.SPACES, output182));
		Map<Integer, Set<List<Character>>> finStatesAndTails18 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails18.put(0, new HashSet<List<Character>>());
		mySFT18 = SFT.MkSFT(transitions18, 0, finStatesAndTails18, ba);
		
		// SFT1.9: SFT that should delete spaces but does not
		List<SFTMove<CharPred, CharFunc, Character>> transitions19 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output191 = new ArrayList<CharFunc>();
		output191.add(CharOffset.IDENTITY);
		transitions19.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.ALPHA_NUM, output191));
		List<CharFunc> output192 = new ArrayList<CharFunc>();
		output192.add(CharOffset.IDENTITY);
		transitions19.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, StdCharPred.SPACES, output192));
		Map<Integer, Set<List<Character>>> finStatesAndTails19 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails19.put(0, new HashSet<List<Character>>());
		mySFT19 = SFT.MkSFT(transitions19, 0, finStatesAndTails19, ba);
		
		// SFT2.0: escape html broken
		List<SFTMove<CharPred, CharFunc, Character>> transitions20 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output201 = new ArrayList<CharFunc>();
		output201.add(new CharConstant('&'));
		output201.add(new CharConstant('l'));
		output201.add(new CharConstant('t'));
		output201.add(new CharConstant(';'));
		transitions20.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('<'), output201));
		List<CharFunc> output202 = new ArrayList<CharFunc>();
		output202.add(new CharConstant('&'));
		output202.add(new CharConstant('g'));
		output202.add(new CharConstant('t'));
		output202.add(new CharConstant(';'));
		transitions20.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('>'), output202));
		List<CharFunc> output203 = new ArrayList<CharFunc>();
		output203.add(new CharConstant('&'));
		output203.add(new CharConstant('q'));
		output203.add(new CharConstant('u'));
		output203.add(new CharConstant('o'));
		output203.add(new CharConstant('t'));
		output203.add(new CharConstant(';'));
		transitions20.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('\t'), output203)); // bug
		Map<Integer, Set<List<Character>>> finStatesAndTails20 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails20.put(0, new HashSet<List<Character>>());
		mySFT20 = SFT.MkSFT(transitions20, 0, finStatesAndTails20, ba);
		
		// SFT2.1: escape html 
		List<SFTMove<CharPred, CharFunc, Character>> transitions21 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output211 = new ArrayList<CharFunc>();
		output211.add(new CharConstant('&'));
		output211.add(new CharConstant('l'));
		output211.add(new CharConstant('t'));
		output211.add(new CharConstant(';'));
		transitions21.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('<'), output211));
		List<CharFunc> output212 = new ArrayList<CharFunc>();
		output212.add(new CharConstant('&'));
		output212.add(new CharConstant('g'));
		output212.add(new CharConstant('t'));
		output212.add(new CharConstant(';'));
		transitions21.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('>'), output212));
		List<CharFunc> output213 = new ArrayList<CharFunc>();
		output213.add(new CharConstant('&'));
		output213.add(new CharConstant('q'));
		output213.add(new CharConstant('u'));
		output213.add(new CharConstant('o'));
		output213.add(new CharConstant('t'));
		output213.add(new CharConstant(';'));
		transitions21.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('\"'), output213)); 
		Map<Integer, Set<List<Character>>> finStatesAndTails21 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails21.put(0, new HashSet<List<Character>>());
		mySFT21 = SFT.MkSFT(transitions21, 0, finStatesAndTails21, ba);
		
		// SFT2.1: escape html 
		List<SFTMove<CharPred, CharFunc, Character>> transitions22 = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		List<CharFunc> output221 = new ArrayList<CharFunc>();
		output221.add(new CharConstant('&'));
		output221.add(new CharConstant('l'));
		output221.add(new CharConstant('t'));
		output221.add(new CharConstant(';'));
		transitions22.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('<'), output221));
		List<CharFunc> output222 = new ArrayList<CharFunc>();
		output222.add(new CharConstant('&'));
		output222.add(new CharConstant('l')); // bug
		output222.add(new CharConstant('t'));
		output222.add(new CharConstant(';'));
		transitions22.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('>'), output222));
		List<CharFunc> output223 = new ArrayList<CharFunc>();
		output223.add(new CharConstant('&'));
		output223.add(new CharConstant('q'));
		output223.add(new CharConstant('u'));
		output223.add(new CharConstant('o'));
		output223.add(new CharConstant('t'));
		output223.add(new CharConstant(';'));
		transitions22.add(new SFTInputMove<CharPred, CharFunc, Character>(0, 0, new CharPred('\"'), output223)); 
		Map<Integer, Set<List<Character>>> finStatesAndTails22 = new HashMap<Integer, Set<List<Character>>>();
		finStatesAndTails22.put(0, new HashSet<List<Character>>());
		mySFT22 = SFT.MkSFT(transitions22, 0, finStatesAndTails22, ba);
		
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
		
		// SFA0.2: SFA that reads ab*
		List<SFAMove<CharPred, Character>> transitions02 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions02.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('a')));
		transitions02.add(new SFAInputMove<CharPred, Character>(1, 1, new CharPred('b')));
		List<Integer> finStates02 = new LinkedList<Integer>();
		finStates02.add(1);
		mySFA02 = SFA.MkSFA(transitions02, 0, finStates02, ba);
		
		// SFA0.3: SFA that reads ALPHA.ALPHANUM*
		List<SFAMove<CharPred, Character>> transitions03 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions03.add(new SFAInputMove<CharPred, Character>(0, 1, StdCharPred.ALPHA));
		transitions03.add(new SFAInputMove<CharPred, Character>(1, 1, StdCharPred.LOWER_ALPHA));
		List<Integer> finStates03 = new LinkedList<Integer>();
		finStates03.add(1);
		mySFA03 = SFA.MkSFA(transitions03, 0, finStates03, ba);
		
		// SFA0.4: SFA that reads ALPHA.ALPHANUM*
		List<SFAMove<CharPred, Character>> transitions04 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions04.add(new SFAInputMove<CharPred, Character>(0, 1, StdCharPred.NUM));
		transitions04.add(new SFAInputMove<CharPred, Character>(1, 1, StdCharPred.ALPHA_NUM));
		List<Integer> finStates04 = new LinkedList<Integer>();
		finStates04.add(1);
		mySFA04 = SFA.MkSFA(transitions04, 0, finStates04, ba);
		
		// SFA0.5: HTML script tags
		List<SFAMove<CharPred, Character>> transitions05 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions05.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('<')));
		transitions05.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('s')));
		transitions05.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('>')));
		transitions05.add(new SFAInputMove<CharPred, Character>(3, 4, new CharPred('<')));
		CharPred notLt = ba.MkNot(new CharPred('<'));
		transitions05.add(new SFAInputMove<CharPred, Character>(3, 3, notLt));
		transitions05.add(new SFAInputMove<CharPred, Character>(4, 5, new CharPred('\\')));
		CharPred notBackslash = ba.MkNot(new CharPred('\\'));
		transitions05.add(new SFAInputMove<CharPred, Character>(4, 3, notBackslash));
		transitions05.add(new SFAInputMove<CharPred, Character>(5, 6, new CharPred('s')));
		transitions05.add(new SFAInputMove<CharPred, Character>(6, 7, new CharPred('>')));
		List<Integer> finStates05 = new LinkedList<Integer>();
		finStates05.add(7);
		mySFA05 = SFA.MkSFA(transitions05, 0, finStates05, ba);
		
		// SFA0.6: HTML no script tags
		List<SFAMove<CharPred, Character>> transitions06 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions06.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('<')));
		transitions06.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('s')));
		transitions06.add(new SFAInputMove<CharPred, Character>(1, 1, new CharPred('\\')));
		transitions06.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('>')));
		CharPred notGt = ba.MkNot(new CharPred('>'));
		CharPred notBackslashOrS = ba.MkNot(ba.MkOr(notBackslash, new CharPred('s')));
		transitions06.add(new SFAInputMove<CharPred, Character>(0, 0, notLt));
		transitions06.add(new SFAInputMove<CharPred, Character>(1, 0, notBackslashOrS));
		transitions06.add(new SFAInputMove<CharPred, Character>(2, 0, notGt));
		List<Integer> finStates06 = new LinkedList<Integer>();
		finStates06.add(0); // fix
		mySFA06 = SFA.MkSFA(transitions06, 0, finStates06, ba);
		
		// DOS carriage return
		List<SFAMove<CharPred, Character>> transitions07 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions07.add(new SFAInputMove<CharPred, Character>(0, 0, StdCharPred.ALPHA));
		transitions07.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('\\')));
		transitions07.add(new SFAInputMove<CharPred, Character>(1, 2, new CharPred('r')));
		transitions07.add(new SFAInputMove<CharPred, Character>(2, 3, new CharPred('\\')));
		transitions07.add(new SFAInputMove<CharPred, Character>(3, 0, new CharPred('n')));
		List<Integer> finStates07 = new LinkedList<Integer>();
		finStates07.add(0);
		mySFA07 = SFA.MkSFA(transitions07, 0, finStates07, ba);
		
		// Unix carriage return
		List<SFAMove<CharPred, Character>> transitions08 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions08.add(new SFAInputMove<CharPred, Character>(0, 0, StdCharPred.ALPHA));
		transitions08.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('\\')));
		transitions08.add(new SFAInputMove<CharPred, Character>(1, 0, new CharPred('n')));
		List<Integer> finStates08 = new LinkedList<Integer>();
		finStates08.add(0);
		mySFA08 = SFA.MkSFA(transitions08, 0, finStates08, ba);
		
		// CSV file separated by comma
		List<SFAMove<CharPred, Character>> transitions09 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions09.add(new SFAInputMove<CharPred, Character>(0, 0, StdCharPred.ALPHA));
		transitions09.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred(',')));
		transitions09.add(new SFAInputMove<CharPred, Character>(1, 0, StdCharPred.ALPHA));
		List<Integer> finStates09 = new LinkedList<Integer>();
		finStates09.add(0);
		mySFA09 = SFA.MkSFA(transitions09, 0, finStates09, ba);
		
		/**
		 * CSV file separated by period
		 */
		List<SFAMove<CharPred, Character>> transitions101 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions101.add(new SFAInputMove<CharPred, Character>(0, 0, StdCharPred.ALPHA));
		transitions101.add(new SFAInputMove<CharPred, Character>(0, 1, new CharPred('.')));
		transitions101.add(new SFAInputMove<CharPred, Character>(1, 0, StdCharPred.ALPHA));
		List<Integer> finStates101 = new LinkedList<Integer>();
		finStates101.add(0);
		mySFA101 = SFA.MkSFA(transitions101, 0, finStates101, ba);
		
		/**
		 * 10 digit phone nunber
		 */
		List<SFAMove<CharPred, Character>> transitions102 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions102.add(new SFAInputMove<CharPred, Character>(0, 1, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(1, 2, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(2, 3, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(3, 4, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(4, 5, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(5, 6, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(6, 7, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(7, 8, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(8, 9, StdCharPred.NUM));
		transitions102.add(new SFAInputMove<CharPred, Character>(9, 10, StdCharPred.NUM));
		List<Integer> finStates102 = new LinkedList<Integer>();
		finStates102.add(10);
		mySFA102 = SFA.MkSFA(transitions102, 0, finStates102, ba);
		
		/**
		 * 10 digit phone nunber formatted with hyphens
		 */
		List<SFAMove<CharPred, Character>> transitions103 = new LinkedList<SFAMove<CharPred, Character>>();
		transitions103.add(new SFAInputMove<CharPred, Character>(0, 1, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(1, 2, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(2, 3, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(3, 4, new CharPred('.')));
		transitions103.add(new SFAInputMove<CharPred, Character>(4, 5, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(5, 6, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(6, 7, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(7, 8, new CharPred('.')));
		transitions103.add(new SFAInputMove<CharPred, Character>(8, 9, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(9, 10, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(10, 11, StdCharPred.NUM));
		transitions103.add(new SFAInputMove<CharPred, Character>(11, 12, StdCharPred.NUM));
		List<Integer> finStates103 = new LinkedList<Integer>();
		finStates103.add(12);
		mySFA103 = SFA.MkSFA(transitions103, 0, finStates103, ba);
	}
	
	@AfterClass
	public static void afterClass() throws Exception {
	}
	
	/**
	 * Auxiliary recursive function for generateExamplesSFT
	 * 
	 * @throws TimeoutException 
	 */
	public static Set<Pair<String, String>> generateExamplesSFTRec(SFT<CharPred, CharFunc, Character> transducer, 
			Pair<String, String> run, Set<SFTMove<CharPred, CharFunc, Character>> taken, Integer state) throws TimeoutException { // FIX RETURN TYPE
		Set<Pair<String, String>> examples = new HashSet<Pair<String, String>>();
		if (transducer.getFinalStatesAndTails().containsKey(state)) {
			examples.add(run);
			return examples;
		}
		
		for (SFTInputMove<CharPred, CharFunc, Character> transition: transducer.getInputMovesFrom(state)) {
			if (taken.contains(transition)) continue;
			
			Character input = ba.generateWitness(transition.guard);
			List<CharFunc> outputFuncs = transition.outputFunctions;
			Character output = null;
			for (CharFunc func : outputFuncs) {
				CharPred phi = ba.getRestrictedOutput(transition.guard, func);
				output = ba.generateWitness(phi);
			}
			
			// Add input and output to run
			run.first.concat(String.valueOf(input));
			run.second.concat(String.valueOf(output));
			
			// Recursive call
			if (!taken.contains(transition)) {
				taken.add(transition);
				examples.addAll(generateExamplesSFTRec(transducer, run, taken, transition.to));
			}
		}
		
		return examples; 
	}
	
	/**
	 * Generates set of example runs on an SFT
	 * 
	 * @throws TimeoutException 
	 */
	public static Set<Pair<String, String>> generateExamplesSFT(SFT<CharPred, CharFunc, Character> transducer) throws TimeoutException {
		Pair<String, String> run = new Pair<String, String>("", "");
		Set<SFTMove<CharPred, CharFunc, Character>> taken = new HashSet<SFTMove<CharPred, CharFunc, Character>>();
		return generateExamplesSFTRec(transducer, run, taken, transducer.getInitialState());
	}
	
	
	/**
	 * Constructs an identity transducer from aut
	 * 
	 * @throws TimeoutException
	 */
	public static SFT<CharPred, CharFunc, Character> MkIdentitySFT(SFA<CharPred, Character> aut) throws TimeoutException {
		Collection <SFTMove<CharPred, CharFunc, Character>> transitions = new LinkedList<SFTMove<CharPred, CharFunc, Character>>();
		
		for (Integer state : aut.getStates()) {
			Collection<SFAInputMove<CharPred, Character>> stateTransitions = aut.getInputMovesFrom(state);
			for (SFAInputMove<CharPred, Character> transition : stateTransitions) {
				List<CharFunc> output = new ArrayList<CharFunc>();
				output.add(CharOffset.IDENTITY);
				transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(state, transition.to, transition.guard, output));
			}
		}
		Integer init = aut.getInitialState();
		Collection<Integer> autFinalStates = aut.getFinalStates();
		Map<Integer, Set<List<Character>>> finStates = new HashMap<Integer, Set<List<Character>>>();
		for (Integer state : autFinalStates) {
			finStates.put(state, new HashSet<List<Character>>());
		}
		
		return SFT.MkSFT(transitions, init, finStates, ba);
	}
	
	@Test
	public void testMkIdentitySFT() throws TimeoutException {
		SFT<CharPred, CharFunc, Character> idSFT02 = MkIdentitySFT(mySFA02);
		assertTrue(idSFT02.decide1equality(mySFT15, ba));
	}
	
	// Move to SFT
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
	
	@Test
	public void testGetOutputSFAMultiple() throws TimeoutException {
		SFA<CharPred, Character> outputSFT11 = mySFT11.getOverapproxOutputSFA(ba);
		assertTrue(outputSFT11.includedIn(mySFA00, ba));
	}
	
	@Test
	public void testMkUnionSFT() throws TimeoutException {
		SFT<CharPred, CharFunc, Character> unionSFT = SFT.union(mySFT12, mySFT15, ba);
		SFA<CharPred, Character> output = unionSFT.getOverapproxOutputSFA(ba);
		assertTrue(mySFA02.includedIn(output, ba));
	}
	
	@Test
	public void testMkFiniteSFA() throws Exception {
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(mySFA03, mySFA04, ba);
		SFA<CharPred, Character> finSFA03 = triple.first;
		SFA<CharPred, Character> finSFA04 = triple.second;
		
		int[] fraction = new int[]{1, 1};
		SFT<CharPred, CharFunc, Character> repair = parseTransducer(callSolverSFA(finSFA03, finSFA04, fraction));
		SFT<CharPred, CharFunc, Character> expanded = repair.mintermExpansion(triple.third, ba);
		SFT<CharPred, CharFunc, Character> broken = MkIdentitySFT(mySFA03);
		SFT<CharPred, CharFunc, Character> compose = broken.composeWith(expanded, ba);
		assertTrue(compose.getOverapproxOutputSFA(ba).includedIn(mySFA04, ba));
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
	
	public static String formatSFAForSolver(SFA<CharPred, Character> aut) throws TimeoutException {
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
	
	public static String callSolverSFA(SFA<CharPred, Character> source, SFA<CharPred, Character> target, int[] fraction) throws Exception {
		String dfa1 = formatSFAForSolver(source);
		String dfa2 = formatSFAForSolver(target);
		
		ProcessBuilder pb = new ProcessBuilder();
		// replace w/ your Python path
		pb.command("/Users/anvaygrover/anaconda3/bin/python3", "solver_DFA.py");
		pb.directory(new File("../../regexToDFA/src"));
		pb.redirectErrorStream(true);
		Process p = pb.start(); // throws Exception
		
		// write to process' stdin
		OutputStream stdin = p.getOutputStream();
		InputStream stdout = p.getInputStream();
		BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(stdin));
		writer.write(dfa1);
		writer.write("\n");
		writer.write(dfa2);
		writer.write("\n");
		writer.write(Integer.toString(fraction[0]) + " " + Integer.toString(fraction[1]));
		writer.write("\n");
		writer.flush();
		writer.close();
		
		// read from process' stdout
		BufferedReader reader = new BufferedReader(new InputStreamReader(stdout));
		StringBuilder builder = new StringBuilder();
		String line = null;
		while ((line = reader.readLine()) != null) {
			builder.append(line);
			builder.append("\n");
		}
        
        String result = builder.toString();
		return result;
	}
	
	// Returns state denoted by input string as an integer
	// TODO: rename
	public static String getIntFromStateStr(String str) {
		int closingQuote = str.lastIndexOf('\"');
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
	public static SFT<CharPred, CharFunc, Character> parseTransducer(String transducer) throws TimeoutException {
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
		finStates.put(stateCounterSFT - 1, new HashSet<List<Character>>());		// TODO: fix
		SFT<CharPred, CharFunc, Character> mySFT = SFT.MkSFT(transitions, 0, finStates, ba);
		// System.out.println(mySFT.toString());
		return mySFT;
	}
	
	// Construct SFT from string output of solver
	public static SFT<CharPred, CharFunc, Character> parseWithMinterms(String transducer) throws TimeoutException {
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
				if (line.isEmpty()) continue;
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
						char inputChar = inputs[i].charAt(0);
						CharPred input = new CharPred(inputChar);
						
						// output char(s)
						List<CharFunc> output = new ArrayList<CharFunc>();
						String outputStr = outputs[i];
						for (int k = 0; k < outputStr.length(); k++) {
							// System.out.println(outputStr.charAt(k));
							char outputChar = outputStr.charAt(k);
							if (outputChar == inputChar) {
								output.add(CharOffset.IDENTITY); // identity if input/output minterms are the same
							} else {
							output.add(new CharConstant(outputStr.charAt(k)));
							}
						}
						transitions.add(new SFTInputMove<CharPred, CharFunc, Character>(fromState, toState, input, output));		
					}
				}
			}				
		}
			
		scanner.close();
		Map<Integer, Set<List<Character>>> finStates = new HashMap<Integer, Set<List<Character>>>();
		finStates.put(stateCounterSFT - 1, new HashSet<List<Character>>());		// TODO: fix
		SFT<CharPred, CharFunc, Character> mySFT = SFT.MkSFT(transitions, 0, finStates, ba);
		// System.out.println(mySFT.toString());
		return mySFT;
	}
	
	public static SFT<CharPred, CharFunc, Character> repair(SFT<CharPred, CharFunc, Character> transducer, SFA<CharPred, Character> target, int[] fraction) throws Exception {
		SFA<CharPred, Character> output = transducer.getOutputSFA(ba);
		SFA<CharPred, Character> badOutput = output.minus(output, ba);
		
		String repairStr = callSolverSFA(badOutput, target, fraction);
		SFT<CharPred, CharFunc, Character> repair = parseTransducer(repairStr);
		
		return repair; 
	}
	
	@Test
	public void callSolverTest() throws IOException {
		String regex1 = "a+";
		String regex2 = "ab+";
		int[] fraction = new int[]{1, 1};
		
		String transducer = callSolver(regex1, regex2, fraction);
		// System.out.println(transducer);
		assertTrue(true);
	}
	
	@Test
	public void callSolverSFATest() throws Exception {
		int[] fraction = new int[]{1, 1};
		
		String transducer = callSolverSFA(mySFA01, mySFA02, fraction);
		// System.out.println("Repair: " + parseTransducer(transducer));
	}
	
	@Test
	public void formatSFAForSolverTest() throws TimeoutException {
		String formatted = formatSFAForSolver(mySFA01);
		// System.out.println(formatted);
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
	public void testEscapeQuotesEndtoEnd() throws Exception {
		// get output languages
		// System.out.println(mySFT16.toDotString(ba));
		SFA<CharPred, Character> outputSFT16 = mySFT16.getOverapproxOutputSFA(ba);
		SFA<CharPred, Character> output = outputSFT16.determinize(ba);
		SFA<CharPred, Character> target = mySFT17.getOverapproxOutputSFA(ba);
		target = target.determinize(ba);
		
		// minterm reduction to finite case
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(output, target, ba);
		// System.out.println(formatSFAForSolver(triple.first));
		// System.out.println(formatSFAForSolver(triple.second));
		// System.out.println(triple.first.toDotString(ba));
		// System.out.println(triple.second.toDotString(ba));
		
		// call solver
		int[] fraction = new int[]{1, 1};
		String repair = callSolverSFA(triple.first, triple.second, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseWithMinterms(repair);
		// System.out.println(transducer.toDotString(ba));	
		SFT<CharPred, CharFunc, Character> expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		// System.out.println(expandedTransducer.toDotString(ba));	
		
		SFT<CharPred, CharFunc, Character> join = mySFT16.composeWith(expandedTransducer, ba);
		// System.out.println(join.toDotString(ba));
		assertTrue(SFT.checkOverapproxOutputInclusion(join, target, ba));
		
		
		// now repair from bad outputs
		SFA<CharPred, Character> badOutput = output.minus(target, ba);
		SFA<CharPred, Character> badOutputMin = badOutput.minimize(ba);
		// System.out.println(badOutput.toDotString(ba));
		SFA<CharPred, Character> goodOutput = outputSFT16.intersectionWith(target, ba);
		triple = SFA.MkFiniteSFA(badOutput, target, ba);
		
		// call solver
		repair = callSolverSFA(triple.first, triple.second, fraction);
		transducer = parseWithMinterms(repair);
		// System.out.println(transducer.toDotString(ba));	
		expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		// System.out.println(expandedTransducer.toDotString(ba));	
		
		SFT<CharPred, CharFunc, Character> idTrans = MkIdentitySFT(goodOutput);
		SFT<CharPred, CharFunc, Character> union = expandedTransducer.unionWith(idTrans, ba);
		join = mySFT16.composeWith(union, ba);
		// System.out.println(join.toDotString(ba));
		assertTrue(SFT.checkOverapproxOutputInclusion(join, target, ba));
	}
	
	@Test
	public void testDeleteSpaces() throws Exception {
		SFA<CharPred, Character> outputSFT19 = mySFT19.getOverapproxOutputSFA(ba);
		SFA<CharPred, Character> output = outputSFT19.determinize(ba);
		SFA<CharPred, Character> target = mySFT18.getOverapproxOutputSFA(ba);
		target = target.determinize(ba);
		// System.out.println(output.toDotString(ba));
		// System.out.println(target.toDotString(ba));
		
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(output, target, ba);
		
		// call solver
		int[] fraction = new int[]{1, 1};
		String repair = callSolverSFA(triple.first, triple.second, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseWithMinterms(repair);
		// System.out.println(transducer.toDotString(ba));	
		SFT<CharPred, CharFunc, Character> expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		// System.out.println(expandedTransducer.toDotString(ba));	
				
		SFT<CharPred, CharFunc, Character> join = mySFT18.composeWith(expandedTransducer, ba);
		// System.out.println(join.toDotString(ba));
		assertTrue(SFT.checkOverapproxOutputInclusion(join, target, ba));
	}
	
	
	public void testRemoveScripts() throws Exception {
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(mySFA05, mySFA06, ba);
		
		// call solver
		int[] fraction = new int[]{1, 1};
		String repair = callSolverSFA(triple.first, triple.second, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseWithMinterms(repair);
		SFT<CharPred, CharFunc, Character> expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		// System.out.println(expandedTransducer.toDotString(ba));
	}
	
	@Test
	public void testDosToUnix() throws Exception {
		
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(mySFA07, mySFA08, ba);
		
		// call solver
		int[] fraction = new int[]{1, 1};
		String repair = callSolverSFA(triple.first, triple.second, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseWithMinterms(repair);
		SFT<CharPred, CharFunc, Character> expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		// System.out.println(expandedTransducer.toDotString(ba));
	}
	
	@Test
	public void testUnixToDos() throws Exception {
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(mySFA08, mySFA07, ba);
		
		// call solver
		int[] fraction = new int[]{1, 1};
		String repair = callSolverSFA(triple.first, triple.second, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseWithMinterms(repair);
		SFT<CharPred, CharFunc, Character> expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		
		assertTrue(SFT.checkOverapproxOutputInclusion(expandedTransducer, mySFA07, ba));
	}
	
	@Test
	public void testCSVSeparators() throws Exception {
		// System.out.println(mySFA09.toDotString(ba));
		// System.out.println(mySFA101.toDotString(ba));
		
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(mySFA09, mySFA101, ba);
		
		// call solver
		int[] fraction = new int[]{1, 1};
		String repair = callSolverSFA(triple.first, triple.second, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseWithMinterms(repair);
		SFT<CharPred, CharFunc, Character> expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		// System.out.println(expandedTransducer.toDotString(ba));
	}
	
	@Test
	public void testFormatPhoneNumbers() throws Exception {
		System.out.println(mySFA102.toDotString(ba));
		System.out.println(mySFA103.toDotString(ba));
		
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(mySFA102, mySFA103, ba);
		
		// call solver
		int[] fraction = new int[]{1, 1};
		String repair = callSolverSFA(triple.first, triple.second, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseWithMinterms(repair);
		SFT<CharPred, CharFunc, Character> expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		System.out.println(expandedTransducer.toDotString(ba));
	}
	
	// Remove as test
	public void testHTMLEscape() throws Exception {
		SFA<CharPred, Character> outputSFT22 = mySFT22.getOverapproxOutputSFA(ba);
		SFA<CharPred, Character> output = outputSFT22.determinize(ba);
		SFA<CharPred, Character> target = mySFT21.getOverapproxOutputSFA(ba);
		// target = target.determinize(ba);
		// System.out.println(outputSFT22.toDotString(ba));
		// System.out.println(target.toDotString(ba));
		
		Triple<SFA<CharPred, Character>, SFA<CharPred, Character>, Map<CharPred, Pair<CharPred, ArrayList<Integer>>>> triple = 
				SFA.MkFiniteSFA(outputSFT22, target, ba);
		
		// call solver
		int[] fraction = new int[]{1, 1};
		String repair = callSolverSFA(triple.first, triple.second, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseWithMinterms(repair);
		// System.out.println(transducer.toDotString(ba));	
		SFT<CharPred, CharFunc, Character> expandedTransducer = transducer.mintermExpansion(triple.third, ba);
		// System.out.println(expandedTransducer.toDotString(ba));	
				
		SFT<CharPred, CharFunc, Character> join = mySFT18.composeWith(expandedTransducer, ba);
		// System.out.println(join.toDotString(ba));
		assertTrue(SFT.checkOverapproxOutputInclusion(join, target, ba));
	}
	
	public void testEscapeQuotes() throws Exception {
		SFA<CharPred, Character> outputSFT13 = mySFT13.getOverapproxOutputSFA(ba); 
		// System.out.println(formatSFAForSolver(outputSFT13));
		// System.out.println(outputSFT13.toDotString(ba));
		
		SFA<CharPred, Character> target = mySFT14.getOverapproxOutputSFA(ba);
		// System.out.println(formatSFAForSolver(target));
		// System.out.println(target.toDotString(ba));
		
		SFA<CharPred, Character> badOutput = outputSFT13.minus(target, ba);
		// System.out.println(formatSFAForSolver(badOutput));
		// System.out.println(badOutput.toDotString(ba));
		
		SFA<CharPred, Character> goodOutput = outputSFT13.intersectionWith(target, ba);
		
		int[] fraction = new int[]{1, 1};
		
//		String repair = callSolverSFA(outputSFT13, target, fraction);
//		SFT<CharPred, CharFunc, Character> transducer = parseTransducer(repair);
//		System.out.println(transducer.toDotString(ba));
		
		String repair = callSolverSFA(badOutput, target, fraction);
		String repairWhole = callSolverSFA(outputSFT13, target, fraction);
		SFT<CharPred, CharFunc, Character> transducer = parseTransducer(repair);
		SFT<CharPred, CharFunc, Character> transducer2 = parseTransducer(repairWhole);
		// System.out.println(transducer.toDotString(ba));
		
		SFA<CharPred, Character> outputRepair = transducer.getOverapproxOutputSFA(ba);
		SFA<CharPred, Character> outputRepairWhole = transducer2.getOverapproxOutputSFA(ba);
				
		SFT<CharPred, CharFunc, Character> idTrans = MkIdentitySFT(goodOutput);
		SFT<CharPred, CharFunc, Character> union = transducer.unionWith(idTrans, ba);
		SFT<CharPred, CharFunc, Character> join = mySFT13.composeWith(union, ba);
		SFA<CharPred, Character> newOutput = join.getOverapproxOutputSFA(ba);
		assertTrue(newOutput.includedIn(target, ba));
	}
	
	/* 
	 * Using (.+\".+\".+)+ produces a very large transducer
	 */
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
	public void escapeBrackets() throws IOException {
		String regex1 = "(a*<a*>a*)+";
		String regex2 = "(a*&lt;a*&gt;a*)+";
		int[] fraction = new int[]{4, 1};
		
		String transducer = callSolver(regex1, regex2, fraction);
		// System.out.println(transducer);
	}
	
}




