// Generated from /Users/amosloverde/Desktop/bonacina/solutore_SAT/src/main/java/org/sat/antlr/org/sat/parser/LogicFormula.g4 by ANTLR 4.13.2
package org.sat.antlr.org.sat.parser;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue", "this-escape"})
public class LogicFormulaParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		NOT=1, AND=2, OR=3, IMPLIES=4, IFF=5, LPAR=6, RPAR=7, TRUE=8, FALSE=9, 
		IDENTIFIER=10, WHITESPACE=11;
	public static final int
		RULE_formula = 0, RULE_biconditional = 1, RULE_implication = 2, RULE_disjunction = 3, 
		RULE_conjunction = 4, RULE_negation = 5, RULE_atom = 6;
	private static String[] makeRuleNames() {
		return new String[] {
			"formula", "biconditional", "implication", "disjunction", "conjunction", 
			"negation", "atom"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, null, null, null, null, null, "'('", "')'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "NOT", "AND", "OR", "IMPLIES", "IFF", "LPAR", "RPAR", "TRUE", "FALSE", 
			"IDENTIFIER", "WHITESPACE"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "LogicFormula.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public LogicFormulaParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class FormulaContext extends ParserRuleContext {
		public BiconditionalContext biconditional() {
			return getRuleContext(BiconditionalContext.class,0);
		}
		public TerminalNode EOF() { return getToken(LogicFormulaParser.EOF, 0); }
		public FormulaContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_formula; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitFormula(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FormulaContext formula() throws RecognitionException {
		FormulaContext _localctx = new FormulaContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_formula);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(14);
			biconditional();
			setState(15);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class BiconditionalContext extends ParserRuleContext {
		public BiconditionalContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_biconditional; }
	 
		public BiconditionalContext() { }
		public void copyFrom(BiconditionalContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IffContext extends BiconditionalContext {
		public List<ImplicationContext> implication() {
			return getRuleContexts(ImplicationContext.class);
		}
		public ImplicationContext implication(int i) {
			return getRuleContext(ImplicationContext.class,i);
		}
		public List<TerminalNode> IFF() { return getTokens(LogicFormulaParser.IFF); }
		public TerminalNode IFF(int i) {
			return getToken(LogicFormulaParser.IFF, i);
		}
		public IffContext(BiconditionalContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitIff(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BiconditionalContext biconditional() throws RecognitionException {
		BiconditionalContext _localctx = new BiconditionalContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_biconditional);
		int _la;
		try {
			_localctx = new IffContext(_localctx);
			enterOuterAlt(_localctx, 1);
			{
			setState(17);
			implication();
			setState(22);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==IFF) {
				{
				{
				setState(18);
				match(IFF);
				setState(19);
				implication();
				}
				}
				setState(24);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ImplicationContext extends ParserRuleContext {
		public ImplicationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_implication; }
	 
		public ImplicationContext() { }
		public void copyFrom(ImplicationContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ImpliesContext extends ImplicationContext {
		public DisjunctionContext disjunction() {
			return getRuleContext(DisjunctionContext.class,0);
		}
		public TerminalNode IMPLIES() { return getToken(LogicFormulaParser.IMPLIES, 0); }
		public ImplicationContext implication() {
			return getRuleContext(ImplicationContext.class,0);
		}
		public ImpliesContext(ImplicationContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitImplies(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ImplicationContext implication() throws RecognitionException {
		ImplicationContext _localctx = new ImplicationContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_implication);
		int _la;
		try {
			_localctx = new ImpliesContext(_localctx);
			enterOuterAlt(_localctx, 1);
			{
			setState(25);
			disjunction();
			setState(28);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==IMPLIES) {
				{
				setState(26);
				match(IMPLIES);
				setState(27);
				implication();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class DisjunctionContext extends ParserRuleContext {
		public DisjunctionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_disjunction; }
	 
		public DisjunctionContext() { }
		public void copyFrom(DisjunctionContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class OrContext extends DisjunctionContext {
		public List<ConjunctionContext> conjunction() {
			return getRuleContexts(ConjunctionContext.class);
		}
		public ConjunctionContext conjunction(int i) {
			return getRuleContext(ConjunctionContext.class,i);
		}
		public List<TerminalNode> OR() { return getTokens(LogicFormulaParser.OR); }
		public TerminalNode OR(int i) {
			return getToken(LogicFormulaParser.OR, i);
		}
		public OrContext(DisjunctionContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitOr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DisjunctionContext disjunction() throws RecognitionException {
		DisjunctionContext _localctx = new DisjunctionContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_disjunction);
		int _la;
		try {
			_localctx = new OrContext(_localctx);
			enterOuterAlt(_localctx, 1);
			{
			setState(30);
			conjunction();
			setState(35);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==OR) {
				{
				{
				setState(31);
				match(OR);
				setState(32);
				conjunction();
				}
				}
				setState(37);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ConjunctionContext extends ParserRuleContext {
		public ConjunctionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_conjunction; }
	 
		public ConjunctionContext() { }
		public void copyFrom(ConjunctionContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class AndContext extends ConjunctionContext {
		public List<NegationContext> negation() {
			return getRuleContexts(NegationContext.class);
		}
		public NegationContext negation(int i) {
			return getRuleContext(NegationContext.class,i);
		}
		public List<TerminalNode> AND() { return getTokens(LogicFormulaParser.AND); }
		public TerminalNode AND(int i) {
			return getToken(LogicFormulaParser.AND, i);
		}
		public AndContext(ConjunctionContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitAnd(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConjunctionContext conjunction() throws RecognitionException {
		ConjunctionContext _localctx = new ConjunctionContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_conjunction);
		int _la;
		try {
			_localctx = new AndContext(_localctx);
			enterOuterAlt(_localctx, 1);
			{
			setState(38);
			negation();
			setState(43);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==AND) {
				{
				{
				setState(39);
				match(AND);
				setState(40);
				negation();
				}
				}
				setState(45);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class NegationContext extends ParserRuleContext {
		public NegationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_negation; }
	 
		public NegationContext() { }
		public void copyFrom(NegationContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class NotContext extends NegationContext {
		public TerminalNode NOT() { return getToken(LogicFormulaParser.NOT, 0); }
		public NegationContext negation() {
			return getRuleContext(NegationContext.class,0);
		}
		public NotContext(NegationContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitNot(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class VarContext extends NegationContext {
		public AtomContext atom() {
			return getRuleContext(AtomContext.class,0);
		}
		public VarContext(NegationContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitVar(this);
			else return visitor.visitChildren(this);
		}
	}

	public final NegationContext negation() throws RecognitionException {
		NegationContext _localctx = new NegationContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_negation);
		try {
			setState(49);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case NOT:
				_localctx = new NotContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(46);
				match(NOT);
				setState(47);
				negation();
				}
				break;
			case LPAR:
			case TRUE:
			case FALSE:
			case IDENTIFIER:
				_localctx = new VarContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(48);
				atom();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class AtomContext extends ParserRuleContext {
		public AtomContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_atom; }
	 
		public AtomContext() { }
		public void copyFrom(AtomContext ctx) {
			super.copyFrom(ctx);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class ParContext extends AtomContext {
		public TerminalNode LPAR() { return getToken(LogicFormulaParser.LPAR, 0); }
		public BiconditionalContext biconditional() {
			return getRuleContext(BiconditionalContext.class,0);
		}
		public TerminalNode RPAR() { return getToken(LogicFormulaParser.RPAR, 0); }
		public ParContext(AtomContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitPar(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class TrueContext extends AtomContext {
		public TerminalNode TRUE() { return getToken(LogicFormulaParser.TRUE, 0); }
		public TrueContext(AtomContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitTrue(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class FalseContext extends AtomContext {
		public TerminalNode FALSE() { return getToken(LogicFormulaParser.FALSE, 0); }
		public FalseContext(AtomContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitFalse(this);
			else return visitor.visitChildren(this);
		}
	}
	@SuppressWarnings("CheckReturnValue")
	public static class IdContext extends AtomContext {
		public TerminalNode IDENTIFIER() { return getToken(LogicFormulaParser.IDENTIFIER, 0); }
		public IdContext(AtomContext ctx) { copyFrom(ctx); }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof LogicFormulaVisitor ) return ((LogicFormulaVisitor<? extends T>)visitor).visitId(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AtomContext atom() throws RecognitionException {
		AtomContext _localctx = new AtomContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_atom);
		try {
			setState(58);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case LPAR:
				_localctx = new ParContext(_localctx);
				enterOuterAlt(_localctx, 1);
				{
				setState(51);
				match(LPAR);
				setState(52);
				biconditional();
				setState(53);
				match(RPAR);
				}
				break;
			case IDENTIFIER:
				_localctx = new IdContext(_localctx);
				enterOuterAlt(_localctx, 2);
				{
				setState(55);
				match(IDENTIFIER);
				}
				break;
			case TRUE:
				_localctx = new TrueContext(_localctx);
				enterOuterAlt(_localctx, 3);
				{
				setState(56);
				match(TRUE);
				}
				break;
			case FALSE:
				_localctx = new FalseContext(_localctx);
				enterOuterAlt(_localctx, 4);
				{
				setState(57);
				match(FALSE);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\u0004\u0001\u000b=\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"+
		"\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"+
		"\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0001\u0000\u0001\u0000\u0001"+
		"\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0005\u0001\u0015\b\u0001\n"+
		"\u0001\f\u0001\u0018\t\u0001\u0001\u0002\u0001\u0002\u0001\u0002\u0003"+
		"\u0002\u001d\b\u0002\u0001\u0003\u0001\u0003\u0001\u0003\u0005\u0003\""+
		"\b\u0003\n\u0003\f\u0003%\t\u0003\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0005\u0004*\b\u0004\n\u0004\f\u0004-\t\u0004\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0003\u00052\b\u0005\u0001\u0006\u0001\u0006\u0001\u0006"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0003\u0006;\b\u0006"+
		"\u0001\u0006\u0000\u0000\u0007\u0000\u0002\u0004\u0006\b\n\f\u0000\u0000"+
		"=\u0000\u000e\u0001\u0000\u0000\u0000\u0002\u0011\u0001\u0000\u0000\u0000"+
		"\u0004\u0019\u0001\u0000\u0000\u0000\u0006\u001e\u0001\u0000\u0000\u0000"+
		"\b&\u0001\u0000\u0000\u0000\n1\u0001\u0000\u0000\u0000\f:\u0001\u0000"+
		"\u0000\u0000\u000e\u000f\u0003\u0002\u0001\u0000\u000f\u0010\u0005\u0000"+
		"\u0000\u0001\u0010\u0001\u0001\u0000\u0000\u0000\u0011\u0016\u0003\u0004"+
		"\u0002\u0000\u0012\u0013\u0005\u0005\u0000\u0000\u0013\u0015\u0003\u0004"+
		"\u0002\u0000\u0014\u0012\u0001\u0000\u0000\u0000\u0015\u0018\u0001\u0000"+
		"\u0000\u0000\u0016\u0014\u0001\u0000\u0000\u0000\u0016\u0017\u0001\u0000"+
		"\u0000\u0000\u0017\u0003\u0001\u0000\u0000\u0000\u0018\u0016\u0001\u0000"+
		"\u0000\u0000\u0019\u001c\u0003\u0006\u0003\u0000\u001a\u001b\u0005\u0004"+
		"\u0000\u0000\u001b\u001d\u0003\u0004\u0002\u0000\u001c\u001a\u0001\u0000"+
		"\u0000\u0000\u001c\u001d\u0001\u0000\u0000\u0000\u001d\u0005\u0001\u0000"+
		"\u0000\u0000\u001e#\u0003\b\u0004\u0000\u001f \u0005\u0003\u0000\u0000"+
		" \"\u0003\b\u0004\u0000!\u001f\u0001\u0000\u0000\u0000\"%\u0001\u0000"+
		"\u0000\u0000#!\u0001\u0000\u0000\u0000#$\u0001\u0000\u0000\u0000$\u0007"+
		"\u0001\u0000\u0000\u0000%#\u0001\u0000\u0000\u0000&+\u0003\n\u0005\u0000"+
		"\'(\u0005\u0002\u0000\u0000(*\u0003\n\u0005\u0000)\'\u0001\u0000\u0000"+
		"\u0000*-\u0001\u0000\u0000\u0000+)\u0001\u0000\u0000\u0000+,\u0001\u0000"+
		"\u0000\u0000,\t\u0001\u0000\u0000\u0000-+\u0001\u0000\u0000\u0000./\u0005"+
		"\u0001\u0000\u0000/2\u0003\n\u0005\u000002\u0003\f\u0006\u00001.\u0001"+
		"\u0000\u0000\u000010\u0001\u0000\u0000\u00002\u000b\u0001\u0000\u0000"+
		"\u000034\u0005\u0006\u0000\u000045\u0003\u0002\u0001\u000056\u0005\u0007"+
		"\u0000\u00006;\u0001\u0000\u0000\u00007;\u0005\n\u0000\u00008;\u0005\b"+
		"\u0000\u00009;\u0005\t\u0000\u0000:3\u0001\u0000\u0000\u0000:7\u0001\u0000"+
		"\u0000\u0000:8\u0001\u0000\u0000\u0000:9\u0001\u0000\u0000\u0000;\r\u0001"+
		"\u0000\u0000\u0000\u0006\u0016\u001c#+1:";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}