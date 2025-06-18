// Generated from /Users/amosloverde/Desktop/bonacina/solutore_SAT/src/main/java/org/sat/antlr/org/sat/parser/LogicFormula.g4 by ANTLR 4.13.2
package org.sat.antlr.org.sat.parser;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue", "this-escape"})
public class LogicFormulaLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		NOT=1, AND=2, OR=3, IMPLIES=4, IFF=5, LPAR=6, RPAR=7, TRUE=8, FALSE=9, 
		IDENTIFIER=10, WHITESPACE=11;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"NOT", "AND", "OR", "IMPLIES", "IFF", "LPAR", "RPAR", "TRUE", "FALSE", 
			"IDENTIFIER", "WHITESPACE"
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


	public LogicFormulaLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "LogicFormula.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\u0004\u0000\u000bz\u0006\uffff\uffff\u0002\u0000\u0007\u0000\u0002\u0001"+
		"\u0007\u0001\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004"+
		"\u0007\u0004\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007"+
		"\u0007\u0007\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0001\u0000"+
		"\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000\u0001\u0000"+
		"\u0003\u0000\u001f\b\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0003\u0001(\b\u0001\u0001\u0002"+
		"\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0003\u0002/\b\u0002"+
		"\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003\u0001\u0003"+
		"\u0003\u0003C\b\u0003\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004\u0001\u0004"+
		"\u0001\u0004\u0001\u0004\u0003\u0004Q\b\u0004\u0001\u0005\u0001\u0005"+
		"\u0001\u0006\u0001\u0006\u0001\u0007\u0001\u0007\u0001\u0007\u0001\u0007"+
		"\u0001\u0007\u0001\u0007\u0003\u0007]\b\u0007\u0001\b\u0001\b\u0001\b"+
		"\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001"+
		"\b\u0003\bk\b\b\u0001\t\u0001\t\u0005\to\b\t\n\t\f\tr\t\t\u0001\n\u0004"+
		"\nu\b\n\u000b\n\f\nv\u0001\n\u0001\n\u0000\u0000\u000b\u0001\u0001\u0003"+
		"\u0002\u0005\u0003\u0007\u0004\t\u0005\u000b\u0006\r\u0007\u000f\b\u0011"+
		"\t\u0013\n\u0015\u000b\u0001\u0000\u0003\u0002\u0000AZaz\u0004\u00000"+
		"9AZ__az\u0003\u0000\t\n\r\r  \u0089\u0000\u0001\u0001\u0000\u0000\u0000"+
		"\u0000\u0003\u0001\u0000\u0000\u0000\u0000\u0005\u0001\u0000\u0000\u0000"+
		"\u0000\u0007\u0001\u0000\u0000\u0000\u0000\t\u0001\u0000\u0000\u0000\u0000"+
		"\u000b\u0001\u0000\u0000\u0000\u0000\r\u0001\u0000\u0000\u0000\u0000\u000f"+
		"\u0001\u0000\u0000\u0000\u0000\u0011\u0001\u0000\u0000\u0000\u0000\u0013"+
		"\u0001\u0000\u0000\u0000\u0000\u0015\u0001\u0000\u0000\u0000\u0001\u001e"+
		"\u0001\u0000\u0000\u0000\u0003\'\u0001\u0000\u0000\u0000\u0005.\u0001"+
		"\u0000\u0000\u0000\u0007B\u0001\u0000\u0000\u0000\tP\u0001\u0000\u0000"+
		"\u0000\u000bR\u0001\u0000\u0000\u0000\rT\u0001\u0000\u0000\u0000\u000f"+
		"\\\u0001\u0000\u0000\u0000\u0011j\u0001\u0000\u0000\u0000\u0013l\u0001"+
		"\u0000\u0000\u0000\u0015t\u0001\u0000\u0000\u0000\u0017\u001f\u0005!\u0000"+
		"\u0000\u0018\u0019\u0005n\u0000\u0000\u0019\u001a\u0005o\u0000\u0000\u001a"+
		"\u001f\u0005t\u0000\u0000\u001b\u001c\u0005N\u0000\u0000\u001c\u001d\u0005"+
		"O\u0000\u0000\u001d\u001f\u0005T\u0000\u0000\u001e\u0017\u0001\u0000\u0000"+
		"\u0000\u001e\u0018\u0001\u0000\u0000\u0000\u001e\u001b\u0001\u0000\u0000"+
		"\u0000\u001f\u0002\u0001\u0000\u0000\u0000 (\u0005&\u0000\u0000!\"\u0005"+
		"a\u0000\u0000\"#\u0005n\u0000\u0000#(\u0005d\u0000\u0000$%\u0005A\u0000"+
		"\u0000%&\u0005N\u0000\u0000&(\u0005D\u0000\u0000\' \u0001\u0000\u0000"+
		"\u0000\'!\u0001\u0000\u0000\u0000\'$\u0001\u0000\u0000\u0000(\u0004\u0001"+
		"\u0000\u0000\u0000)/\u0005|\u0000\u0000*+\u0005o\u0000\u0000+/\u0005r"+
		"\u0000\u0000,-\u0005O\u0000\u0000-/\u0005R\u0000\u0000.)\u0001\u0000\u0000"+
		"\u0000.*\u0001\u0000\u0000\u0000.,\u0001\u0000\u0000\u0000/\u0006\u0001"+
		"\u0000\u0000\u000001\u0005-\u0000\u00001C\u0005>\u0000\u000023\u0005="+
		"\u0000\u00003C\u0005>\u0000\u000045\u0005i\u0000\u000056\u0005m\u0000"+
		"\u000067\u0005p\u0000\u000078\u0005l\u0000\u000089\u0005i\u0000\u0000"+
		"9:\u0005e\u0000\u0000:C\u0005s\u0000\u0000;<\u0005I\u0000\u0000<=\u0005"+
		"M\u0000\u0000=>\u0005P\u0000\u0000>?\u0005L\u0000\u0000?@\u0005I\u0000"+
		"\u0000@A\u0005E\u0000\u0000AC\u0005S\u0000\u0000B0\u0001\u0000\u0000\u0000"+
		"B2\u0001\u0000\u0000\u0000B4\u0001\u0000\u0000\u0000B;\u0001\u0000\u0000"+
		"\u0000C\b\u0001\u0000\u0000\u0000DE\u0005<\u0000\u0000EF\u0005-\u0000"+
		"\u0000FQ\u0005>\u0000\u0000GH\u0005<\u0000\u0000HI\u0005=\u0000\u0000"+
		"IQ\u0005>\u0000\u0000JK\u0005i\u0000\u0000KL\u0005f\u0000\u0000LQ\u0005"+
		"f\u0000\u0000MN\u0005I\u0000\u0000NO\u0005F\u0000\u0000OQ\u0005F\u0000"+
		"\u0000PD\u0001\u0000\u0000\u0000PG\u0001\u0000\u0000\u0000PJ\u0001\u0000"+
		"\u0000\u0000PM\u0001\u0000\u0000\u0000Q\n\u0001\u0000\u0000\u0000RS\u0005"+
		"(\u0000\u0000S\f\u0001\u0000\u0000\u0000TU\u0005)\u0000\u0000U\u000e\u0001"+
		"\u0000\u0000\u0000VW\u0005t\u0000\u0000WX\u0005o\u0000\u0000X]\u0005p"+
		"\u0000\u0000YZ\u0005T\u0000\u0000Z[\u0005O\u0000\u0000[]\u0005P\u0000"+
		"\u0000\\V\u0001\u0000\u0000\u0000\\Y\u0001\u0000\u0000\u0000]\u0010\u0001"+
		"\u0000\u0000\u0000^_\u0005b\u0000\u0000_`\u0005o\u0000\u0000`a\u0005t"+
		"\u0000\u0000ab\u0005t\u0000\u0000bc\u0005o\u0000\u0000ck\u0005m\u0000"+
		"\u0000de\u0005B\u0000\u0000ef\u0005O\u0000\u0000fg\u0005T\u0000\u0000"+
		"gh\u0005T\u0000\u0000hi\u0005O\u0000\u0000ik\u0005M\u0000\u0000j^\u0001"+
		"\u0000\u0000\u0000jd\u0001\u0000\u0000\u0000k\u0012\u0001\u0000\u0000"+
		"\u0000lp\u0007\u0000\u0000\u0000mo\u0007\u0001\u0000\u0000nm\u0001\u0000"+
		"\u0000\u0000or\u0001\u0000\u0000\u0000pn\u0001\u0000\u0000\u0000pq\u0001"+
		"\u0000\u0000\u0000q\u0014\u0001\u0000\u0000\u0000rp\u0001\u0000\u0000"+
		"\u0000su\u0007\u0002\u0000\u0000ts\u0001\u0000\u0000\u0000uv\u0001\u0000"+
		"\u0000\u0000vt\u0001\u0000\u0000\u0000vw\u0001\u0000\u0000\u0000wx\u0001"+
		"\u0000\u0000\u0000xy\u0006\n\u0000\u0000y\u0016\u0001\u0000\u0000\u0000"+
		"\n\u0000\u001e\'.BP\\jpv\u0001\u0006\u0000\u0000";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}