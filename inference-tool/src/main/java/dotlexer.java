// Generated from dotlexer.g4 by ANTLR 4.6
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class dotlexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.6", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		LABEL=1, ARITY=2, NUMBER=3, BOOL=4, COLON=5, STR=6, INT=7, REAL=8, VALUE=9, 
		VALUELIST=10, VNAME=11, AOP=12, GOP=13, OR=14, IN=15, NOT=16, OPEN=17, 
		CLOSE=18, LANGLE=19, RANGLE=20, COMMA=21, SLASH=22, IS=23;
	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"LABEL", "ARITY", "NUMBER", "BOOL", "COLON", "STR", "INT", "REAL", "VALUE", 
		"VALUELIST", "VNAME", "AOP", "GOP", "OR", "IN", "NOT", "OPEN", "CLOSE", 
		"LANGLE", "RANGLE", "COMMA", "SLASH", "IS"
	};

	private static final String[] _LITERAL_NAMES = {
		null, null, null, null, null, "':'", null, null, null, null, null, null, 
		null, null, "'&or;'", "'&isin;'", "'!'", "'('", "')'", "'['", "']'", "','", 
		"'/'", "':='"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "LABEL", "ARITY", "NUMBER", "BOOL", "COLON", "STR", "INT", "REAL", 
		"VALUE", "VALUELIST", "VNAME", "AOP", "GOP", "OR", "IN", "NOT", "OPEN", 
		"CLOSE", "LANGLE", "RANGLE", "COMMA", "SLASH", "IS"
	};
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


	public dotlexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "dotlexer.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\2\31\u00c1\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\3\2"+
		"\3\2\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\5\5A\n\5\3\6"+
		"\3\6\3\7\3\7\7\7G\n\7\f\7\16\7J\13\7\3\7\3\7\3\b\5\bO\n\b\3\b\6\bR\n\b"+
		"\r\b\16\bS\3\t\6\tW\n\t\r\t\16\tX\3\t\3\t\6\t]\n\t\r\t\16\t^\3\n\3\n\3"+
		"\n\5\nd\n\n\3\13\3\13\3\13\3\13\7\13j\n\13\f\13\16\13m\13\13\3\13\3\13"+
		"\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3"+
		"\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\5\f\u008f\n\f\3\r\3"+
		"\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\5\r\u00a1\n"+
		"\r\3\16\3\16\3\17\3\17\3\17\3\17\3\17\3\20\3\20\3\20\3\20\3\20\3\20\3"+
		"\20\3\21\3\21\3\22\3\22\3\23\3\23\3\24\3\24\3\25\3\25\3\26\3\26\3\27\3"+
		"\27\3\30\3\30\3\30\2\2\31\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25"+
		"\f\27\r\31\16\33\17\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\3\2\4"+
		"\3\2C|\4\2--//\u00cc\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2"+
		"\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3"+
		"\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2"+
		"\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2"+
		"\2-\3\2\2\2\2/\3\2\2\2\3\61\3\2\2\2\5\63\3\2\2\2\7\65\3\2\2\2\t@\3\2\2"+
		"\2\13B\3\2\2\2\rD\3\2\2\2\17N\3\2\2\2\21V\3\2\2\2\23c\3\2\2\2\25e\3\2"+
		"\2\2\27\u008e\3\2\2\2\31\u00a0\3\2\2\2\33\u00a2\3\2\2\2\35\u00a4\3\2\2"+
		"\2\37\u00a9\3\2\2\2!\u00b0\3\2\2\2#\u00b2\3\2\2\2%\u00b4\3\2\2\2\'\u00b6"+
		"\3\2\2\2)\u00b8\3\2\2\2+\u00ba\3\2\2\2-\u00bc\3\2\2\2/\u00be\3\2\2\2\61"+
		"\62\t\2\2\2\62\4\3\2\2\2\63\64\5\7\4\2\64\6\3\2\2\2\65\66\4\62;\2\66\b"+
		"\3\2\2\2\678\7V\2\289\7t\2\29:\7w\2\2:A\7g\2\2;<\7H\2\2<=\7c\2\2=>\7n"+
		"\2\2>?\7u\2\2?A\7g\2\2@\67\3\2\2\2@;\3\2\2\2A\n\3\2\2\2BC\7<\2\2C\f\3"+
		"\2\2\2DH\7$\2\2EG\3\2\2\2FE\3\2\2\2GJ\3\2\2\2HF\3\2\2\2HI\3\2\2\2IK\3"+
		"\2\2\2JH\3\2\2\2KL\7$\2\2L\16\3\2\2\2MO\7/\2\2NM\3\2\2\2NO\3\2\2\2OQ\3"+
		"\2\2\2PR\5\7\4\2QP\3\2\2\2RS\3\2\2\2SQ\3\2\2\2ST\3\2\2\2T\20\3\2\2\2U"+
		"W\5\7\4\2VU\3\2\2\2WX\3\2\2\2XV\3\2\2\2XY\3\2\2\2YZ\3\2\2\2Z\\\7\60\2"+
		"\2[]\5\7\4\2\\[\3\2\2\2]^\3\2\2\2^\\\3\2\2\2^_\3\2\2\2_\22\3\2\2\2`d\5"+
		"\r\7\2ad\5\17\b\2bd\5\7\4\2c`\3\2\2\2ca\3\2\2\2cb\3\2\2\2d\24\3\2\2\2"+
		"ek\7]\2\2fg\5\23\n\2gh\7.\2\2hj\3\2\2\2if\3\2\2\2jm\3\2\2\2ki\3\2\2\2"+
		"kl\3\2\2\2ln\3\2\2\2mk\3\2\2\2no\7_\2\2o\26\3\2\2\2pq\7k\2\2qr\7>\2\2"+
		"rs\7u\2\2st\7w\2\2tu\7d\2\2uv\7@\2\2vw\3\2\2\2wx\5\17\b\2xy\7>\2\2yz\7"+
		"\61\2\2z{\7u\2\2{|\7w\2\2|}\7d\2\2}~\7@\2\2~\u008f\3\2\2\2\177\u0080\7"+
		"t\2\2\u0080\u0081\7>\2\2\u0081\u0082\7u\2\2\u0082\u0083\7w\2\2\u0083\u0084"+
		"\7d\2\2\u0084\u0085\7@\2\2\u0085\u0086\3\2\2\2\u0086\u0087\5\17\b\2\u0087"+
		"\u0088\7>\2\2\u0088\u0089\7\61\2\2\u0089\u008a\7u\2\2\u008a\u008b\7w\2"+
		"\2\u008b\u008c\7d\2\2\u008c\u008d\7@\2\2\u008d\u008f\3\2\2\2\u008ep\3"+
		"\2\2\2\u008e\177\3\2\2\2\u008f\30\3\2\2\2\u0090\u00a1\t\3\2\2\u0091\u0092"+
		"\7(\2\2\u0092\u0093\7v\2\2\u0093\u0094\7k\2\2\u0094\u0095\7o\2\2\u0095"+
		"\u0096\7g\2\2\u0096\u0097\7u\2\2\u0097\u00a1\7=\2\2\u0098\u0099\7(\2\2"+
		"\u0099\u009a\7f\2\2\u009a\u009b\7k\2\2\u009b\u009c\7x\2\2\u009c\u009d"+
		"\7k\2\2\u009d\u009e\7f\2\2\u009e\u009f\7g\2\2\u009f\u00a1\7=\2\2\u00a0"+
		"\u0090\3\2\2\2\u00a0\u0091\3\2\2\2\u00a0\u0098\3\2\2\2\u00a1\32\3\2\2"+
		"\2\u00a2\u00a3\4?@\2\u00a3\34\3\2\2\2\u00a4\u00a5\7(\2\2\u00a5\u00a6\7"+
		"q\2\2\u00a6\u00a7\7t\2\2\u00a7\u00a8\7=\2\2\u00a8\36\3\2\2\2\u00a9\u00aa"+
		"\7(\2\2\u00aa\u00ab\7k\2\2\u00ab\u00ac\7u\2\2\u00ac\u00ad\7k\2\2\u00ad"+
		"\u00ae\7p\2\2\u00ae\u00af\7=\2\2\u00af \3\2\2\2\u00b0\u00b1\7#\2\2\u00b1"+
		"\"\3\2\2\2\u00b2\u00b3\7*\2\2\u00b3$\3\2\2\2\u00b4\u00b5\7+\2\2\u00b5"+
		"&\3\2\2\2\u00b6\u00b7\7]\2\2\u00b7(\3\2\2\2\u00b8\u00b9\7_\2\2\u00b9*"+
		"\3\2\2\2\u00ba\u00bb\7.\2\2\u00bb,\3\2\2\2\u00bc\u00bd\7\61\2\2\u00bd"+
		".\3\2\2\2\u00be\u00bf\7<\2\2\u00bf\u00c0\7?\2\2\u00c0\60\3\2\2\2\r\2@"+
		"HNSX^ck\u008e\u00a0\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}