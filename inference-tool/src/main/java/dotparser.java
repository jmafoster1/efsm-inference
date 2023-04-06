// Generated from dotparser.g4 by ANTLR 4.6
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class dotparser extends Parser {
	static { RuntimeMetaData.checkVersion("4.6", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		VALUE=1, VNAME=2, AOP=3, BOOL=4, GOP=5, IN=6, VALUELIST=7, NOT=8, OPEN=9, 
		OR=10, CLOSE=11, LANGLE=12, COMMA=13, RANGLE=14, IS=15, SLASH=16, LABEL=17, 
		COLON=18, ARITY=19;
	public static final int
		RULE_aexp = 0, RULE_gexp = 1, RULE_guards = 2, RULE_outputs = 3, RULE_update = 4, 
		RULE_updates = 5, RULE_rightpart = 6, RULE_transition = 7;
	public static final String[] ruleNames = {
		"aexp", "gexp", "guards", "outputs", "update", "updates", "rightpart", 
		"transition"
	};

	private static final String[] _LITERAL_NAMES = {
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "VALUE", "VNAME", "AOP", "BOOL", "GOP", "IN", "VALUELIST", "NOT", 
		"OPEN", "OR", "CLOSE", "LANGLE", "COMMA", "RANGLE", "IS", "SLASH", "LABEL", 
		"COLON", "ARITY"
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

	@Override
	public String getGrammarFileName() { return "dotparser.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public dotparser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class AexpContext extends ParserRuleContext {
		public TerminalNode VALUE() { return getToken(dotparser.VALUE, 0); }
		public TerminalNode VNAME() { return getToken(dotparser.VNAME, 0); }
		public List<AexpContext> aexp() {
			return getRuleContexts(AexpContext.class);
		}
		public AexpContext aexp(int i) {
			return getRuleContext(AexpContext.class,i);
		}
		public TerminalNode AOP() { return getToken(dotparser.AOP, 0); }
		public AexpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_aexp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).enterAexp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).exitAexp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof dotparserVisitor ) return ((dotparserVisitor<? extends T>)visitor).visitAexp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AexpContext aexp() throws RecognitionException {
		return aexp(0);
	}

	private AexpContext aexp(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		AexpContext _localctx = new AexpContext(_ctx, _parentState);
		AexpContext _prevctx = _localctx;
		int _startState = 0;
		enterRecursionRule(_localctx, 0, RULE_aexp, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(19);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case VALUE:
				{
				setState(17);
				match(VALUE);
				}
				break;
			case VNAME:
				{
				setState(18);
				match(VNAME);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(26);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,1,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new AexpContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_aexp);
					setState(21);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(22);
					match(AOP);
					setState(23);
					aexp(2);
					}
					} 
				}
				setState(28);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,1,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class GexpContext extends ParserRuleContext {
		public TerminalNode BOOL() { return getToken(dotparser.BOOL, 0); }
		public List<AexpContext> aexp() {
			return getRuleContexts(AexpContext.class);
		}
		public AexpContext aexp(int i) {
			return getRuleContext(AexpContext.class,i);
		}
		public TerminalNode GOP() { return getToken(dotparser.GOP, 0); }
		public TerminalNode VNAME() { return getToken(dotparser.VNAME, 0); }
		public TerminalNode IN() { return getToken(dotparser.IN, 0); }
		public TerminalNode VALUELIST() { return getToken(dotparser.VALUELIST, 0); }
		public TerminalNode NOT() { return getToken(dotparser.NOT, 0); }
		public TerminalNode OPEN() { return getToken(dotparser.OPEN, 0); }
		public List<GexpContext> gexp() {
			return getRuleContexts(GexpContext.class);
		}
		public GexpContext gexp(int i) {
			return getRuleContext(GexpContext.class,i);
		}
		public TerminalNode OR() { return getToken(dotparser.OR, 0); }
		public TerminalNode CLOSE() { return getToken(dotparser.CLOSE, 0); }
		public GexpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_gexp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).enterGexp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).exitGexp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof dotparserVisitor ) return ((dotparserVisitor<? extends T>)visitor).visitGexp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GexpContext gexp() throws RecognitionException {
		GexpContext _localctx = new GexpContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_gexp);
		try {
			setState(44);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,2,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(29);
				match(BOOL);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(30);
				aexp(0);
				setState(31);
				match(GOP);
				setState(32);
				aexp(0);
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				{
				setState(34);
				match(VNAME);
				setState(35);
				match(IN);
				setState(36);
				match(VALUELIST);
				}
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				{
				setState(37);
				match(NOT);
				setState(38);
				match(OPEN);
				setState(39);
				gexp();
				setState(40);
				match(OR);
				setState(41);
				gexp();
				setState(42);
				match(CLOSE);
				}
				}
				break;
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

	public static class GuardsContext extends ParserRuleContext {
		public TerminalNode LANGLE() { return getToken(dotparser.LANGLE, 0); }
		public TerminalNode RANGLE() { return getToken(dotparser.RANGLE, 0); }
		public List<TerminalNode> COMMA() { return getTokens(dotparser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(dotparser.COMMA, i);
		}
		public List<GexpContext> gexp() {
			return getRuleContexts(GexpContext.class);
		}
		public GexpContext gexp(int i) {
			return getRuleContext(GexpContext.class,i);
		}
		public GuardsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_guards; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).enterGuards(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).exitGuards(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof dotparserVisitor ) return ((dotparserVisitor<? extends T>)visitor).visitGuards(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GuardsContext guards() throws RecognitionException {
		GuardsContext _localctx = new GuardsContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_guards);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(46);
			match(LANGLE);
			setState(52);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << VALUE) | (1L << VNAME) | (1L << BOOL) | (1L << NOT))) != 0)) {
				{
				{
				{
				setState(47);
				gexp();
				}
				setState(48);
				match(COMMA);
				}
				}
				setState(54);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(55);
			match(RANGLE);
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

	public static class OutputsContext extends ParserRuleContext {
		public TerminalNode LANGLE() { return getToken(dotparser.LANGLE, 0); }
		public TerminalNode RANGLE() { return getToken(dotparser.RANGLE, 0); }
		public List<TerminalNode> COMMA() { return getTokens(dotparser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(dotparser.COMMA, i);
		}
		public List<AexpContext> aexp() {
			return getRuleContexts(AexpContext.class);
		}
		public AexpContext aexp(int i) {
			return getRuleContext(AexpContext.class,i);
		}
		public OutputsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_outputs; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).enterOutputs(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).exitOutputs(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof dotparserVisitor ) return ((dotparserVisitor<? extends T>)visitor).visitOutputs(this);
			else return visitor.visitChildren(this);
		}
	}

	public final OutputsContext outputs() throws RecognitionException {
		OutputsContext _localctx = new OutputsContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_outputs);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(57);
			match(LANGLE);
			setState(63);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==VALUE || _la==VNAME) {
				{
				{
				{
				setState(58);
				aexp(0);
				}
				setState(59);
				match(COMMA);
				}
				}
				setState(65);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(66);
			match(RANGLE);
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

	public static class UpdateContext extends ParserRuleContext {
		public TerminalNode VNAME() { return getToken(dotparser.VNAME, 0); }
		public TerminalNode IS() { return getToken(dotparser.IS, 0); }
		public AexpContext aexp() {
			return getRuleContext(AexpContext.class,0);
		}
		public UpdateContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_update; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).enterUpdate(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).exitUpdate(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof dotparserVisitor ) return ((dotparserVisitor<? extends T>)visitor).visitUpdate(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UpdateContext update() throws RecognitionException {
		UpdateContext _localctx = new UpdateContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_update);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(68);
			match(VNAME);
			setState(69);
			match(IS);
			setState(70);
			aexp(0);
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

	public static class UpdatesContext extends ParserRuleContext {
		public TerminalNode LANGLE() { return getToken(dotparser.LANGLE, 0); }
		public TerminalNode RANGLE() { return getToken(dotparser.RANGLE, 0); }
		public List<TerminalNode> COMMA() { return getTokens(dotparser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(dotparser.COMMA, i);
		}
		public List<UpdateContext> update() {
			return getRuleContexts(UpdateContext.class);
		}
		public UpdateContext update(int i) {
			return getRuleContext(UpdateContext.class,i);
		}
		public UpdatesContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_updates; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).enterUpdates(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).exitUpdates(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof dotparserVisitor ) return ((dotparserVisitor<? extends T>)visitor).visitUpdates(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UpdatesContext updates() throws RecognitionException {
		UpdatesContext _localctx = new UpdatesContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_updates);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(72);
			match(LANGLE);
			setState(78);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==VNAME) {
				{
				{
				{
				setState(73);
				update();
				}
				setState(74);
				match(COMMA);
				}
				}
				setState(80);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(81);
			match(RANGLE);
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

	public static class RightpartContext extends ParserRuleContext {
		public TerminalNode SLASH() { return getToken(dotparser.SLASH, 0); }
		public OutputsContext outputs() {
			return getRuleContext(OutputsContext.class,0);
		}
		public UpdatesContext updates() {
			return getRuleContext(UpdatesContext.class,0);
		}
		public RightpartContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_rightpart; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).enterRightpart(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).exitRightpart(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof dotparserVisitor ) return ((dotparserVisitor<? extends T>)visitor).visitRightpart(this);
			else return visitor.visitChildren(this);
		}
	}

	public final RightpartContext rightpart() throws RecognitionException {
		RightpartContext _localctx = new RightpartContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_rightpart);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(90);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==SLASH) {
				{
				setState(83);
				match(SLASH);
				setState(85);
				_errHandler.sync(this);
				switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
				case 1:
					{
					setState(84);
					outputs();
					}
					break;
				}
				setState(88);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==LANGLE) {
					{
					setState(87);
					updates();
					}
				}

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

	public static class TransitionContext extends ParserRuleContext {
		public TerminalNode LABEL() { return getToken(dotparser.LABEL, 0); }
		public TerminalNode COLON() { return getToken(dotparser.COLON, 0); }
		public TerminalNode ARITY() { return getToken(dotparser.ARITY, 0); }
		public GuardsContext guards() {
			return getRuleContext(GuardsContext.class,0);
		}
		public RightpartContext rightpart() {
			return getRuleContext(RightpartContext.class,0);
		}
		public TransitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_transition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).enterTransition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof dotparserListener ) ((dotparserListener)listener).exitTransition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof dotparserVisitor ) return ((dotparserVisitor<? extends T>)visitor).visitTransition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TransitionContext transition() throws RecognitionException {
		TransitionContext _localctx = new TransitionContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_transition);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(92);
			match(LABEL);
			setState(93);
			match(COLON);
			setState(94);
			match(ARITY);
			setState(95);
			guards();
			setState(96);
			rightpart();
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

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 0:
			return aexp_sempred((AexpContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean aexp_sempred(AexpContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 1);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\3\25e\4\2\t\2\4\3\t"+
		"\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\3\2\3\2\3\2\5\2\26"+
		"\n\2\3\2\3\2\3\2\7\2\33\n\2\f\2\16\2\36\13\2\3\3\3\3\3\3\3\3\3\3\3\3\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\5\3/\n\3\3\4\3\4\3\4\3\4\7\4\65\n\4"+
		"\f\4\16\48\13\4\3\4\3\4\3\5\3\5\3\5\3\5\7\5@\n\5\f\5\16\5C\13\5\3\5\3"+
		"\5\3\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\7\7O\n\7\f\7\16\7R\13\7\3\7\3\7\3\b"+
		"\3\b\5\bX\n\b\3\b\5\b[\n\b\5\b]\n\b\3\t\3\t\3\t\3\t\3\t\3\t\3\t\2\3\2"+
		"\n\2\4\6\b\n\f\16\20\2\2g\2\25\3\2\2\2\4.\3\2\2\2\6\60\3\2\2\2\b;\3\2"+
		"\2\2\nF\3\2\2\2\fJ\3\2\2\2\16\\\3\2\2\2\20^\3\2\2\2\22\23\b\2\1\2\23\26"+
		"\7\3\2\2\24\26\7\4\2\2\25\22\3\2\2\2\25\24\3\2\2\2\26\34\3\2\2\2\27\30"+
		"\f\3\2\2\30\31\7\5\2\2\31\33\5\2\2\4\32\27\3\2\2\2\33\36\3\2\2\2\34\32"+
		"\3\2\2\2\34\35\3\2\2\2\35\3\3\2\2\2\36\34\3\2\2\2\37/\7\6\2\2 !\5\2\2"+
		"\2!\"\7\7\2\2\"#\5\2\2\2#/\3\2\2\2$%\7\4\2\2%&\7\b\2\2&/\7\t\2\2\'(\7"+
		"\n\2\2()\7\13\2\2)*\5\4\3\2*+\7\f\2\2+,\5\4\3\2,-\7\r\2\2-/\3\2\2\2.\37"+
		"\3\2\2\2. \3\2\2\2.$\3\2\2\2.\'\3\2\2\2/\5\3\2\2\2\60\66\7\16\2\2\61\62"+
		"\5\4\3\2\62\63\7\17\2\2\63\65\3\2\2\2\64\61\3\2\2\2\658\3\2\2\2\66\64"+
		"\3\2\2\2\66\67\3\2\2\2\679\3\2\2\28\66\3\2\2\29:\7\20\2\2:\7\3\2\2\2;"+
		"A\7\16\2\2<=\5\2\2\2=>\7\17\2\2>@\3\2\2\2?<\3\2\2\2@C\3\2\2\2A?\3\2\2"+
		"\2AB\3\2\2\2BD\3\2\2\2CA\3\2\2\2DE\7\20\2\2E\t\3\2\2\2FG\7\4\2\2GH\7\21"+
		"\2\2HI\5\2\2\2I\13\3\2\2\2JP\7\16\2\2KL\5\n\6\2LM\7\17\2\2MO\3\2\2\2N"+
		"K\3\2\2\2OR\3\2\2\2PN\3\2\2\2PQ\3\2\2\2QS\3\2\2\2RP\3\2\2\2ST\7\20\2\2"+
		"T\r\3\2\2\2UW\7\22\2\2VX\5\b\5\2WV\3\2\2\2WX\3\2\2\2XZ\3\2\2\2Y[\5\f\7"+
		"\2ZY\3\2\2\2Z[\3\2\2\2[]\3\2\2\2\\U\3\2\2\2\\]\3\2\2\2]\17\3\2\2\2^_\7"+
		"\23\2\2_`\7\24\2\2`a\7\25\2\2ab\5\6\4\2bc\5\16\b\2c\21\3\2\2\2\13\25\34"+
		".\66APWZ\\";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}