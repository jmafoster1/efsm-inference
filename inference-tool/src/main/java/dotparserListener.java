// Generated from dotparser.g4 by ANTLR 4.6
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link dotparser}.
 */
public interface dotparserListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link dotparser#aexp}.
	 * @param ctx the parse tree
	 */
	void enterAexp(dotparser.AexpContext ctx);
	/**
	 * Exit a parse tree produced by {@link dotparser#aexp}.
	 * @param ctx the parse tree
	 */
	void exitAexp(dotparser.AexpContext ctx);
	/**
	 * Enter a parse tree produced by {@link dotparser#gexp}.
	 * @param ctx the parse tree
	 */
	void enterGexp(dotparser.GexpContext ctx);
	/**
	 * Exit a parse tree produced by {@link dotparser#gexp}.
	 * @param ctx the parse tree
	 */
	void exitGexp(dotparser.GexpContext ctx);
	/**
	 * Enter a parse tree produced by {@link dotparser#guards}.
	 * @param ctx the parse tree
	 */
	void enterGuards(dotparser.GuardsContext ctx);
	/**
	 * Exit a parse tree produced by {@link dotparser#guards}.
	 * @param ctx the parse tree
	 */
	void exitGuards(dotparser.GuardsContext ctx);
	/**
	 * Enter a parse tree produced by {@link dotparser#outputs}.
	 * @param ctx the parse tree
	 */
	void enterOutputs(dotparser.OutputsContext ctx);
	/**
	 * Exit a parse tree produced by {@link dotparser#outputs}.
	 * @param ctx the parse tree
	 */
	void exitOutputs(dotparser.OutputsContext ctx);
	/**
	 * Enter a parse tree produced by {@link dotparser#update}.
	 * @param ctx the parse tree
	 */
	void enterUpdate(dotparser.UpdateContext ctx);
	/**
	 * Exit a parse tree produced by {@link dotparser#update}.
	 * @param ctx the parse tree
	 */
	void exitUpdate(dotparser.UpdateContext ctx);
	/**
	 * Enter a parse tree produced by {@link dotparser#updates}.
	 * @param ctx the parse tree
	 */
	void enterUpdates(dotparser.UpdatesContext ctx);
	/**
	 * Exit a parse tree produced by {@link dotparser#updates}.
	 * @param ctx the parse tree
	 */
	void exitUpdates(dotparser.UpdatesContext ctx);
	/**
	 * Enter a parse tree produced by {@link dotparser#rightpart}.
	 * @param ctx the parse tree
	 */
	void enterRightpart(dotparser.RightpartContext ctx);
	/**
	 * Exit a parse tree produced by {@link dotparser#rightpart}.
	 * @param ctx the parse tree
	 */
	void exitRightpart(dotparser.RightpartContext ctx);
	/**
	 * Enter a parse tree produced by {@link dotparser#transition}.
	 * @param ctx the parse tree
	 */
	void enterTransition(dotparser.TransitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link dotparser#transition}.
	 * @param ctx the parse tree
	 */
	void exitTransition(dotparser.TransitionContext ctx);
}