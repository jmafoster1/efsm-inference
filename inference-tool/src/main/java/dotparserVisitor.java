// Generated from dotparser.g4 by ANTLR 4.6
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link dotparser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface dotparserVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link dotparser#aexp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAexp(dotparser.AexpContext ctx);
	/**
	 * Visit a parse tree produced by {@link dotparser#gexp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGexp(dotparser.GexpContext ctx);
	/**
	 * Visit a parse tree produced by {@link dotparser#guards}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGuards(dotparser.GuardsContext ctx);
	/**
	 * Visit a parse tree produced by {@link dotparser#outputs}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOutputs(dotparser.OutputsContext ctx);
	/**
	 * Visit a parse tree produced by {@link dotparser#update}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUpdate(dotparser.UpdateContext ctx);
	/**
	 * Visit a parse tree produced by {@link dotparser#updates}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUpdates(dotparser.UpdatesContext ctx);
	/**
	 * Visit a parse tree produced by {@link dotparser#rightpart}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitRightpart(dotparser.RightpartContext ctx);
	/**
	 * Visit a parse tree produced by {@link dotparser#transition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTransition(dotparser.TransitionContext ctx);
}