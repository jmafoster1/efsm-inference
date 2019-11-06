package mint.inference.gp.tree.nonterminals.strings;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

import mint.inference.gp.Generator;
import mint.inference.gp.tree.Node;
import mint.inference.gp.tree.NonTerminal;
import mint.tracedata.types.StringVariableAssignment;

/**
 * Created by neilwalkinshaw on 03/03/15.
 */
public class ConcatStringsOperator extends StringNonTerminal {

	public ConcatStringsOperator() {
	}

	protected ConcatStringsOperator(Node<StringVariableAssignment> a, Node<StringVariableAssignment> b) {
		super();
		addChild(a);
		addChild(b);
	}

	@Override
	public StringVariableAssignment evaluate() throws InterruptedException {
		checkInterrupted();
		StringVariableAssignment svar = new StringVariableAssignment("result",
				(getChild(0).evaluate().getValue().toString().concat(getChild(1).evaluate().getValue().toString())));
		vals.add(svar);
		return svar;
	}

	@Override
	public NonTerminal<StringVariableAssignment> createInstance(Generator g, int depth) {
		return new ConcatStringsOperator(g.generateRandomStringExpression(depth),
				g.generateRandomStringExpression(depth));
	}

	@Override
	public Node<StringVariableAssignment> copy() {
		return new ConcatStringsOperator((Node<StringVariableAssignment>) getChild(0).copy(),
				(Node<StringVariableAssignment>) getChild(1).copy());
	}

	@Override
	public String nodeString() {
		return "Concat(" + childrenString() + ")";
	}
	
	@Override
	public Expr toZ3(Context ctx) {
		BitVecExpr b1 = (BitVecExpr) getChild(0).toZ3(ctx);
		BitVecExpr b2 = (BitVecExpr) getChild(1).toZ3(ctx);
		return ctx.mkConcat(b1, b2);
	}
}
