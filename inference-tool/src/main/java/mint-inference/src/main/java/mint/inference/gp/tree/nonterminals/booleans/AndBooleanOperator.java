package mint.inference.gp.tree.nonterminals.booleans;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

import mint.inference.gp.Generator;
import mint.inference.gp.tree.Node;
import mint.inference.gp.tree.NodeVisitor;
import mint.inference.gp.tree.NonTerminal;
import mint.tracedata.types.BooleanVariableAssignment;

/**
 * Created by neilwalkinshaw on 26/05/15.
 */
public class AndBooleanOperator extends BooleanNonTerminal {

	public AndBooleanOperator(Node<?> a, Node<?> b) {
		super(null);
		addChild(a);
		addChild(b);
	}

	public AndBooleanOperator() {
		super();
	}

	@Override
	public NonTerminal<BooleanVariableAssignment> createInstance(Generator g, int depth) {
		return new AndBooleanOperator(g.generateRandomBooleanExpression(depth),
				g.generateRandomBooleanExpression(depth));
	}

	@Override
	protected String nodeString() {
		return "(and " + childrenString() + ")";
	}

	@Override
	public boolean accept(NodeVisitor visitor) throws InterruptedException {
		visitor.visitEnter(this);
		for (Node<?> child : children) {
			child.accept(visitor);
		}
		return visitor.visitExit(this);
	}

	@Override
	public BooleanVariableAssignment evaluate() throws InterruptedException {
		checkInterrupted();
		Boolean from = (Boolean) children.get(0).evaluate().getValue();
		Boolean to = (Boolean) children.get(1).evaluate().getValue();
		BooleanVariableAssignment res = new BooleanVariableAssignment("result", to && from);
		vals.add(res.getValue());
		return res;
	}

	@Override
	public Node<BooleanVariableAssignment> copy() {
		return new AndBooleanOperator(children.get(0).copy(), children.get(1).copy());

	}

	@Override
	public Expr toZ3(Context ctx) {
		BoolExpr b1 = (BoolExpr) getChild(0).toZ3(ctx);
		BoolExpr b2 = (BoolExpr) getChild(1).toZ3(ctx);
		return ctx.mkAnd(b1, b2);
	}
}
