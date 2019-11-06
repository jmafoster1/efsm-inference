package mint.inference.gp.tree.nonterminals.booleans;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

import mint.inference.gp.Generator;
import mint.inference.gp.tree.Node;
import mint.inference.gp.tree.NodeVisitor;
import mint.inference.gp.tree.NonTerminal;
import mint.tracedata.types.BooleanVariableAssignment;
import mint.tracedata.types.IntegerVariableAssignment;

/**
 * Created by neilwalkinshaw on 26/05/15.
 */
public class LTBooleanIntegersOperator extends BooleanNonTerminal {

	public LTBooleanIntegersOperator(Node<?> b) {
		super(b);
	}

	public LTBooleanIntegersOperator(Node<IntegerVariableAssignment> a, Node<IntegerVariableAssignment> b) {
		super(null);
		addChild(a);
		addChild(b);
	}

	public LTBooleanIntegersOperator() {

	}

	@Override
	public NonTerminal<BooleanVariableAssignment> createInstance(Generator g, int depth) {
		return new LTBooleanIntegersOperator(g.generateRandomIntegerExpression(depth),
				g.generateRandomIntegerExpression(depth));
	}

	@Override
	protected String nodeString() {
		return "(< " + childrenString() + ")";
	}

	@Override
	public boolean accept(NodeVisitor visitor) throws InterruptedException {
		if (visitor.visitEnter(this)) {
			visitChildren(visitor);
		}
		return visitor.visitExit(this);
	}

	@Override
	public BooleanVariableAssignment evaluate() throws InterruptedException {
		checkInterrupted();
		BooleanVariableAssignment res = new BooleanVariableAssignment("result",
				(Integer) children.get(0).evaluate().getValue() < (Integer) children.get(1).evaluate().getValue());
		vals.add(res.getValue());
		return res;
	}

	@Override
	public Node<BooleanVariableAssignment> copy() {
		return new LTBooleanIntegersOperator((Node<IntegerVariableAssignment>) children.get(0).copy(),
				(Node<IntegerVariableAssignment>) children.get(1).copy());

	}

	@Override
	public Expr toZ3(Context ctx) {
		ArithExpr b1 = (ArithExpr) getChild(0).toZ3(ctx);
		ArithExpr b2 = (ArithExpr) getChild(1).toZ3(ctx);
		return ctx.mkLt(b1, b2);
	}
}
