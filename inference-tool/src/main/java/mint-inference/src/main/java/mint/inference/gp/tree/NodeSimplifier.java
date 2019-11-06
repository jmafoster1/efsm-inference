package mint.inference.gp.tree;

import java.util.Arrays;

import com.microsoft.z3.*;

import mint.inference.gp.tree.nonterminals.doubles.*;
import mint.inference.gp.tree.nonterminals.integers.*;
import mint.inference.gp.tree.terminals.*;
import mint.tracedata.types.*;

public class NodeSimplifier {

	private static Node<?> makeBinary(Expr[] e, NonTerminal<?> f) {
		f.addChild(fromZ3((IntExpr) e[0]));

		if (e.length == 2) {
			f.addChild(fromZ3((IntExpr) e[1]).copy());
			return f;
		}
		else {
			IntegerNonTerminal fPrime = (IntegerNonTerminal) f.copy();
			fPrime.clearChildren();
			Node<?> right = makeBinary(Arrays.copyOfRange(e, 1, e.length), fPrime);
			f.addChild(right.copy());
			return f;
		}
	}

	public static Node<IntegerVariableAssignment> fromZ3(IntExpr exp) {
		if (exp.isAdd()) {
			return (Node<IntegerVariableAssignment>) makeBinary(exp.getArgs(), new AddIntegersOperator());
		}
		if (exp.isSub()) {
			return (Node<IntegerVariableAssignment>) makeBinary(exp.getArgs(), new SubtractIntegersOperator());
		}
		if (exp.isMul() && Integer.valueOf(exp.getArgs()[0].toString()) == -1 && exp.getArgs().length == 2) {
			IntegerVariableAssignment zero = new IntegerVariableAssignment("0", 0);
			Node<IntegerVariableAssignment> c2 = fromZ3((IntExpr) exp.getArgs()[1]);
			return new SubtractIntegersOperator(new IntegerVariableAssignmentTerminal(zero, true), c2);
		}
		if (exp.isConst()) {
			IntegerVariableAssignment num = new IntegerVariableAssignment(exp.toString());
			return new IntegerVariableAssignmentTerminal(num, false);
		}
		if (exp.isIntNum()) {
			IntegerVariableAssignment num = new IntegerVariableAssignment(exp.toString(),
					Integer.valueOf(exp.toString()));
			return new IntegerVariableAssignmentTerminal(num, true);
		}
		throw new IllegalArgumentException("Could not convert from Z3 expression " + exp);
	}
	
	public static Node<DoubleVariableAssignment> fromZ3(RealExpr exp) {
		if (exp.isAdd()) {
			return (Node<DoubleVariableAssignment>) makeBinary(exp.getArgs(), new AddDoublesOperator());
		}
		if (exp.isSub()) {
			return (Node<DoubleVariableAssignment>) makeBinary(exp.getArgs(), new SubtractDoublesOperator());
		}
		if (exp.isMul() && Double.valueOf(exp.getArgs()[0].toString()) == -1 && exp.getArgs().length == 2) {
			DoubleVariableAssignment zero = new DoubleVariableAssignment("0", 0);
			Node<DoubleVariableAssignment> c2 = fromZ3((RealExpr) exp.getArgs()[1]);
			return new SubtractDoublesOperator(new DoubleVariableAssignmentTerminal(zero, true), c2);
		}
		if (exp.isConst()) {
			DoubleVariableAssignment num = new DoubleVariableAssignment(exp.toString());
			return new DoubleVariableAssignmentTerminal(num, false);
		}
		if (exp.isRatNum()) {
			DoubleVariableAssignment num = new DoubleVariableAssignment(exp.toString(),
					Double.valueOf(exp.toString()));
			return new DoubleVariableAssignmentTerminal(num, true);
		}
		throw new IllegalArgumentException("Could not convert from Z3 expression " + exp);
	}
	
	public static Node<BooleanVariableAssignment> fromZ3(BoolExpr exp) {
		if (exp.isAnd()) {
			return (Node<BooleanVariableAssignment>) makeBinary(exp.getArgs(), new AddIntegersOperator());
		}
		if (exp.isOr()) {
			return (Node<BooleanVariableAssignment>) makeBinary(exp.getArgs(), new SubtractIntegersOperator());
		}
		if (exp.isBool()) {
			BooleanVariableAssignment num = new BooleanVariableAssignment(exp.toString(),
					Boolean.valueOf(exp.toString()));
			return new BooleanVariableAssignmentTerminal(num, true);
		}
		throw new IllegalArgumentException("Could not convert from Z3 expression " + exp);
	}
	
	public static Node<?> fromZ3(Expr exp) {
		if (exp instanceof BoolExpr)
			return fromZ3((BoolExpr) exp);
		if (exp instanceof IntExpr)
			return fromZ3((IntExpr) exp);
		if (exp instanceof RealExpr)
			return fromZ3((RealExpr) exp);
		throw new IllegalArgumentException("Could not convert from Z3 expression " + exp);
	}

}
