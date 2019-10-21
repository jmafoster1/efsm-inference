/*******************************************************************************
 * Copyright 2012 Yuriy Lagodiuk
 * Modified by Michael Foster
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 ******************************************************************************/
package com.lagodiuk.gp.symbolic.interpreter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

public class Expression implements Cloneable {

	private List<Expression> childs = new ArrayList<Expression>();

	private List<Integer> coefficients = new ArrayList<Integer>();

	private String variable;

	private Function function;

	public Expression(Function function) {
		this.function = function;
	}

	public int eval(com.lagodiuk.gp.symbolic.interpreter.Context context) {
		return this.function.eval(this, context);
	}

	public Set<String> vars() {
		return this.function.vars(this);
	}

	public int height() {
		return this.function.height(this);
	}

	public String print() {
		return this.function.print(this);
	}

	public List<Expression> getChilds() {
		return this.childs;
	}

	public Expression setChilds(List<Expression> childs) {
		this.childs = childs;
		return this;
	}

	public void addChild(Expression child) {
		this.childs.add(child);
	}

	public void removeChilds() {
		this.childs.clear();
	}

	public List<Integer> getCoefficientsOfNode() {
		return this.coefficients;
	}

	public Expression setCoefficientsOfNode(List<Integer> coefficients) {
		this.coefficients = coefficients;
		return this;
	}

	public void addCoefficient(int coefficient) {
		this.coefficients.add(coefficient);
	}

	public void removeCoefficients() {
		if (this.coefficients.size() > 0) {
			this.coefficients.clear();
		}
	}

	public String getVariable() {
		return this.variable;
	}

	public Expression setVariable(String variable) {
		this.variable = variable;
		return this;
	}

	public Function getFunction() {
		return this.function;
	}

	public void setFunction(Function function) {
		this.function = function;
	}

	@Override
	public Expression clone() {
		Expression cloned = new Expression(this.function);
		if (this.variable != null) {
			cloned.variable = new String(this.variable);
		}
		for (Expression c : this.childs) {
			cloned.childs.add(c.clone());
		}
		for (Integer d : this.coefficients) {
			cloned.coefficients.add(d);
		}
		return cloned;
	}

	public List<Integer> getCoefficientsOfTree() {
		LinkedList<Integer> coefficients = new LinkedList<Integer>();
		this.getCoefficientsOfTree(coefficients);
		Collections.reverse(coefficients);
		return coefficients;
	}

	private void getCoefficientsOfTree(Deque<Integer> coefficients) {
		List<Integer> coeffs = this.function.getCoefficients(this);
		for (Integer d : coeffs) {
			coefficients.push(d);
		}
		for (int i = 0; i < this.childs.size(); i++) {
			this.childs.get(i).getCoefficientsOfTree(coefficients);
		}
	}

	public void setCoefficientsOfTree(List<Integer> coefficients) {
		this.setCoefficientsOfTree(coefficients, 0);
	}

	private int setCoefficientsOfTree(List<Integer> coefficients, int index) {
		this.function.setCoefficients(this, coefficients, index);
		index += this.function.coefficientsCount();
		if (this.childs.size() > 0) {
			for (int i = 0; i < this.childs.size(); i++) {
				index = this.childs.get(i).setCoefficientsOfTree(coefficients, index);
			}
		}
		return index;
	}

	public List<Expression> getAllNodesAsList() {
		List<Expression> nodes = new LinkedList<Expression>();
		this.getAllNodesBreadthFirstSearch(nodes);
		return nodes;
	}

	/**
	 * non-recursive Breadth-first iteration over all node of syntax tree
	 */
	private void getAllNodesBreadthFirstSearch(List<Expression> nodesList) {
		int indx = 0;
		nodesList.add(this);
		while (true) {
			if (indx < nodesList.size()) {
				Expression node = nodesList.get(indx++);
				for (Expression child : node.childs) {
					nodesList.add(child);
				}
			} else {
				break;
			}
		}
	}

	public ArithExpr toZ3(Context ctx) {
		return this.function.toZ3(this, ctx);
	}

	public Functions whatIs(Expr e) {
		if (e.isMul()) {
			return Functions.MUL;
		}
		if (e.isAdd()) {
			return Functions.ADD;
		}
		if (e.isSub()) {
			return Functions.SUB;
		}
		if (e.isConst()) {
			return Functions.VARIABLE;
		}
		if (e.isIntNum()) {
			return Functions.CONSTANT;
		}
		throw new IllegalArgumentException("Expression is not ADD, SUB, VARIABLE, or CONSTANT");
	}

	private Expression makeBinary(Expr[] e, Function f) {
		if (e.length == 0) {
			throw new IllegalArgumentException("Not enough args for function");
		}
		Expression left = fromZ3(e[0]);
		if (e.length == 1) {
			return left;
		}
		Expression expr = new Expression(f);
		Expression right = makeBinary(Arrays.copyOfRange(e, 1, e.length), f);
		expr.addChild(left);
		expr.addChild(right);
		return expr;
	}

	public Expression fromZ3(Expr ex) {
		Functions f = whatIs(ex);
		Expression expr = new Expression(f);

		switch (f) {
		case CONSTANT:
			expr.addCoefficient(Integer.parseInt(ex.toString()));
			return expr;
		case VARIABLE:
			expr.setVariable(ex.toString());
			return expr;
		case ADD:
			return makeBinary(ex.getArgs(), Functions.ADD);
		case MUL:
			return makeBinary(ex.getArgs(), Functions.MUL);
		case SUB:
			return makeBinary(ex.getArgs(), Functions.SUB);
		default:
			break;
		}
		throw new IllegalArgumentException("Simplified expression is not ADD, SUB, VARIABLE, or CONSTANT");
	}

	public Expression simplify() {
		Context ctx = new Context();
		Expr ex = this.function.toZ3(this, ctx).simplify();
		Expression simpler;
		try {
			simpler =  fromZ3(ex);
		}
		catch (NumberFormatException e) {
			simpler = this.clone();
		}
		ctx.close();
		return simpler;
	}

	public String toString() {
		return this.print();
	}

}
