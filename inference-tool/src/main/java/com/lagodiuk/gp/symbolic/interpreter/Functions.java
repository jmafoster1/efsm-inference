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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.microsoft.z3.ArithExpr;

public enum Functions implements Function {

	CONSTANT {
		private int coefficientsCount = 1;

		@Override
		public int argumentsCount() {
			return 0;
		}

		@Override
		public int coefficientsCount() {
			return this.coefficientsCount;
		}

		@Override
		public List<Integer> getCoefficients(Expression expression) {
			return expression.getCoefficientsOfNode().subList(0, this.coefficientsCount);
		}

		@Override
		public void setCoefficients(Expression expression, List<Integer> coefficients, int startIndex) {
			expression.removeCoefficients();
			for (int i = 0; i < this.coefficientsCount; i++) {
				expression.addCoefficient(coefficients.get(startIndex + i));
			}
		}

		@Override
		public boolean isVariable() {
			return false;
		}

		@Override
		public boolean isCommutative() {
			return true;
		}

		@Override
		public int eval(Expression expression, Context context) {
			return expression.getCoefficientsOfNode().get(0);
		}

		@Override
		public String print(Expression expression) {
			int retVal = expression.getCoefficientsOfNode().get(0);
			String retStr = null;
			if (retVal < 0) {
				retStr = String.format("(%s)", retVal);
			} else {
				retStr = "" + retVal;
			}
			return retStr;
		}

		@Override
		public boolean isNumber() {
			return true;
		}

		@Override
		public int height(Expression expression) {
			return 1;
		}

		@Override
		public ArithExpr toZ3(Expression expression, com.microsoft.z3.Context ctx) {
			return ctx.mkInt(expression.getCoefficientsOfNode().get(0));
		}

		@Override
		public Set<String> vars(Expression expression) {
			return new HashSet<String>();
		}

	},
	VARIABLE {
		private int coefficientsCount = 0;

		@Override
		public int coefficientsCount() {
			return this.coefficientsCount;
		}

		@Override
		public List<Integer> getCoefficients(Expression expression) {
			return new LinkedList<Integer>();
		}

		@Override
		public void setCoefficients(Expression expression, List<Integer> coefficients, int startIndex) {
			expression.removeCoefficients();
		}

		@Override
		public int argumentsCount() {
			return 0;
		}

		@Override
		public boolean isVariable() {
			return true;
		}

		@Override
		public boolean isNumber() {
			return false;
		}

		@Override
		public boolean isCommutative() {
			return true;
		}

		@Override
		public int eval(Expression expression, Context context) {
			return context.lookupVariable(expression.getVariable());
		}

		@Override
		public String print(Expression expression) {
			return expression.getVariable().toString();
		}

		@Override
		public int height(Expression expression) {
			return 1;
		}

		@Override
		public ArithExpr toZ3(Expression expression, com.microsoft.z3.Context ctx) {
			return ctx.mkIntConst(expression.getVariable().toString());
		}

		@Override
		public Set<String> vars(Expression expression) {
			Set<String> vars = new HashSet<String>();
			vars.add(expression.getVariable().toString());
			return vars;
		}
	},
	ADD {
		private int coefficientsCount = 0;

		@Override
		public int coefficientsCount() {
			return this.coefficientsCount;
		}

		@Override
		public List<Integer> getCoefficients(Expression expression) {
			return new LinkedList<Integer>();
		}

		@Override
		public void setCoefficients(Expression expression, List<Integer> coefficients, int startIndex) {
			expression.removeCoefficients();
		}

		@Override
		public int argumentsCount() {
			return 2;
		}

		@Override
		public boolean isVariable() {
			return false;
		}

		@Override
		public boolean isNumber() {
			return false;
		}

		@Override
		public boolean isCommutative() {
			return true;
		}

		@Override
		public int eval(Expression expression, Context context) {
			List<Expression> childs = expression.getChilds();
			int left = childs.get(0).eval(context);
			int right = childs.get(1).eval(context);
			return (left + right);
		}

		@Override
		public String print(Expression expression) {
			List<Expression> childs = expression.getChilds();
			String left = childs.get(0).print();
			String right = childs.get(1).print();
			return String.format("(+ %s %s)", left, right);
		}

		@Override
		public int height(Expression expression) {
			List<Expression> childs = expression.getChilds();
			int left = childs.get(0).height();
			int right = childs.get(1).height();
			return (left + right + 1);
		}

		@Override
		public ArithExpr toZ3(Expression expression, com.microsoft.z3.Context ctx) {
			List<Expression> childs = expression.getChilds();
			Expression left = childs.get(0);
			Expression right = childs.get(1);
			return ctx.mkAdd(left.toZ3(ctx), right.toZ3(ctx));
		}

		@Override
		public Set<String> vars(Expression expression) {
			List<Expression> childs = expression.getChilds();
			Set<String> vars = childs.get(0).vars();
			for (String v: childs.get(1).vars()) {
				vars.add(v);
			}
			return vars;
		}
	},
	SUB {
		private int coefficientsCount = 0;

		@Override
		public int coefficientsCount() {
			return this.coefficientsCount;
		}

		@Override
		public List<Integer> getCoefficients(Expression expression) {
			return new LinkedList<Integer>();
		}

		@Override
		public void setCoefficients(Expression expression, List<Integer> coefficients, int startIndex) {
			expression.removeCoefficients();
		}

		@Override
		public int argumentsCount() {
			return 2;
		}

		@Override
		public boolean isVariable() {
			return false;
		}

		@Override
		public boolean isNumber() {
			return false;
		}

		@Override
		public boolean isCommutative() {
			return false;
		}

		@Override
		public int eval(Expression expression, Context context) {
			List<Expression> childs = expression.getChilds();
			int left = childs.get(0).eval(context);
			int right = childs.get(1).eval(context);
			return (left - right);
		}

		@Override
		public String print(Expression expression) {
			List<Expression> childs = expression.getChilds();
			String left = childs.get(0).print();
			String right = childs.get(1).print();

			return String.format("(- %s %s)", left, right);
		}
		
		@Override
		public int height(Expression expression) {
			List<Expression> childs = expression.getChilds();
			int left = childs.get(0).height();
			int right = childs.get(1).height();
			return (left + right + 1);
		}

		@Override
		public Set<String> vars(Expression expression) {
			List<Expression> childs = expression.getChilds();
			Set<String> vars = childs.get(0).vars();
			for (String v: childs.get(1).vars()) {
				vars.add(v);
			}
			return vars;
		}

		@Override
		public ArithExpr toZ3(Expression expression, com.microsoft.z3.Context ctx) {
			List<Expression> childs = expression.getChilds();
			Expression left = childs.get(0);
			Expression right = childs.get(1);
			return ctx.mkSub(left.toZ3(ctx), right.toZ3(ctx));
		}
	},
	MUL {
		private int coefficientsCount = 0;

		@Override
		public int coefficientsCount() {
			return this.coefficientsCount;
		}

		@Override
		public List<Integer> getCoefficients(Expression expression) {
			return new LinkedList<Integer>();
		}

		@Override
		public void setCoefficients(Expression expression, List<Integer> coefficients, int startIndex) {
			expression.removeCoefficients();
		}

		@Override
		public int argumentsCount() {
			return 2;
		}

		@Override
		public boolean isVariable() {
			return false;
		}

		@Override
		public boolean isNumber() {
			return false;
		}

		@Override
		public boolean isCommutative() {
			return true;
		}

		@Override
		public int eval(Expression expression, Context context) {
			List<Expression> childs = expression.getChilds();
			int left = childs.get(0).eval(context);
			int right = childs.get(1).eval(context);
			return (left * right);
		}

		@Override
		public String print(Expression expression) {
			List<Expression> childs = expression.getChilds();
			String left = childs.get(0).print();
			String right = childs.get(1).print();

			return String.format("(* %s %s)", left, right);
		}

		@Override
		public int height(Expression expression) {
			List<Expression> childs = expression.getChilds();
			int left = childs.get(0).height();
			int right = childs.get(1).height();
			return (left + right + 1);
		}

		@Override
		public Set<String> vars(Expression expression) {
			List<Expression> childs = expression.getChilds();
			Set<String> vars = childs.get(0).vars();
			for (String v: childs.get(1).vars()) {
				vars.add(v);
			}
			return vars;
		}

		@Override
		public ArithExpr toZ3(Expression expression, com.microsoft.z3.Context ctx) {
			List<Expression> childs = expression.getChilds();
			Expression left = childs.get(0);
			Expression right = childs.get(1);
			return ctx.mkMul(left.toZ3(ctx), right.toZ3(ctx));
		}
	},
}
