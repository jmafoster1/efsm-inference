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
package com.lagodiuk.gp.symbolic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.lagodiuk.gp.symbolic.interpreter.Expression;
import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;

public class Target {
	private Map<String, Integer> contextState = new HashMap<String, Integer>();
	private int targetValue;

	public Target() {
	}

	public Target(Map<String, Integer> contextState, int targetValue) {
		this.contextState.putAll(contextState);
		this.targetValue = targetValue;
	}
	
	public Target(int targetValue, Integer... inputs) {
		int i = 1;
		for (int iv: inputs) {
			this.when("i"+i, iv);
		}
		this.targetValue = targetValue;
	}

	public Target when(String variableName, int variableValue) {
		this.contextState.put(variableName, variableValue);
		return this;
	}

	public Target targetIs(int targetValue) {
		this.targetValue = targetValue;
		return this;
	}

	public int getTargetValue() {
		return this.targetValue;
	}

	public Map<String, Integer> getContextState() {
		return this.contextState;
	}
	
	public void solve(Expression expression) {
		List<String> expVars = new ArrayList<>(expression.vars());
		Collections.sort(expVars);

		Set<String> definedVars = this.getContextState().keySet();
		
		List<String> undefinedVars = new ArrayList<>(expVars);
		undefinedVars.removeAll(definedVars);
		
		String inputs = "";
		for (String v : expVars) {
			inputs += "("+v +" Int)";
		}

		String z3String = "(define-fun f ("+inputs+") Int \n  "+expression+"\n)\n";
		
		for (String v: undefinedVars) {
			z3String += "(declare-const "+v+" Int)\n";
		}
		
		List<String> args = new ArrayList<String>();
		
		for (String v: expVars) {
			if (definedVars.contains(v)) {
				args.add(this.getContextState().get(v).toString());
			}
			else {
				args.add(v);
			}
		}
		
		String assertion = "(assert (= "+this.getTargetValue()+" (f "+String.join(" ", args)+")))";

		z3String += assertion;
		
//		System.out.println(z3String);
		
        Context ctx = new Context();
        Solver solver = ctx.mkSimpleSolver();
        solver.fromString(z3String);
        solver.check();
        Model model = solver.getModel();
        for (FuncDecl f: model.getConstDecls()) {
        	this.when(f.getName().toString(), Integer.valueOf(model.getConstInterp(f).toString()));
        }
        ctx.close();
	}
	
	public String toString() {
		return this.getContextState().entrySet() + " -> " + this.targetValue;
	}
}
