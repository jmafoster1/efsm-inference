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
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;

public class Context {

	private Random random = new Random();
	
	private ArrayList<Integer> values = new ArrayList<Integer>(Arrays.asList(0));

	private int minMutationValue = -3;

	private int maxMutationValue = 3;

	private Map<String, Integer> variables = new HashMap<String, Integer>();

	private List<Function> nonTerminalFunctions = new ArrayList<Function>();

	private List<Function> terminalFunctions = new ArrayList<Function>();

	private int nextRndFunctionIndx = 0;
	
	public void setup(Set<Entry<String, Integer>> s) {
		for (Entry<String, Integer> e : s) {
			String variableName = e.getKey();
			Integer variableValue = e.getValue();
			this.setVariable(variableName, variableValue);
		}
	}
	
	public Set<String> dom() {
		Set<String> d = new HashSet<String>();
		for (String v: this.variables.keySet()) {
			d.add(v);
		}
		return d;
	}
	
	public Context(List<Integer> values, List<? extends Function> functions, Collection<String> variables) {
		for (int v : values) {
			this.values.add(v);
		}
		for (Function f : functions) {
			if (f.argumentsCount() == 0) {
				this.terminalFunctions.add(f);
			} else {
				this.nonTerminalFunctions.add(f);
			}
		}
		if (this.terminalFunctions.isEmpty()) {
			throw new IllegalArgumentException("At least one terminal function must be defined");
		}

		if (variables.isEmpty()) {
			throw new IllegalArgumentException("At least one variable must be defined");
		}

		for (String variable : variables) {
			this.setVariable(variable, 0);
		}
	}

	public Context(int[] values, List<? extends Function> functions, Collection<String> variables) {
		for (int v : values) {
			this.values.add(v);
		}
		for (Function f : functions) {
			if (f.argumentsCount() == 0) {
				this.terminalFunctions.add(f);
			} else {
				this.nonTerminalFunctions.add(f);
			}
		}
		if (this.terminalFunctions.isEmpty()) {
			throw new IllegalArgumentException("At least one terminal function must be defined");
		}

		if (variables.isEmpty()) {
			throw new IllegalArgumentException("At least one variable must be defined");
		}

		for (String variable : variables) {
			this.setVariable(variable, 0);
		}
	}
	
	public String toString() {
		return this.variables.toString();
	}

	public int lookupVariable(String variable) {
		return this.variables.get(variable);
	}

	public void setVariable(String variable, int value) {
		this.variables.put(variable, value);
	}

	public Function getRandomNonTerminalFunction() {
		return this.roundRobinFunctionSelection();
		// return this.randomFunctionSelection();
	}

	// private Function randomFunctionSelection() {
	// int indx = this.random.nextInt(this.nonTerminalFunctions.size());
	// return this.nonTerminalFunctions.get(indx);
	// }

	private Function roundRobinFunctionSelection() {
		if (this.nextRndFunctionIndx >= this.nonTerminalFunctions.size()) {
			this.nextRndFunctionIndx = 0;
			Collections.shuffle(this.nonTerminalFunctions);
		}
		// round-robin like selection
		return this.nonTerminalFunctions.get(this.nextRndFunctionIndx++);
	}

	public Function getRandomTerminalFunction() {
		int indx = this.random.nextInt(this.terminalFunctions.size());
		Function f = this.terminalFunctions.get(indx);
		return f;
	}

	public List<Function> getTerminalFunctions() {
		return this.terminalFunctions;
	}

	public String getRandomVariableName() {
		int indx = this.random.nextInt(this.variables.keySet().size());
		int i = 0;
		for (String varName : this.variables.keySet()) {
			if (i == indx) {
				return varName;
			}
			++i;
		}
		// Unreachable code
		return this.variables.keySet().iterator().next();
	}

	public int getRandomValue() {
		return values.get(this.random.nextInt(values.size()));
	}

	public int getRandomMutationValue() {
		return (int) ((this.random.nextDouble() * (this.maxMutationValue - this.minMutationValue)) + this.minMutationValue);
	}

	public boolean hasVariables() {
		return !this.variables.isEmpty();
	}
	
	public ArrayList<Integer> possibleValues() {
		return this.values;
	}
	
	public ArrayList<Integer> getValues() {
		return this.values;
	}

}
