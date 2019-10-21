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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import com.lagodiuk.gp.symbolic.interpreter.Context;
import com.lagodiuk.gp.symbolic.interpreter.Expression;

public class TabulatedFunctionFitness implements ExpressionFitness {

	private List<Target> targets = new LinkedList<Target>();

	public TabulatedFunctionFitness(Target... targets) {
		for (Target target : targets) {
			this.targets.add(target);
		}
	}

	public TabulatedFunctionFitness(List<Target> targets) {
		this.targets.addAll(targets);
	}
	
	public List<Target> getTargets() {
		return this.targets;
	}
	
	@Override
	public double fitness(Expression expression, Context context) {
		double diff = 0.0;
		double mistakes = 0.0;
		Set<String> totalUsedVars = new HashSet<String>();
		
		for (Target target : this.targets) {
			Set<String> usedVars = target.getContextState().keySet();
			for (String v: usedVars) {
				totalUsedVars.add(v);
			}
			
			double targetValue = target.getTargetValue();
			
			Set<String> undef = context.dom();
			undef.removeAll(usedVars);
			context.setup(target.getContextState().entrySet());

			double minErr = Double.POSITIVE_INFINITY;
			
			if (undef.isEmpty()) {
				double offBy = Math.abs(targetValue - expression.eval(context));
				if (offBy < minErr) {
					minErr = offBy;
				}
			}
			else {
				for (String v: undef) {
					for (int i: context.getValues()) {
						context.setVariable(v, i);
						double offBy = Math.abs(targetValue - expression.eval(context));
						if (offBy < minErr) {
							minErr = offBy;
						}
					}
				}
			}
			
			diff += minErr;
			if (minErr > 0) {
				mistakes++;
			}
		}
		
		totalUsedVars.removeAll(expression.vars());
		
		return mistakes + (diff/this.targets.size()) + totalUsedVars.size() + expression.vars().size();
	}
	
//	This is solidly OK most of the time.
//	public double fitness(Expression expression, Context context) {
//		int diff = 0;
//		int mistakes = 0;
//		
//		for (Target target : this.targets) {
//			Set<String> undef = context.dom();
//			undef.removeAll(target.getContextState().keySet());
//			
//			for (String v: undef) {
//				context.setVariable(v, context.getRandomValue());
//			}
//			context.setup(target.getContextState().entrySet());
//			
//			int targetValue = target.getTargetValue();
//			int calculatedValue = expression.eval(context);
//			double offBy = Math.abs(targetValue - calculatedValue);
//			diff += offBy/(offBy+1);
//			if (targetValue != calculatedValue) {
//				mistakes++;
//			}
//		}
//		
//		return mistakes + (diff/this.targets.size());
//	}
	
}
