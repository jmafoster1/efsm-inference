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

import java.util.List;
import java.util.Set;

import com.microsoft.z3.ArithExpr;

public interface Function {

	int eval(Expression expression, Context context);

	int argumentsCount();

	boolean isVariable();

	boolean isNumber();

	boolean isCommutative();

	String print(Expression expression);

	List<Integer> getCoefficients(Expression expression);

	void setCoefficients(Expression expression, List<Integer> coefficients, int startIndex);

	int coefficientsCount();
	
	int height(Expression expression);
	
	Set<String> vars(Expression expression);

	ArithExpr toZ3(Expression expression, com.microsoft.z3.Context ctx);

}
