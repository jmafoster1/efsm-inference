/**
 * Broker@Cloud Verification and Testing Tool Suite.
 * Copyright (C) 2015 Anthony J H Simons and Raluca Lefticaru, 
 * University of Sheffield, UK.  All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 * 
 * This file is "foreground software", developed as an output of 
 * the European Union collaborative research project, "Broker@Cloud: 
 * enabling continuous quality assurance and optimization in future 
 * enterprise cloud service brokers", FP7-ICT-2011-8 no. 318392, and
 * is licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *     http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or 
 * implied.  See the License for the specific language governing 
 * permissions and limitations under the License.
 * 
 * The freedoms granted by the License to incorporate, redistribute,
 * modify or extend the software apply only to "foreground software"
 * contributed by the Broker@Cloud project; and not to any proprietary 
 * software, or "background software" incorporated from other sources, 
 * which may be offered under different terms of usage.
 * 
 * Please contact the Department of Computer Science, University of
 * Sheffield, Regent Court, 211 Portobello, Sheffield S1 4DP, UK or
 * visit www.sheffield.ac.uk/dcs if you need additional information 
 * or have any questions.
 */

package uk.ac.sheffield.vtts.client.pojo;

/**
 * Dvd is an example witness-type, implementing the symbolic type used in 
 * the <code>ShoppingCart.xml</code> specification.
 * The specification language supports the built-in basic types: Void, Byte, 
 * Boolean, Character, Integer, Short, Long, Float, Double and String; and 
 * the complex types List[T], Set[T], Map[K,V] and Pair[K,V].  If a 
 * specification declares variables of any other type, this is treated as a
 * symbolic type, but it is uninterpreted, in the sense that nothing is known
 * about its structure.  It is possible to associate other values with such
 * symbolic types through the use of Maps in the expression language.  The
 * only necessary feature of symbolic types is that instances must be able
 * to be distinguished.  This is achieved using an ID, which by convention
 * is the first three letters of the type-name, in lower case, followed by
 * an incrementing digit, starting from 1.
 * <p>
 * During verification, symbolic types are modelled as instances of the model
 * type Entity, which records the ID name and the symbolic type name.  During 
 * testing, we expect these symbolic types to translate into domain-specific
 * object types in the application, having the same type name.  Testing will
 * need to create instances of these domain types, which we refer to as
 * witness-types, since they must provide witness-values for use during
 * testing.  Any witness-type must provide a default constructor, and a 
 * constructor that accepts a String ID value.  It must also define the 
 * hashCode() method to hash on the ID value, and the equals() method to
 * compare two ID values for equality.  Apart from this, it may offer 
 * whatever methods are needed (typically, to encode internally properties
 * expressed in the model through Maps).
 * <p>
 * The Dvd class shows how to provide such a witness-type, which requires:  
 * a default constructor that generates the first witness value; a 
 * constructor-from-String that accepts a String ID value; an equals() 
 * method that compares a pair of IDs; and a hashCode() method that hashes
 * on the ID.  The directory path to witness-types must be known to the
 * generated test-driver.  Here, we have copied Dvd to the folders
 * <code>client/pojo</code>, <code>client/rs</code> and 
 * <code>client/ws</code> to make it available to generated POJO, SOAP and 
 * REST test-drivers which expect to find it there.
 * 
 * @author Anthony J H Simons
 * @version Broker@Cloud 1.0
 */
public class Dvd {

	/**
	 * The identifier distinguishing each Dvd uniquely from any other.
	 */
	private String identifier;
	
	/**
	 * The default constructor, which always creates the first Dvd in the
	 * monotonic sequence, with the identifier: "dvd1".
	 */
	public Dvd() {
		identifier = "dvd1";
	}
	
	/**
	 * The from-String constructor that is required for a witness-type.
	 * By convention, the identifier for the type Dvd is expected to be
	 * the lower case character string: "dvd" followed by an incrementing
	 * digit, starting from 1.
	 * @param identifier a String identifier.
	 */
	public Dvd(String identifier) {
		this.identifier=identifier;
	}
	
	/**
	 * Returns a quasi-unique hash code for this Dvd.  Hashes on the value 
	 * of the identifier.  For safety, returns zero if the identifier is 
	 * null, although this should not happen in practice.
	 */
	public int hashCode() {
		return identifier == null ? 0 : identifier.hashCode();
	}
	
	/**
	 * Tests whether this Dvd and another object are equal.  If they are 
	 * identical, returns true immediately.  Otherwise, tests whether the
	 * other is an instance of Dvd, then compares the values of their 
	 * identifiers.  For safety, still works if either identifier is null,
	 * although this should not happen in practice.
	 */
	public boolean equals(Object other) {
		if (other == this)
			return true;
		else if (other instanceof Dvd) {
			Dvd dvd = (Dvd) other;
			if (identifier == null)
				return dvd.identifier == null;
			else
				return identifier.equals(dvd.identifier);
		}
		else
			return false;
	}
	
}
