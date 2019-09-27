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
 * Account is a correct POJO implementation of the <code>Account.xml</code>
 * specification.
 * This uses the State Pattern (a Design Pattern from Gamma, et al.) for its 
 * implementation.  All requests are delegated to an abstract State, which 
 * has concrete subclasses Closed and Open, which respond to certain requests
 * and ignore  others.  This is a good implementation strategy to ensure that
 * no information is returned by a service, when it is in an inappropriate
 * state.
 * <p>
 * Otherwise, the account holder is recorded in a field when the Account is
 * opened; and the balance is recorded in another field, when amounts are
 * deposited or withdrawn.  This implementation obeys the preconditions in
 * the specification, which treat any attempt to deposit or withdraw a zero
 * or negative amount as an error.  Errors are treated in this example as
 * normal responses, in which bad requests have no effect, but return signal
 * Boolean results to indicate success or failure.
 * <p>
 * Suggestions are given for how to modify the source code to seed
 * faults deliberately, which will be detected during testing.
 *
 * @author Anthony J H Simons
 * @version 1.0
 */
public class Account {
	
	/**
	 * Logs the last request received by this Account.
	 */
	private String request;
	
	/**
	 * Logs the last response enacted by this Account.
	 */
	private String response;
	
	/**
	 * The last state entered by this Account.
	 */
	private State state;
	
	/**
	 * The holder of this Account, initially null.
	 */
	private String holder;
	
	/**
	 * The current balance of this Account, initially zero.
	 */
	private int balance;
	
	/**
	 * Creates this Account.  Enacts the scenario create/ok.  Sets the 
	 * holder to null and the balance to zero.  For POJO implementations,
	 * the constructor is also used to reset the service.
	 */
	public Account() {
		// implementation
		balance = 0;
		state = new Closed();
		// logging info
		request = "create";
		response = "ok";
	}

	/**
	 * Returns the last scenario that was enacted.  This State Pattern
	 * implementation logs separately the request received and the response
	 * triggered (which is state-dependent).  The name of the last scenario
	 * that was enacted is obtained by concatenating the request, "/" and 
	 * the response.
	 * @return the last scenario that was enacted.
	 */
	public String getScenario() {
		return request + "/" + response;
	}

	/**
	 * Returns the last state that was entered.  This State Pattern 
	 * implementation models the states explicitly as nested inner classes, 
	 * which also have access to the Account's fields.  The name of the
	 * current state is obtained by reflection on the class name.
	 * @return the name of the current State instance.
	 */
	public String getState() {
		return state.getClass().getSimpleName();
	}

	/**
	 * Attempts to open this Account for a given holder.  If this
	 * account is already open, enacts the scenario open/ignore.  If this
	 * account is closed and the holder is non-empty, enacts the scenario 
	 * open/ok and enters the Open state.  Otherwise, enacts the scenario 
	 * open/error and remains in the Closed state.
	 * @param holder the account holder.
	 * @return true, if open succeeded, false if it failed, or null if
	 * it was ignored.
	 */
	public Boolean open(String holder) {
		request = "open";
		return state.open(holder);
	}

	/**
	 * Attempts to close this Account.  If the account is Closed, enacts
	 * the scenario close/ignore.  If the account is Open and the balance is
	 * zero, enacts the scenario close/ok and enters the Closed state.  If
	 * the account is Open but the balance is not zero, enacts the scenario
	 * close/error and remains in the Open state.
	 * @return true, if closing succeeded, false if it failed, or null if 
	 * it was ignored.
	 */
	public Boolean close() {
		request = "close";
		return state.close();
	}

	/**
	 * Attempts to deposit an amount in this Account.  If the account is
	 * Closed, enacts deposit/ignore.  If the account is Open but the amount
	 * is not positive, enacts deposit/error; otherwise enacts deposit/ok and
	 * adds the amount to the balance.
	 * @param amount the amount to deposit.
	 * @return true, if deposit succeeded, false if it failed, or null if it
	 * was ignored.
	 */
	public Boolean deposit(int amount) {
		request = "deposit";
		return state.deposit(amount);
	}

	/**
	 * Attempts to withdraw an amount from this Account.  If the account
	 * is Closed, enacts withdraw/ignore.  If the account is Open but the 
	 * amount is not positive, enacts withdraw/error.  If the account is Open
	 * but the positive amount is greater than the current balance, enacts
	 * withdraw/blocked.  Otherwise, the positive amount is less than or
	 * equal to the current balance, so enacts withdraw/ok and subtracts the
	 * amount from the balance.
	 * @param amount the amount to withdraw.
	 * @return true, if withdraw succeeded, false if it failed, or null if it
	 * was ignored.
	 */
	public Boolean withdraw(int amount) {
		request = "withdraw";
		return state.withdraw(amount);
	}

	/**
	 * Attempts to inspect the current balance.  If the account is Closed,
	 * enacts inspect/ignore.  If the account is Open, enacts inspect/ok and
	 * returns the current balance.
	 * @return the current balance, if inspect succeeded, or null if it was
	 * ignored.
	 */
	public Integer getBalance() {
		request = "getBalance";
		return state.getBalance();
	}
	
	/**
	 * Attempts to inspect the current holder.  If the account is Closed,
	 * enacts inspect/ignore.  If the account is Open, enacts inspect/ok and
	 * returns the current balance.
	 * @return the current balance, if inspect succeeded, or null if it was
	 * ignored.
	 */
	public String getHolder() {
		request = "getHolder";
		return state.getHolder();
	}
	
	/**
	 * State is the abstract supertype State in the State Pattern.  All 
	 * requests are ignored by default; all methods return null, so as
	 * not to reveal any information (a good security principle).
	 * 
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private abstract class State {
		public Boolean open(String string) {
			response = "ignore";
			return null;
		}
		public Boolean close() {
			response = "ignore";
			return null;
		}
		public Boolean deposit(int amount) {
			response = "ignore";
			return null;
		}
		public Boolean withdraw(int amount) {
			response = "ignore";
			return null;
		}
		public Integer getBalance() {
			response = "ignore";
			return null;
		}
		public String getHolder() {
			response = "ignore";
			return null;
		}
	}
	
	/**
	 * Closed is the concrete subclass of State representing when this
	 * Account is closed.  The only valid action is to attempt to 
	 * open the account.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class Closed extends State {
		public Boolean open(String holder) {
			if (holder == null || holder.isEmpty()) {
				response = "error";
				return false;
			}
			else {
				Account.this.holder = holder;
				response = "ok";
				// Change state here.
				state = new Open();  // Try commenting this line out.
				return true;
			}
		}
	}

	/**
	 * Open is the concrete subclass of State representing when this
	 * Account is Open.  All actions apart from opening the account
	 * are valid.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class Open extends State {
		public Boolean close() {
			if (balance == 0) {
				response = "ok";
				// Change state here.
				state = new Closed();  // Try commenting this line out.
				return true;
			}
			else {
				response = "error";
				return false;
			}
		}
		public Boolean deposit(int amount) {
			if (amount > 0) {          // Try changing this to amount >= 0.
				response = "ok";
				balance += amount;
				return true;
			}
			else {
				response = "error";
				return false;
			}
		}
		public Boolean withdraw(int amount) {
			if (amount <= 0) {
				response = "error";
				return false;
			}
			else if (amount > balance) {
				response = "blocked";
				return false;
			}
			else {
				response = "ok";
				balance -= amount;
				return true;
			}
		}
		public Integer getBalance() {
			response = "ok";
			return balance;
		}
		public String getHolder() {
			response = "ok";
			return holder;
		}
	}

}
