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

import java.util.HashMap;
import java.util.Map;

/**
 * Login is a correct POJO implementation of the <code>Login.xml</code> 
 * specification.
 * This uses the State Pattern (a Design Pattern from Gamma, et al.) for its 
 * implementation.  All requests are delegated to an abstract State, which 
 * has concrete subclasses LoggedOut and LoggedIn, which respond to certain 
 * requests and ignore others.  This is a good implementation strategy to
 * ensure that no information is returned by a service, when it is in an 
 * inappropriate state.  
 * <p>
 * Otherwise, a Map is used to represent the table of known users and
 * passwords; one of these corresponds to the valid test user from the 
 * <code>Login.xml</code> specification.  This simple example performs 
 * no other actions apart from controlling the logged state of the user.
 * <p>
 * Suggestions are given for how to modify the source code to seed
 * faults deliberately, which will be detected during testing.
 *
 * @author Anthony J H Simons
 * @version 1.0
 */
public class Login {
	
	/**
	 * Logs the last request received by this Login.
	 */
	private String request;
	
	/**
	 * Logs the last response enacted by this Login.
	 */
	private String response;
	
	/**
	 * The last state entered by this Login.
	 */
	private State state;
	
	/**
	 * The table of known users and passwords.  Basically to show that
	 * the implementation can be done however you like.
	 */
	private Map<String, String> userTable;
	
	/**
	 * Creates this Login service.  Enacts the scenario create/ok.  Creates
	 * a table of valid users with their passwords, and then enters the 
	 * LoggedOut state.  For POJO implementations, the constructor is also
	 * used to reset the service.
	 */
	public Login() {
		// implementation
		userTable = new HashMap<String, String>();
		userTable.put("Jane Good", "serendipity");  // a valid user
		userTable.put("John Right", "abracadabra");
		state = new LoggedOut();
		// logging info
		request = "create";
		response = "ok";
	}

	/**
	 * Returns the last scenario that was enacted.  This implementation logs 
	 * separately the request received and the response that was triggered 
	 * (which is state-dependent).  The name of the last scenario that was
	 * enacted is obtained by concatenating the request, "/" and the response.
	 * @return the last scenario that was enacted.
	 */
	public String getScenario() {
		return request + "/" + response;
	}

	/**
	 * Returns the last state that was entered.  This implementation models
	 * the states explicitly as nested inner classes, which also have access
	 * to the Account's fields.  The name of the current state is obtained by
	 * reflection on the class name.
	 * @return the name of the current State instance.
	 */
	public String getState() {
		return state.getClass().getSimpleName();
	}

	/**
	 * Attempts to log a user into the system.  If the state is already
	 * LoggedIn, enacts the scenario login/ignore.  If the state is
	 * LoggedOut, checks whether the user and corresponding password are
	 * correct.  If so, enacts the scenario login/ok and changes the state
	 * to LoggedIn.  Otherwise enacts the scenario login/error and leaves
	 * the state unchanged as LoggedOut.
	 * @param username the user name.
	 * @param password the password.
	 */
	public void login(String username, String password) {
		request = "login";
		state.login(username, password);
	}

	/**
	 * Attempts to log a user out of the system.  If the state is already
	 * LoggedOut, enacts the scenario logout/ignore and leaves the state
	 * unchanged.  Otherwise, enacts the scenario logout/ok and changes
	 * the state to LoggedOut.
	 */
	public void logout() {
		request = "logout";
		state.logout();
	}

	/**
	 * Attempts to time a user out of the system.  If the state is already
	 * LoggedOut, enacts the scenario timeout/ignore and leaves the state
	 * unchanged.  Otherwise, enacts the scenario timeout/ok and changes
	 * the state to LoggedOut.
	 */
	public void timeout() {
		request = "timeout";
		state.timeout();
	}
	
	/**
	 * State is the abstract supertype State in the State Pattern.  All 
	 * requests are ignored by default; all methods return void in this
	 * example, so no information is returned.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private abstract class State {
		public void login(String username, String password) {
			response = "ignore";
		}
		public void timeout() {
			response = "ignore";
		}
		public void logout() {
			response = "ignore";
		}
	}
	
	/**
	 * LoggedOut is the concrete subclass of State representing when this
	 * Login service is logged out.  The only valid action is to attempt to
	 * login.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class LoggedOut extends State {
		public void login(String username, String password) {
			if (userTable.containsKey(username) 
					&& userTable.get(username).equals(password)) {
				response = "ok";
				// change state
				state = new LoggedIn();  // try commenting out this line
			}
			else {
				response = "error";
			}
		}
	}
	
	/**
	 * LoggedIn is the concrete subclass of State representing when this
	 * Login service is logged in.  The only valid actions are to logout,
	 * or timeout.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class LoggedIn extends State {
		public void logout() {
			response = "ok";
			// change state
			state = new LoggedOut();  // try commenting out this line
		}
		public void timeout() {
			response = "ok";
			// change state
			state = new LoggedOut();
		}
	}

}
