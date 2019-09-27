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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * DocumentStore is a correct POJO implementation of the 
 * <code>DocumentStore.xml</code> 
 * specification.  This uses the State Pattern (a Design Pattern from Gamma,
 * et al.) for its implementation.  All requests are delegated to an abstract
 * State, which has concrete subclasses LoggedOut and LoggedIn, which respond
 * to certain requests and ignore others.  This is a good implementation 
 * strategy to ensure that no information is returned by a service, when it
 * is in an inappropriate state.
 * <p>
 * Otherwise, the DocumentStore consists of a Map from customers to their own 
 * private storage space; the space consists of indexed Document sets, where 
 * each index maps to a List of versions of the Document.  Each customer has
 * previously registered and is given an SLA specifying a storage allocation,
 * in terabytes, and an encryption standard.  This example uses a witness-type
 * for the Document, and also demonstrates how a service may throw exceptions.
 * This service defines two kinds of RuntimeException, which mimic "Not Found"
 * kinds of http error.  These are thrown under suitable conditions, such that
 * the test-driver must expect these exceptions during testing.
 * <p>
 * Suggestions are given for how to modify the source code to seed
 * faults deliberately, which will be detected during testing.
 *
 * @author Anthony J H Simons
 * @version 1.0
 */
public class DocumentStore {
	
	/**
	 * Logs the last request received by this DocumentStore.
	 */
	private String request;
	
	/**
	 * Logs the last response enacted by this DocumentStore.
	 */
	private String response;
	
	/**
	 * The last state entered by this DocumentStore.
	 */
	private State state;
	
	/**
	 * The table of known users and passwords.  Basically to show that
	 * the implementation can be done however you like.
	 */
	private static final Map<String, String> USERS;
	static {
		USERS = new HashMap<String, String>();
		USERS.put("Jane Good", "serendipity");  // a valid test user
		USERS.put("John Right", "abracadabra");		
	}
	
	/**
	 * The table of known users and specified encryption levels.  Basically
	 * to show that the implementation can be done however you like.
	 */
	private static final Map<String, Integer> CRYPT;
	static {
		CRYPT = new HashMap<String, Integer>();
		CRYPT.put("Jane Good", 192);  // a valid test user
		CRYPT.put("John Right", 192);		
	}

	/**
	 * The table of known users and maximum storage allocation.  Basically
	 * to show that the implementation can be done however you like.
	 */
	private static final Map<String, Integer> ALLOC;
	static {
		ALLOC = new HashMap<String, Integer>();
		ALLOC.put("Jane Good", 100);  // a valid test user
		ALLOC.put("John Right", 70);		
	}
	
	/**
	 * The table of known users and their personal document storage.  
	 * Basically to show that the implementation can be done however you 
	 * like.
	 */
	private static Map<String, Map<Integer, List<Document>>> STORE;
	static {
		STORE = new HashMap<String, Map<Integer, List<Document>>>();
		STORE.put("Jane Good", new HashMap<Integer, List<Document>>());  // a valid test user
		STORE.put("John Right", new HashMap<Integer, List<Document>>());		
	}
	
	/**
	 * When resetting this service, we have to give each customer an empty
	 * personal document storage space.
	 */
	private void reset() {
		for (String user : STORE.keySet()) {
			STORE.put(user, new HashMap<Integer, List<Document>>());
		}
	}
	
	/**
	 * The name of the currently logged-in customer.  This is used to access
	 * different values and permissions allocated to this customer.
	 */
	private String user;
	
	/**
	 * The document store for the logged-in customer.  This is a cache of 
	 * this customer's personal document storage, and is bound when this
	 * customer has logged in.
	 */
	private Map<Integer, List<Document>> store;
	
	/**
	 * Creates this DocumentStore.  Resets this DocumentStore so that every
	 * customer has a full storage allocation.  Enacts create/ok and enters
	 * the LoggedOut state.
	 */
	public DocumentStore() {
		// implementation
		reset();
		state = new LoggedOut();
		// logging
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
	 * which also have access to the DocumentStore's fields.  The name of the
	 * current state is obtained by reflection on the class name.
	 * @return the name of the current State instance.
	 */
	public String getState() {
		return state.getClass().getSimpleName();
	}

	/**
	 * If LoggedOut, attempts to login with the given credentials.  Either
	 * enacts login/ok, enters the LoggedIn state, and returns the user's 
	 * maximum storage allocation and encryption standard; or enacts 
	 * login/error and remains in the LoggedOut state.  Otherwise, enacts
	 * login/ignore.
	 * @param username the username of a customer.
	 * @param password the password of this user.
	 * @return an array with the storage allocation and encryption standard, 
	 * or a pair of nulls.
	 */
	public Object[] login(String username, String password) {
		request = "login";
		return state.login(username, password);
	}
	
	/**
	 * If LoggedIn, enacts logout/ok, clears the current customer's cached 
	 * information and enters the LoggedOut state.  Otherwise, enacts
	 * login/ignore.
	 */
	public void logout() {
		request = "logout";
		state.logout();
	}
	
	/**
	 * If LoggedIn, enacts getEncryption/ok and returns the encryption
	 * standard for the customer.  Otherwise enacts getEncryption/ignore.
	 * @return the encryption standard, or null.
	 */
	public Integer getEncryption() {
		request = "getEncryption";
		return state.getEncryption();
	}

	/**
	 * If LoggedIn, enacts getStorageLimit/ok and returns the allocated 
	 * storage for the customer.  Otherwise enacts getStorageLimit/ignore.
	 * @return the maximum storage allocated, or null.
	 */
	public Integer getStorageLimit() {
		request = "getStorageLimit";
		return state.getStorageLimit();
	}

	/**
	 * If LoggedIn, enacts getStorageUsed/ok and returns the storage used
	 * by the customer.  Otherwise enacts getStorageUsed/ignore.
	 * @return the storage currently used, or null.
	 */
	public Integer getStorageUsed() {
		request = "getStorageUsed";
		return state.getStorageUsed();
	}

	/**
	 * If LoggedIn, attempts to store a Document against the given docid.  If
	 * an out-of-range docid is given, enacts putDocument/error and throws a
	 * BadDocumentIdentifier exception.  Otherwise, if the size of the current
	 * Document would cause the customer to reach their storage allocation 
	 * limit, enacts putDocument/blocked and returns a tuple of the available
	 * storage and null (no new version).  Otherwise, if the docid relates to
	 * an existing Document, enacts putDocument/update and stores the Document
	 * as the last version in the list of Documents indexed against the docid.
	 * Otherwise, the docid is one greater than the last version, and enacts
	 * putDocument/new to create a new list to hold versions of the Document
	 * and adds the Document.  If LoggedOut, enacts putDocument/ignore.
	 * @param docid the index of the Document.
	 * @param document the Document.
	 * @return a tuple of the remaining storage left; and the latest version 
	 * number for the Document, or null if the Document was not stored.
	 * @throws BadDocumentIdentifier if an out-of-range docid was provided.
	 */
	public Object[] putDocument(Integer docid, Document document) 
			throws BadDocumentIdentifier {
		request = "putDocument";
		return state.putDocument(docid, document);
	}
	
	/**
	 * If LoggedIn, attempts to retrieve a Document with the given docid.  If
	 * an out-of-range docid is given, enacts getDocument/error and throws a
	 * BadDocumentIdentifier exception.  Otherwise, if the size of the version
	 * list associated with the docid is empty, enacts getDocument/absent and
	 * throws a BadVersionIdentifier exception.  Otherwise, retrieves the last
	 * version of the Document, enacting getDocument/ok and returning a tuple
	 * of the Document and its last version number. If LoggedOut, enacts 
	 * getDocument/ignore.
	 * @param docid the index of the Document.
	 * @return the latest version of the Document.
	 * @throws BadDocumentIdentifier if an out-of-range docid was provided.
	 * @throws BadVersionIdentifier if no versions of this Document exist.
	 */
	public Document getDocument(Integer docid) 
			throws BadDocumentIdentifier, BadVersionIdentifier {
		request = "getDocument";
		return state.getDocument(docid);
	}
	
	/**
	 * If LoggedIn, attempts to retrieve a Document with the given docid and
	 * version number.  If an out-of-range docid is given, enacts 
	 * getVersion/error and throws a BadDocumentIdentifier exception.  
	 * Otherwise, if the version is out-of-range, enacts getVersion/absent
	 * and throws a BadVersionIdentifier exception.  Otherwise, retrieves the 
	 * given version of the Document, enacting getVersion/ok and returns the 
	 * Document. If LoggedOut, enacts getVersion/ignore.
	 * @param docid the index of the Document.
	 * @param version the version number.
	 * @return the Document.
	 * @throws BadDocumentIdentifier if an out-of-range docid was provided.
	 * @throws BadVersionIdentifier if an out-of-range version was provided.
	 */
	public Document getVersion(Integer docid, Integer version) 
			throws BadDocumentIdentifier, BadVersionIdentifier {
		request = "getVersion";
		return state.getVersion(docid, version);
	}
	
	/**
	 * If LoggedIn, attempts to delete a Document with the given docid and
	 * version number.  If an out-of-range docid is given, enacts 
	 * deleteVersion/error and throws a BadDocumentIdentifier exception.  
	 * Otherwise, if the version is out-of-range, enacts deleteVersion/absent
	 * and throws a BadVersionIdentifier exception.  Otherwise, deletes the 
	 * given version of the Document, enacting deleteVersion/ok and returns the 
	 * remaining storage available. If LoggedOut, enacts deleteVersion/ignore.
	 * @param docid the index of the Document.
	 * @param version the version number.
	 * @return the remaining available storage.
	 * @throws BadDocumentIdentifier if an out-of-range docid was provided.
	 * @throws BadVersionIdentifier if an out-of-range version was provided.
	 */
	public Integer deleteVersion(Integer docid, Integer version) 
			throws BadDocumentIdentifier, BadVersionIdentifier {
		request = "deleteVersion";
		return state.deleteVersion(docid, version);
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
		public Object[] login(String username, String password) {
			response = "ignore";
			return new Object[] {null, null};
		}
		public void logout() {
			response = "ignore";
		}
		public Integer getEncryption() {
			response = "ignore";
			return null;
		}
		public Integer getStorageLimit() {
			response = "ignore";
			return null;
		}
		public Integer getStorageUsed() {
			response = "ignore";
			return null;
		}
		public Object[] putDocument(Integer docid, Document document) 
				throws BadDocumentIdentifier {
			response = "ignore";
			return new Object[] {null, null};
		}
		public Document getDocument(Integer docid) 
				throws BadDocumentIdentifier, BadVersionIdentifier {
			response = "ignore";
			return null;
		}
		public Document getVersion(Integer docid, Integer version) 
				throws BadDocumentIdentifier, BadVersionIdentifier {
			response = "ignore";
			return null;
		}
		public Integer deleteVersion(Integer docid, Integer version) 
				throws BadDocumentIdentifier, BadVersionIdentifier {
			response = "ignore";
			return null;
		}
	}
	
	/**
	 * LoggedOut is the concrete subclass of State representing when the
	 * customer is logged out of the service.  The only valid action is
	 * to login, which can succeed with login/ok and change to the state
	 * LoggedIn; or fail with login/error and remain in this state.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class LoggedOut extends State {
		public Object[] login(String username, String password) {
			Object[] result = new Object[] {null, null};
			if (USERS.containsKey(username) 
					&& USERS.get(username).equals(password)) {
				response = "ok";
				// Set up the current user's status
				user = username;
				store = STORE.get(username);
				// Return the current user's SLA
				result = new Object[] {
					ALLOC.get(username),	// try swapping these values, so
					CRYPT.get(username)		// they come in the wrong order
				};
				state = new LoggedIn();  // try commenting out this line
			}
			else {
				response = "error";
			}
			return result;
		}
	}
	
	private class LoggedIn extends State {
		public void logout () {
			response = "ok";
			user = null;
			store = null;
			state = new LoggedOut();  // try commenting out this line
		}
		public Integer getEncryption() {
			response = "ok";
			return CRYPT.get(user);
		}
		public Integer getStorageLimit() {
			response = "ok";
			return ALLOC.get(user);
		}
		public Integer getStorageUsed() {
			response = "ok";
			// Use a helper-method to compute storage used.
			return getUsage();
		}
		// A helper-method that is used in several places.
		private int getUsage() {
			int storageUsed = 0;
			for (List<Document> versions : store.values()) {
				for (Document document : versions) {
					storageUsed += document.size();
				}
			}
			return storageUsed;			
		}
		public Object[] putDocument(Integer docid, Document document) 
				throws BadDocumentIdentifier {
			Object[] result = new Object[]{null, null};
			// Use a helper-method to compute storage used.
			int storageUsed = getUsage();
			int storageLeft = ALLOC.get(user) - storageUsed;
			int nextDocid = store.size() + 1;
			if (docid <= 0 || docid > nextDocid) {
				response = "error";
				throw new BadDocumentIdentifier();
			}
			else if (storageUsed + document.size() >= ALLOC.get(user)) {
				response = "blocked";
				result = new Object[]{storageLeft, null};
			}
			else if (docid < nextDocid) {
				response = "update";
				List<Document> versions = store.get(docid);
				versions.add(document);
				storageLeft -= document.size();
				result = new Object[]{storageLeft, versions.size()};
			}
			else {
				response = "new";
				List<Document> versions = new ArrayList<Document>();
				versions.add(document);
				store.put(docid, versions);
				storageLeft -= document.size();
				result = new Object[]{storageLeft, versions.size()};				
			}
			return result;
		}
		public Document getDocument(Integer docid) 
				throws BadDocumentIdentifier, BadVersionIdentifier {
			Document result = null;
			if (docid <= 0 || docid > store.size()) {
				response = "error";
				throw new BadDocumentIdentifier();
			}
			else {
				List<Document> versions = store.get(docid);
				if (versions.isEmpty()) {
					response = "absent";
					throw new BadVersionIdentifier();
				}
				else {
					response = "ok";
					int version = versions.size();
					result = versions.get(version -1);
				}
			}
			return result;
		}
		public Document getVersion(Integer docid, Integer version) 
				throws BadDocumentIdentifier, BadVersionIdentifier {
			Document result = null;
			if (docid <= 0 || docid > store.size()) {
				response = "error";
				throw new BadDocumentIdentifier();
			}
			else {
				List<Document> versions = store.get(docid);
				if (version <= 0 || version > versions.size()) {
					response = "absent";
					throw new BadVersionIdentifier();
				}
				else {
					response = "ok";
					result = versions.get(version -1);
				}
			}
			return result;
		}
		public Integer deleteVersion(Integer docid, Integer version) 
				throws BadDocumentIdentifier, BadVersionIdentifier {
			Integer result = null;
			if (docid <= 0 || docid > store.size()) {
				response = "error";
				throw new BadDocumentIdentifier();
			}
			else {
				List<Document> versions = store.get(docid);
				if (version <= 0 || version > versions.size()) {
					response = "absent";
					throw new BadVersionIdentifier();
				}
				else {
					response = "ok";
					versions.remove(version -1);
					result = ALLOC.get(user) - getUsage();
				}
			}
			return result;
		}
	}
	
	/**
	 * BadDocumentIdentifier is a kind of RuntimeException thrown by this
	 * service.  This is similar to a "Not Found" kind of error, to show
	 * how services can throw Exceptions.  The error text must match the
	 * Failure message in the specification.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	public class BadDocumentIdentifier extends RuntimeException {
		private static final long serialVersionUID = -7020220146701184141L;
		public BadDocumentIdentifier() {
			super("Bad document identifier");
		}
	}
	
	/**
	 * BadVersionIdentifier is a kind of RuntimeException thrown by this
	 * service.  This is similar to a "Not Found" kind of error, to show
	 * how services can throw Exceptions.  The error text must match the
	 * Failure message in the specification.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	public class BadVersionIdentifier extends RuntimeException {
		private static final long serialVersionUID = 469735834852191617L;
		public BadVersionIdentifier() {
			super("Bad version identifier");
		}
	}
	
}
