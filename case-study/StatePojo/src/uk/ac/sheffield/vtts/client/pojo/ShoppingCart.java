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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * ShoppingCart is a correct POJO implementation of the 
 * <code>ShoppingCart.xml</code> 
 * specification.  This uses the State Pattern (a Design Pattern from Gamma,
 * et al.) for its implementation.  All requests are delegated to an abstract
 * State, which has concrete subclasses Ready, Shopping, Checkout and 
 * Payment, which respond to certain requests and ignore  others.  This is a
 * good implementation strategy to ensure that no information is returned by 
 * a service, when it is in an inappropriate state.
 * <p>
 * Otherwise, the shopping cart and the current stock are stored in Maps.  As
 * items are added to the cart, they are subtracted from the stock and the
 * total cost of purchases is recalculated.  Once there are items in the cart
 * it is possible to go to the checkout.  At the checkout, if valid billing
 * information is supplied, payment can be initiated.  This must be confirmed
 * for the payment to go through.  At any previous step, the user may exit
 * the shop with no obligation.  This example uses a user-defined symbolic
 * type, called Dvd, to model the products sold in the shop.
 * <p>
 * Suggestions are given for how to modify the source code to seed
 * faults deliberately, which will be detected during testing.
 *
 * @author Anthony J H Simons
 * @version 1.0
 */
public class ShoppingCart {
	
	/**
	 * Logs the last request received by this ShoppingCart.
	 */
	private String request;
	
	/**
	 * Logs the last response enacted by this ShoppingCart.
	 */
	private String response;
	
	/**
	 * The last state entered by this ShoppingCart.
	 */
	private State state;
	
	/**
	 * Suitable stock levels corresponding to the specification.  The main
	 * tests are based on Dvds d1, d2, where d1 is available and d2 is not.
	 */
	private static final Map<Dvd, Integer> INITIAL_STOCK;
	static {
		INITIAL_STOCK = new HashMap<Dvd, Integer>();
		INITIAL_STOCK.put(new Dvd("dvd1"), 100);
		INITIAL_STOCK.put(new Dvd("dvd2"), 0);
		INITIAL_STOCK.put(new Dvd("dvd3"), 5);
		INITIAL_STOCK.put(new Dvd("dvd4"), 2);
		INITIAL_STOCK.put(new Dvd("dvd5"), 20);
	}
	
	/**
	 * Suitable prices for the Dvds corresponding to the specification.
	 */
	private static final Map<Dvd, Float> PRICE_LIST;
	static {
		PRICE_LIST = new HashMap<Dvd, Float>();
		PRICE_LIST.put(new Dvd("dvd1"), 7.99F);
		PRICE_LIST.put(new Dvd("dvd2"), 7.99F);
		PRICE_LIST.put(new Dvd("dvd3"), 9.99F);
		PRICE_LIST.put(new Dvd("dvd4"), 9.99F);
		PRICE_LIST.put(new Dvd("dvd5"), 5.99F);
	}
	
	private static final Set<Integer> VALID_BILLING;
	static {
		VALID_BILLING = new HashSet<Integer>();
		// The known good billing information
		VALID_BILLING.add(113623567);  // Try modifying this digit
		VALID_BILLING.add(235133353);
		VALID_BILLING.add(940633632);
	}
	
	/**
	 * The current levels of stock in the shop.
	 */
	private Map<Dvd, Integer> currentStock;
	
	/**
	 * The current levels of product in the cart.
	 */
	private Map<Dvd, Integer> shoppingCart;
	
	/**
	 * The total cost of purchases added to the cart.
	 */
	private float totalCost;
	
	/**
	 * Creates this ShoppingCart. Enacts the scenario create/ok.  Sets the 
	 * shopping cart to empty, the stock to its initial level, and the total
	 * cost to zero.  For POJO implementations, the constructor is also used
	 * to reset the service.
	 */
	public ShoppingCart() {
		// Implementation
		currentStock = new HashMap<Dvd, Integer>(INITIAL_STOCK);
		shoppingCart = new HashMap<Dvd, Integer>();
		totalCost = 0.0F;
		state = new Ready();
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
	 * Enters the Shopping state from either the Ready state (to start 
	 * shopping) or from the Checkout state (to return to shopping for extra
	 * items before finally making payment).  Enacts enterShop/ok if in a
	 * suitable state; otherwise enacts enterShop/ignore.
	 */
	public void enterShop() {
		request = "enterShop";
		state.enterShop();
	}

	/**
	 * Exits the shop from every state, cancelling every action made so far.
	 * Always enacts exitShop/ok.
	 */
	public void exitShop() {
		request = "exitShop";
		state.exitShop();
	}

	/**
	 * In the Shopping state, adds one Dvd purchase to the cart, if enough
	 * stock exists.  If there are copies, enacts addItem/ok and adds the 
	 * Dvd to the cart, removing it from the current stock, and adds the
	 * cost of the Dvd to the total cost.  Otherwise, enacts addItem/error,
	 * since there are no copies.  In other states, enacts addItem/ignore.
	 * @param dvd the Dvd to add to the cart.
	 * @return the quantity of this Dvd in the cart.
	 */
	public Integer addItem(Dvd dvd) {
		request = "addItem";
		return state.addItem(dvd);
	}

	/**
	 * In the Shopping state, removes one Dvd purchase from the cart, if a
	 * copy exists in the cart.  If there are copies, enacts removeItem/ok
	 * and removes the Dvd from the cart, restoring it to the current stock,
	 * and subtracts the cost of the Dvd from the total cost.  Otherwise,
	 * enacts removeItem/error, since there are no copies.  In other states,
	 * enacts removeItem/ignore.
	 * @param dvd the Dvd to take out of the cart.
	 * @return the quantity of this Dvd in the cart.
	 */
	public Integer removeItem(Dvd dvd) {
		request = "removeItem";
		return state.removeItem(dvd);
	}

	/**
	 * In the Shopping state, removes all Dvd purchases from the cart.  Sets
	 * the shopping cart to empty, and the stock to its original levels, and
	 * the total cost to zero.  Enacts clearItems/ok in this state, but
	 * clearItems/ignore in all other states.
	 */
	public void clearItems() {
		request = "clearItems";
		state.clearItems();
	}

	/**
	 * Attempts to checkout from the Shopping state.  If there are items in
	 * the cart, changes state to Checkout and returns true.  Otherwise, the
	 * state is unchanged and false is returned.
	 * @return true, if checkout succeeded.
	 */
	public Boolean checkout() {
		request = "checkout";
		return state.checkout();
	}

	/**
	 * In the Checkout or Payment states, enacts getBill/ok and returns the
	 * total cost of items in the cart.  In other states, enacts 
	 * getBill/ignore.
	 * @return the total amount due, or null if ignored.
	 */
	public Float getBill() {
		request ="getBill";
		return state.getBill();
	}

	/**
	 * In the Checkout state, attempts to pay the bill.  If correct billing
	 * information is provided, enacts payBill/ok, returns true and changes 
	 * to the Payment state; otherwise enacts payBill/error, returns false 
	 * and remains in the Checkout state.  In other states, enacts
	 * payBill/ignore.
	 * @param billingInfo an Integer payment authorisation.
	 * @param addressInfo the shipping address.
	 * @return true, if valid billing information was given.
	 */
	public Boolean payBill(int billingInfo, String addressInfo) {
		request = "payBill";
		return state.payBill(billingInfo, addressInfo);
	}
	
	/**
	 * In the Payment state, confirms the payment and shipping address that
	 * were previously supplied and makes the payment.  Enacts confirm/ok and
	 * returns the amount that was paid.  Resets the service and enters the 
	 * Ready state.  In all other states, enacts confirm/ignore.
	 * @return the amount paid, or null.
	 */
	public Float confirm() {
		request = "confirm";
		return state.confirm();
	}
	
	/**
	 * State is the abstract supertype State in the State Pattern.  Most 
	 * requests are ignored by default and methods return null, except for
	 * exitShop, which always succeeds, enacts exitShop/ok and changes to
	 * the Ready state.
	 * 
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private abstract class State {
		public void enterShop() {
			response = "ignore";
		}
		public void exitShop() {
			response = "ok";  // resets from every state.
			currentStock = new HashMap<Dvd, Integer>(INITIAL_STOCK);
			shoppingCart = new HashMap<Dvd, Integer>();
			totalCost = 0.0F;
			state = new Ready();
		}
		public Integer addItem(Dvd dvd) {
			response = "ignore";
			return null;
		}
		public Integer removeItem(Dvd dvd) {
			response = "ignore";
			return null;
		}
		public void clearItems() {
			response = "ignore";
		}
		public Boolean checkout() {
			response = "ignore";
			return null;
		}
		public Float getBill() {
			response = "ignore";
			return null;
		}
		public Boolean payBill(int billingInfo, String addressInfo) {
			response = "ignore";
			return null;
		}
		public Float confirm() {
			response = "ignore";
			return null;
		}
	}
	
	/**
	 * Ready is the concrete subclass of State representing when this 
	 * ShoppingCart is idle, before commencing, or after completing, sundry
	 * purchases.  The only valid action is to enter the shop.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class Ready extends State {
		public void enterShop() {
			response = "ok";
			state = new Shopping();
		}
	}
	
	/**
	 * Shopping is the concrete subclass of State representing when this
	 * ShoppingCart is able to add and remove items.  Adding a Dvd increases
	 * the quantity in the cart, and decreases the quantity in the shop. 
	 * Removing a Dvd has the opposite effect.  Clearing resets the state of
	 * the cart and stock to their initial levels.  Checkout moves to the 
	 * Checkout state, so long as there are items in the cart.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class Shopping extends State {
		public Integer addItem(Dvd dvd) {
			if (currentStock.get(dvd) > 0) {
				response = "ok";
				int count = (shoppingCart.containsKey(dvd) ? 
						shoppingCart.get(dvd) : 0);
				shoppingCart.put(dvd, count + 1);
				currentStock.put(dvd, currentStock.get(dvd) - 1);
				totalCost += PRICE_LIST.get(dvd);
			}
			else
				response = "error";
			return shoppingCart.containsKey(dvd) ? 
					shoppingCart.get(dvd) : 0;
		}
		public Integer removeItem(Dvd dvd) {
			int count = shoppingCart.containsKey(dvd) ?
					shoppingCart.get(dvd) : 0;
			if (count > 0) {
				response = "ok";
				shoppingCart.put(dvd, count - 1);
				currentStock.put(dvd, currentStock.get(dvd) + 1);
				totalCost -= PRICE_LIST.get(dvd);
			}
			else
				response = "error";
			return shoppingCart.containsKey(dvd) ? 
					shoppingCart.get(dvd) : 0;
		}
		public void clearItems() {
			response = "ok";
			currentStock = new HashMap<Dvd, Integer>(INITIAL_STOCK);
			shoppingCart = new HashMap<Dvd, Integer>();
			totalCost = 0.0F;
		}
		public Boolean checkout() {
			if (shoppingCart.isEmpty()) {
				response = "error";
				return false;
			}
			else {
				response = "ok";
				state = new Checkout();
				return true;
			}
		}
	}
	
	/**
	 * Checkout is the concrete subclass of State representing when this
	 * ShoppingCart is able to accept payment.  Allows the user to see the
	 * amount due, enacting getBill/ok.  If valid billing information and a
	 * shipping address are given, enacts payBill/ok and changes to the 
	 * Payment state; otherwise enacts payBill/error.  The user may enact
	 * enterShop/ok if they change their mind and wish to return to the 
	 * Shopping state; or enact exitShop/ok to abort shopping.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class Checkout extends State {
		public void enterShop() {
			response = "ok";
			state = new Shopping();
		}
		public Float getBill() {
			response = "ok";
			return totalCost;
		}
		public Boolean payBill(int billingInfo, String addressInfo) {
			if (VALID_BILLING.contains(billingInfo)) {
				response ="ok";
				state = new Payment();
				return true;
			}
			else {
				response = "error";
				return false;
			}
		}
	}
	
	/**
	 * Payment is the concrete subclass of State representing when this
	 * ShoppingCart is waiting for confirmation of payment.  The user may see
	 * the amount due, enacting getBill/ok.  If the user enacts confirm/ok,
	 * the amount is paid, the system is reset, and the state changes to the
	 * Ready state.  The user may still enact checkout/ok to return to the
	 * Checkout state, or enact exitShop/ok to abandon shopping.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class Payment extends State {
		public Float getBill() {
			response = "ok";
			return totalCost;
		}
		public Float confirm() {
			Float totalPaid = totalCost;
			response = "ok";
			currentStock = new HashMap<Dvd, Integer>(INITIAL_STOCK);
			shoppingCart = new HashMap<Dvd, Integer>();
			totalCost = 0.0F;
			state = new Ready();
			return totalPaid;
		}
		public Boolean checkout() {
			response = "ok";
			state = new Checkout();  // Try commenting out this line.
			return true;
		}
	}

}
