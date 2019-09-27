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
import java.util.List;

/**
 * HolidayBooking is a correct POJO implementation of the 
 * <code>HolidayBooking.xml</code> 
 * specification.  It mimics a simple SAP application built in OpenUI5 and
 * deployed on the SAP HANA cloud.  This application offers three UI states,
 * in which the user could view booked holidays, book more days, or delete
 * existing days.  The user could book up to five days holiday.  The system
 * should refuse booking duplicate days and disallow more than the five days
 * in total.
 * <p>
 * This uses the State Pattern (a Design Pattern from Gamma, et al.) for its 
 * implementation.  All requests are delegated to an abstract State, which 
 * has concrete subclasses ViewDays, BookDays and DeleteDays, which 
 * respond to certain requests in different ways.
 * <p>
 * Indexing in the specification language runs from 1..n; this is preserved
 * in the selected row, but converted to 0..n-1 when accessing the underlying
 * Java Lists.  It demonstrates the facility to return multiple values as the
 * response to a request.  This is translated into returning an Object[]
 * array in Java clients.  In the same way that an error case always returns
 * an unbound output with a null value, multiple unbound results are returned
 * as an array of nulls. 
 * <p>
 * Suggestions are given for how to modify the source code to seed
 * faults deliberately, which will be detected during testing.
 *
 * @author Anthony J H Simons
 * @version 1.0
 */
public class HolidayBooking {

	/**
	 * Logs the last request received by this HolidayBooking.
	 */
	private String request;
	
	/**
	 * Logs the last response enacted by this HolidayBooking.
	 */
	private String response;
	
	/**
	 * The last state entered by this HolidayBooking.
	 */
	private State state;
	
	/**
	 * The maximum number of allowed holidays.
	 */
	private static final int MAX_HOLIDAYS = 5;
	
	/**
	 * The list of first-days in this HolidayBooking.
	 */
	private List<Integer> firstDays;
	
	/**
	 * The list of last-days in this HolidayBooking.
	 */
	private List<Integer> lastDays;
	
	/**
	 * The selected row (1..n), initially zero since no row is selected.
	 */
	private int selectedRow = 0;
	
	/**
	 * The total number of days holiday, initially zero.  This cannot exceed 
	 * MAX_HOLIDAYS.
	 */
	private int totalHolidays = 0;
	
	/**
	 * Last fromDay that was booked by choose(fromDay, untilDay).
	 */
	private int fromDay = 0;
	
	/**
	 * Last toDay that was booked by choose(fromDay, untilDay).
	 */
	private int untilDay = 0;
	
	/**
	 * Last block of days that was booked by choose(fromDay, untilDay).
	 */
	private int bookedDays = 0;

	
	/**
	 * Creates a HolidayBooking.  Enacts the scenario create/ok and enters the
	 * ViewDays state.  
	 */	
	public HolidayBooking() {
		// implementation - other constants zero
		firstDays = new ArrayList<Integer>();
		lastDays = new ArrayList<Integer>();
		state = new ViewDays();
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
	 * which also have access to the HolidayBooking's fields.  The name of 
	 * the current state is obtained by reflection on the class name.
	 * @return the name of the current State instance.
	 */
	public String getState() {
		return state.getClass().getSimpleName();
	}

	/**
	 * Mimics clicking on the "BookDays" button to move from the ViewDays
	 * state to the BookDays state, in which more holidays may be booked.
	 */
	public void bookDays() {
		request = "bookDays";
		state.bookDays();
	}

	/**
	 * Allows selection of one booked holiday period, stored in a list.
	 * @param row the row selected in the UI (indexing is 1..n).
	 */
	public void select(int row) {
		request = "select";
		state.select(row);
	}

	/**
	 * Mimics clicking on the "Back" button in either of the states
	 * BookDays or DeleteDays to return to the ViewDays state.
	 */
	public void back() {
		request = "back";
		state.back();
	}

	/**
	 * Mimics clicking on a pair of days on the calendar, to indicate 
	 * selecting a short period of holiday, where the selected range 
	 * includes both days.  The current month and year are assumed and
	 * are not modelled in this example.
	 * @param firstDay the starting day (inclusive).
	 * @param lastDay the ending day (inclusive).
	 */
	public void choose(int firstDay, int lastDay) {
		request = "choose";
		state.choose(firstDay, lastDay);
	}

	/**
	 * Mimics clicking on the "Save" button to record the selected range
	 * of days as holiday.  
	 * @return a pair of days (integers), or a pair of nulls.
	 */
	public Object[] save() {
		request = "save";
		return state.save();
	}

	/**
	 * Mimics clicking on the "Delete" button to delete the currently
	 * selected row in the list of booked holidays.
	 * @return a pair of days (integers), or a pair of nulls.
	 */
	public Object[] delete() {
		request = "delete";
		return state.delete();
	}
	
	/**
	 * State describes the default behaviour for all states.  This is
	 * selectively overridden in concrete subclasses.  It is always
	 * possible to add a new entry in any state; but there must be some
	 * existing entries for selection and deletion to be possible.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private abstract class State {
		public void bookDays() {
			response = "ignore";
		}
		public Object[] delete() {
			response = "ignore";
			return new Object[] {null, null};
		}
		public Object[] save() {
			response = "ignore";
			return new Object[] {null, null};
		}
		public void choose(int firstDay, int lastDay) {
			response = "ignore";
		}
		public void back() {
			response = "ignore";
		}
		public void select(int row) {
			response = "ignore";
		}
	}
	
	/**
	 * ViewDays is the initial state, displaying zero or more rows of booked
	 * holiday periods.  The user may click a "Book Days" button to change to
	 * the BookDays state, in which further periods may be booked.  If booked
	 * periods already exist, the user may select one of these by clicking on 
	 * the row and this changes state to DeleteDays, in which the user may
	 * choose to delete the selected row.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class ViewDays extends State {
		public void bookDays() {
			response = "ok";
			// Clear the last period selected in the UI.
			fromDay = 0;
			untilDay = 0;
			bookedDays = 0;
			state = new BookDays();
		}
		public void select(int row) {
			if (row <= 0 || row > firstDays.size())
				response = "fail";
			else {
				response = (row == firstDays.size() ? "high" : "low");
				selectedRow = row;
				state = new DeleteDays();
			}
		}
	}
	
	/**
	 * BookDays is a state displaying the calendar for the current month.
	 * It allows the user to select periods of holiday by selecting the first
	 * and last day (in either order) on the calendar.  The period between
	 * these chosen dates (inclusive) is the booked period.  The user may
	 * then attempt to save this period.  If the period is non-zero, and if
	 * none of the days overlap with existing periods, and if the sum total
	 * of booked holidays does not exceed five days, adds the new booked
	 * period, returns the first and last days, and changes state back to 
	 * ViewDays.  Otherwise, remains in this state and logs error responses
	 * fail, duplicate or overflow.  The user may also discard the current
	 * choice by clicking the "Back" button which returns to the ViewDates
	 * state.  
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class BookDays extends State {
		// Saves the current selected days, if they are valid.
		public Object[] save() {
			Object[] result = new Object[]{null, null};
			if (bookedDays == 0) 
				response = "fail";
			else {
				boolean overlap = false;
				for (int i = 0; i < firstDays.size(); ++i) {
					if ((fromDay >= firstDays.get(i) && fromDay <= lastDays.get(i))
						|| (untilDay >= firstDays.get(i) && untilDay <= lastDays.get(i))) {
						overlap = true;
						break;
					}
				}
				if (overlap) 
					response = "duplicate";
				else if (totalHolidays + bookedDays > MAX_HOLIDAYS)
					response = "overflow";
				else {
					response = "ok";
					firstDays.add(fromDay);
					lastDays.add(untilDay);
					result = new Object[]{fromDay, untilDay};
					state = new ViewDays();
				}
			}
			return result;
		}
		public void choose(int firstDay, int lastDay) {
			// Does not matter in which order you select days in the calendar
			if (lastDay < firstDay) {
				int tempDay = firstDay;
				firstDay = lastDay;
				lastDay = tempDay;
			}
			// Can only click on days that exist in the calendar month
			fromDay = (firstDay < 1 ? 1 : firstDay > 31 ? 31 : firstDay);
			untilDay = (lastDay < 1 ? 1 : lastDay > 31 ? 31 : lastDay);
			bookedDays = untilDay - fromDay + 1;
			if (bookedDays == 1)
				response = "single";
			else if (bookedDays < MAX_HOLIDAYS)
				response = "short";
			else
				response = "long";
		}
		public void back() {
			response = "ok";
			state = new ViewDays();
		}
	}
	
	/**
	 * DeleteDays is a state displaying the calendar with the period to be
	 * deleted selected.  If the user clicks the "Delete" button, the state
	 * changes to ViewDays, in which the selected row has been deleted.  If
	 * the user clicks on any other day in the calendar, this is interpreted
	 * as choosing a period, so changes state to BookDays, without deleting
	 * anything.  The user may also click the "Back" button to return to 
	 * ViewDays without deleting the selected period.
	 *
	 * @author Anthony J H Simons
	 * @version 1.0
	 */
	private class DeleteDays extends State {
		public void choose(int firstDay, int lastDay) {
			// Does not matter in which order you select days in the calendar
			if (lastDay < firstDay) {
				int tempDay = firstDay;
				firstDay = lastDay;
				lastDay = tempDay;
			}
			// Can only click on days that exist in the calendar month
			fromDay = (firstDay < 1 ? 1 : firstDay > 31 ? 31 : firstDay);
			untilDay = (lastDay < 1 ? 1 : lastDay > 31 ? 31 : lastDay);
			bookedDays = untilDay - fromDay + 1;
			if (bookedDays == 1)
				response = "single";
			else if (bookedDays < MAX_HOLIDAYS)
				response = "short";
			else
				response = "long";
			state = new BookDays();
		}
		public void back() {
			response = "ok";
			state = new ViewDays();
		}
		public Object[] delete() {
			response = "ok";
			fromDay = firstDays.remove(selectedRow -1);
			untilDay = lastDays.remove(selectedRow -1);
			state = new ViewDays();
			return new Object[]{fromDay, untilDay};
		}
	}

}
