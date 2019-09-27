package uk.ac.sheffield.vtts.client.pojo;

import org.junit.*;
import static org.junit.Assert.*;


/**
 * AccountTest generated on Fri Sep 27 13:37:15 BST 2019
 * by Broker@Cloud generator uk.ac.sheffield.vtts.ground.JavaGrounding
 *
 * System-Under-Test (SUT) is the POJO Java class: Account,
 * assumed to be a 'Plain Old Java Object'.
 *
 * This is a simple demonstration of grounding to Java, as though the
 * tested artifact were a simple Java class (POJO) offering methods that
 * might correspond to the operations of a service.  We assume that the
 * POJO can be reset simply by creating a fresh instance.  The names of
 * the POJO's methods must correspond to the original names used in the
 * specification.  If the POJO offers full inspection of its internal
 * behaviour, it must offer two further methods, <em>getScenario()</em>
 * and <em>getState()</em> to report on its status.
 *
 *		Exploring all paths up to length: 3
 *		Number of theoretical sequences: 2795
 *		Number of infeasible sequences: 794
 *		Number of redundant sequences: 1474
 *		Number of executable sequences: 527
 */
public class AccountTest {

	/**
	 * The Java object representing the System-Under-Test.
	 */
	private Account system = null;

	/**
	 * Creates the JUnit test driver: AccountTest.
	 */
	public AccountTest() {
	}

	/**
	 * Creates a fresh instance of the System-Under-Test before each
	 * test.  Verifies that creation works before the first test.
	 */
	@Before
	public void setUp() {
		if (system == null) {
			system = new Account();
			assertNotNull(system);
		}
		else
			system = new Account();
	}

	/**
	 * Translation of TestSequence #1.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 0.
	 */
	@Test
	public void test1 () {
		assertEquals("create/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #2.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test2 () {
		Boolean result1 = system.open("John Good");
		// Verify invocation step #1
		assertEquals((Boolean) true, result1);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #3.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test3 () {
		Boolean result1 = system.open("");
		// Verify invocation step #1
		assertEquals((Boolean) false, result1);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #4.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test4 () {
		Boolean result1 = system.close();
		// Verify invocation step #1
		assertEquals((Boolean) null, result1);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #5.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test5 () {
		Boolean result1 = system.deposit(1);
		// Verify invocation step #1
		assertEquals((Boolean) null, result1);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #6.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test6 () {
		Boolean result1 = system.deposit(0);
		// Verify invocation step #1
		assertEquals((Boolean) null, result1);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #7.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test7 () {
		Boolean result1 = system.withdraw(0);
		// Verify invocation step #1
		assertEquals((Boolean) null, result1);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #8.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test8 () {
		Boolean result1 = system.withdraw(1);
		// Verify invocation step #1
		assertEquals((Boolean) null, result1);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #9.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test9 () {
		Integer amount1 = system.getBalance();
		// Verify invocation step #1
		assertEquals((Integer) null, amount1);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #10.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 1.
	 */
	@Test
	public void test10 () {
		String customer1 = system.getHolder();
		// Verify invocation step #1
		assertEquals((String) null, customer1);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #11.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test11 () {
		system.open("John Good");
		Boolean result2 = system.open("John Good");
		// Verify invocation step #2
		assertEquals((Boolean) null, result2);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #12.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test12 () {
		system.open("John Good");
		Boolean result2 = system.open("");
		// Verify invocation step #2
		assertEquals((Boolean) null, result2);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #13.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test13 () {
		system.open("John Good");
		Boolean result2 = system.close();
		// Verify invocation step #2
		assertEquals((Boolean) true, result2);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #14.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test14 () {
		system.open("John Good");
		Boolean result2 = system.deposit(1);
		// Verify invocation step #2
		assertEquals((Boolean) true, result2);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #15.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test15 () {
		system.open("John Good");
		Boolean result2 = system.deposit(0);
		// Verify invocation step #2
		assertEquals((Boolean) false, result2);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #16.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test16 () {
		system.open("John Good");
		Boolean result2 = system.withdraw(0);
		// Verify invocation step #2
		assertEquals((Boolean) false, result2);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #17.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test17 () {
		system.open("John Good");
		Boolean result2 = system.withdraw(1);
		// Verify invocation step #2
		assertEquals((Boolean) false, result2);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #18.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test18 () {
		system.open("John Good");
		Integer amount2 = system.getBalance();
		// Verify invocation step #2
		assertEquals((Integer) 0, amount2);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #19.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test19 () {
		system.open("John Good");
		String customer2 = system.getHolder();
		// Verify invocation step #2
		assertEquals((String) "John Good", customer2);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #20.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test20 () {
		system.open("");
		Boolean result2 = system.open("John Good");
		// Verify invocation step #2
		assertEquals((Boolean) true, result2);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #21.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test21 () {
		system.open("");
		Boolean result2 = system.open("");
		// Verify invocation step #2
		assertEquals((Boolean) false, result2);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #22.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test22 () {
		system.open("");
		Boolean result2 = system.close();
		// Verify invocation step #2
		assertEquals((Boolean) null, result2);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #23.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test23 () {
		system.open("");
		Boolean result2 = system.deposit(1);
		// Verify invocation step #2
		assertEquals((Boolean) null, result2);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #24.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test24 () {
		system.open("");
		Boolean result2 = system.deposit(0);
		// Verify invocation step #2
		assertEquals((Boolean) null, result2);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #25.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test25 () {
		system.open("");
		Boolean result2 = system.withdraw(0);
		// Verify invocation step #2
		assertEquals((Boolean) null, result2);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #26.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test26 () {
		system.open("");
		Boolean result2 = system.withdraw(1);
		// Verify invocation step #2
		assertEquals((Boolean) null, result2);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #27.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test27 () {
		system.open("");
		Integer amount2 = system.getBalance();
		// Verify invocation step #2
		assertEquals((Integer) null, amount2);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #28.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 2.
	 */
	@Test
	public void test28 () {
		system.open("");
		String customer2 = system.getHolder();
		// Verify invocation step #2
		assertEquals((String) null, customer2);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #29.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test29 () {
		system.open("John Good");
		system.close();
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #30.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test30 () {
		system.open("John Good");
		system.close();
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #31.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test31 () {
		system.open("John Good");
		system.close();
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #32.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test32 () {
		system.open("John Good");
		system.close();
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #33.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test33 () {
		system.open("John Good");
		system.close();
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #34.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test34 () {
		system.open("John Good");
		system.close();
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #35.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test35 () {
		system.open("John Good");
		system.close();
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #36.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test36 () {
		system.open("John Good");
		system.close();
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) null, amount3);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #37.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test37 () {
		system.open("John Good");
		system.close();
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) null, customer3);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #38.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test38 () {
		system.open("John Good");
		system.deposit(1);
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #39.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test39 () {
		system.open("John Good");
		system.deposit(1);
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #40.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test40 () {
		system.open("John Good");
		system.deposit(1);
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #41.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test41 () {
		system.open("John Good");
		system.deposit(1);
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #42.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test42 () {
		system.open("John Good");
		system.deposit(1);
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #43.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test43 () {
		system.open("John Good");
		system.deposit(1);
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #44.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test44 () {
		system.open("John Good");
		system.deposit(1);
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #45.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test45 () {
		system.open("John Good");
		system.deposit(1);
		Boolean result3 = system.withdraw(2);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #46.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test46 () {
		system.open("John Good");
		system.deposit(1);
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) 1, amount3);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #47.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test47 () {
		system.open("John Good");
		system.deposit(1);
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) "John Good", customer3);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #48.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test48 () {
		system.open("John Good");
		system.deposit(0);
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #49.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test49 () {
		system.open("John Good");
		system.deposit(0);
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #50.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test50 () {
		system.open("John Good");
		system.deposit(0);
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #51.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test51 () {
		system.open("John Good");
		system.deposit(0);
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #52.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test52 () {
		system.open("John Good");
		system.deposit(0);
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #53.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test53 () {
		system.open("John Good");
		system.deposit(0);
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #54.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test54 () {
		system.open("John Good");
		system.deposit(0);
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #55.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test55 () {
		system.open("John Good");
		system.deposit(0);
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) 0, amount3);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #56.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test56 () {
		system.open("John Good");
		system.deposit(0);
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) "John Good", customer3);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #57.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test57 () {
		system.open("John Good");
		system.withdraw(0);
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #58.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test58 () {
		system.open("John Good");
		system.withdraw(0);
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #59.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test59 () {
		system.open("John Good");
		system.withdraw(0);
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #60.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test60 () {
		system.open("John Good");
		system.withdraw(0);
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #61.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test61 () {
		system.open("John Good");
		system.withdraw(0);
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #62.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test62 () {
		system.open("John Good");
		system.withdraw(0);
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #63.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test63 () {
		system.open("John Good");
		system.withdraw(0);
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #64.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test64 () {
		system.open("John Good");
		system.withdraw(0);
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) 0, amount3);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #65.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test65 () {
		system.open("John Good");
		system.withdraw(0);
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) "John Good", customer3);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #66.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test66 () {
		system.open("John Good");
		system.withdraw(1);
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #67.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test67 () {
		system.open("John Good");
		system.withdraw(1);
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #68.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test68 () {
		system.open("John Good");
		system.withdraw(1);
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #69.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test69 () {
		system.open("John Good");
		system.withdraw(1);
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #70.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test70 () {
		system.open("John Good");
		system.withdraw(1);
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #71.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test71 () {
		system.open("John Good");
		system.withdraw(1);
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #72.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test72 () {
		system.open("John Good");
		system.withdraw(1);
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #73.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test73 () {
		system.open("John Good");
		system.withdraw(1);
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) 0, amount3);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #74.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test74 () {
		system.open("John Good");
		system.withdraw(1);
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) "John Good", customer3);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #75.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test75 () {
		system.open("John Good");
		system.getBalance();
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #76.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test76 () {
		system.open("John Good");
		system.getBalance();
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #77.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test77 () {
		system.open("John Good");
		system.getBalance();
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #78.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test78 () {
		system.open("John Good");
		system.getBalance();
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #79.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test79 () {
		system.open("John Good");
		system.getBalance();
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #80.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test80 () {
		system.open("John Good");
		system.getBalance();
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #81.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test81 () {
		system.open("John Good");
		system.getBalance();
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #82.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test82 () {
		system.open("John Good");
		system.getBalance();
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) 0, amount3);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #83.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test83 () {
		system.open("John Good");
		system.getBalance();
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) "John Good", customer3);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #84.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test84 () {
		system.open("John Good");
		system.getHolder();
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #85.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test85 () {
		system.open("John Good");
		system.getHolder();
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #86.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test86 () {
		system.open("John Good");
		system.getHolder();
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #87.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test87 () {
		system.open("John Good");
		system.getHolder();
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #88.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test88 () {
		system.open("John Good");
		system.getHolder();
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #89.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test89 () {
		system.open("John Good");
		system.getHolder();
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #90.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test90 () {
		system.open("John Good");
		system.getHolder();
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #91.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test91 () {
		system.open("John Good");
		system.getHolder();
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) 0, amount3);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #92.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test92 () {
		system.open("John Good");
		system.getHolder();
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) "John Good", customer3);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #93.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test93 () {
		system.open("");
		system.open("John Good");
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #94.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test94 () {
		system.open("");
		system.open("John Good");
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #95.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test95 () {
		system.open("");
		system.open("John Good");
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #96.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test96 () {
		system.open("");
		system.open("John Good");
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #97.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test97 () {
		system.open("");
		system.open("John Good");
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #98.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test98 () {
		system.open("");
		system.open("John Good");
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #99.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test99 () {
		system.open("");
		system.open("John Good");
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #100.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test100 () {
		system.open("");
		system.open("John Good");
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) 0, amount3);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #101.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test101 () {
		system.open("");
		system.open("John Good");
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) "John Good", customer3);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #102.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test102 () {
		system.open("");
		system.open("");
		Boolean result3 = system.open("John Good");
		// Verify invocation step #3
		assertEquals((Boolean) true, result3);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #103.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test103 () {
		system.open("");
		system.open("");
		Boolean result3 = system.open("");
		// Verify invocation step #3
		assertEquals((Boolean) false, result3);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #104.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test104 () {
		system.open("");
		system.open("");
		Boolean result3 = system.close();
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #105.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test105 () {
		system.open("");
		system.open("");
		Boolean result3 = system.deposit(1);
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #106.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test106 () {
		system.open("");
		system.open("");
		Boolean result3 = system.deposit(0);
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #107.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test107 () {
		system.open("");
		system.open("");
		Boolean result3 = system.withdraw(0);
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #108.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test108 () {
		system.open("");
		system.open("");
		Boolean result3 = system.withdraw(1);
		// Verify invocation step #3
		assertEquals((Boolean) null, result3);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #109.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test109 () {
		system.open("");
		system.open("");
		Integer amount3 = system.getBalance();
		// Verify invocation step #3
		assertEquals((Integer) null, amount3);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #110.  The main test goal is to reach the
	 * state 'Closed' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test110 () {
		system.open("");
		system.open("");
		String customer3 = system.getHolder();
		// Verify invocation step #3
		assertEquals((String) null, customer3);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #111.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test111 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #112.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test112 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #113.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test113 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #114.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test114 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #115.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test115 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #116.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test116 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #117.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test117 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #118.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test118 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #119.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test119 () {
		system.open("John Good");
		system.close();
		system.open("John Good");
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #120.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test120 () {
		system.open("John Good");
		system.close();
		system.open("");
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #121.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test121 () {
		system.open("John Good");
		system.close();
		system.open("");
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #122.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test122 () {
		system.open("John Good");
		system.close();
		system.open("");
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #123.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test123 () {
		system.open("John Good");
		system.close();
		system.open("");
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #124.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test124 () {
		system.open("John Good");
		system.close();
		system.open("");
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #125.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test125 () {
		system.open("John Good");
		system.close();
		system.open("");
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #126.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test126 () {
		system.open("John Good");
		system.close();
		system.open("");
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #127.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test127 () {
		system.open("John Good");
		system.close();
		system.open("");
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) null, amount4);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #128.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test128 () {
		system.open("John Good");
		system.close();
		system.open("");
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) null, customer4);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #129.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test129 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #130.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test130 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #131.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test131 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #132.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test132 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #133.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test133 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #134.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test134 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #135.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test135 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #136.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test136 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #137.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test137 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #138.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test138 () {
		system.open("John Good");
		system.deposit(1);
		system.close();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #139.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test139 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #140.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test140 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #141.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test141 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #142.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test142 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #143.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test143 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #144.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test144 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #145.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test145 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #146.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test146 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Boolean result4 = system.withdraw(3);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #147.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test147 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 2, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #148.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test148 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #149.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test149 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #150.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test150 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #151.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test151 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #152.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test152 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #153.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test153 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #154.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test154 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #155.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test155 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #156.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test156 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #157.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test157 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #158.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test158 () {
		system.open("John Good");
		system.deposit(1);
		system.deposit(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #159.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test159 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #160.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test160 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #161.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test161 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #162.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test162 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #163.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test163 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #164.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test164 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #165.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test165 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #166.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test166 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #167.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test167 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #168.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test168 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #169.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test169 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #170.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test170 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #171.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test171 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #172.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test172 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #173.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test173 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #174.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test174 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #175.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test175 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #176.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test176 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #177.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test177 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #178.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test178 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #179.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test179 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #180.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test180 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #181.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test181 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #182.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test182 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #183.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test183 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #184.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test184 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #185.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test185 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #186.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test186 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #187.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test187 () {
		system.open("John Good");
		system.deposit(1);
		system.withdraw(2);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #188.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test188 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #189.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test189 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #190.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test190 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #191.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test191 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #192.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test192 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #193.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test193 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #194.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test194 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #195.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test195 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #196.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test196 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #197.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test197 () {
		system.open("John Good");
		system.deposit(1);
		system.getBalance();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #198.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test198 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #199.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test199 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #200.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test200 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #201.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test201 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #202.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test202 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #203.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test203 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #204.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test204 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #205.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test205 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #206.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test206 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #207.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test207 () {
		system.open("John Good");
		system.deposit(1);
		system.getHolder();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #208.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test208 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #209.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test209 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #210.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test210 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #211.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test211 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #212.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test212 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #213.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test213 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #214.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test214 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #215.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test215 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) null, amount4);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #216.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test216 () {
		system.open("John Good");
		system.deposit(0);
		system.close();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) null, customer4);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #217.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test217 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #218.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test218 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #219.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test219 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #220.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test220 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #221.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test221 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #222.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test222 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #223.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test223 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #224.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test224 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #225.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test225 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #226.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test226 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #227.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test227 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #228.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test228 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #229.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test229 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #230.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test230 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #231.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test231 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #232.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test232 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #233.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test233 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #234.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test234 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #235.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test235 () {
		system.open("John Good");
		system.deposit(0);
		system.deposit(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #236.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test236 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #237.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test237 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #238.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test238 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #239.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test239 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #240.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test240 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #241.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test241 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #242.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test242 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #243.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test243 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #244.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test244 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #245.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test245 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #246.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test246 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #247.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test247 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #248.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test248 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #249.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test249 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #250.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test250 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #251.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test251 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #252.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test252 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #253.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test253 () {
		system.open("John Good");
		system.deposit(0);
		system.withdraw(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #254.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test254 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #255.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test255 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #256.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test256 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #257.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test257 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #258.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test258 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #259.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test259 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #260.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test260 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #261.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test261 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #262.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test262 () {
		system.open("John Good");
		system.deposit(0);
		system.getBalance();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #263.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test263 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #264.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test264 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #265.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test265 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #266.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test266 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #267.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test267 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #268.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test268 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #269.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test269 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #270.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test270 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #271.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test271 () {
		system.open("John Good");
		system.deposit(0);
		system.getHolder();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #272.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test272 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #273.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test273 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #274.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test274 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #275.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test275 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #276.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test276 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #277.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test277 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #278.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test278 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #279.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test279 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) null, amount4);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #280.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test280 () {
		system.open("John Good");
		system.withdraw(0);
		system.close();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) null, customer4);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #281.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test281 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #282.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test282 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #283.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test283 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #284.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test284 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #285.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test285 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #286.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test286 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #287.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test287 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #288.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test288 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #289.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test289 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #290.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test290 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #291.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test291 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #292.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test292 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #293.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test293 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #294.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test294 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #295.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test295 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #296.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test296 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #297.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test297 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #298.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test298 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #299.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test299 () {
		system.open("John Good");
		system.withdraw(0);
		system.deposit(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #300.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test300 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #301.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test301 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #302.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test302 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #303.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test303 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #304.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test304 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #305.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test305 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #306.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test306 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #307.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test307 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #308.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test308 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #309.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test309 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #310.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test310 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #311.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test311 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #312.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test312 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #313.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test313 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #314.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test314 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #315.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test315 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #316.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test316 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #317.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test317 () {
		system.open("John Good");
		system.withdraw(0);
		system.withdraw(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #318.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test318 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #319.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test319 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #320.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test320 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #321.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test321 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #322.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test322 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #323.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test323 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #324.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test324 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #325.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test325 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #326.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test326 () {
		system.open("John Good");
		system.withdraw(0);
		system.getBalance();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #327.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test327 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #328.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test328 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #329.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test329 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #330.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test330 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #331.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test331 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #332.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test332 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #333.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test333 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #334.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test334 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #335.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test335 () {
		system.open("John Good");
		system.withdraw(0);
		system.getHolder();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #336.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test336 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #337.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test337 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #338.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test338 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #339.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test339 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #340.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test340 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #341.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test341 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #342.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test342 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #343.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test343 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) null, amount4);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #344.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test344 () {
		system.open("John Good");
		system.withdraw(1);
		system.close();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) null, customer4);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #345.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test345 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #346.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test346 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #347.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test347 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #348.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test348 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #349.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test349 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #350.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test350 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #351.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test351 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #352.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test352 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #353.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test353 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #354.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test354 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #355.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test355 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #356.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test356 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #357.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test357 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #358.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test358 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #359.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test359 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #360.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test360 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #361.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test361 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #362.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test362 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #363.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test363 () {
		system.open("John Good");
		system.withdraw(1);
		system.deposit(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #364.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test364 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #365.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test365 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #366.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test366 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #367.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test367 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #368.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test368 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #369.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test369 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #370.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test370 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #371.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test371 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #372.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test372 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #373.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test373 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #374.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test374 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #375.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test375 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #376.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test376 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #377.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test377 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #378.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test378 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #379.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test379 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #380.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test380 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #381.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test381 () {
		system.open("John Good");
		system.withdraw(1);
		system.withdraw(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #382.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test382 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #383.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test383 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #384.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test384 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #385.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test385 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #386.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test386 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #387.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test387 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #388.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test388 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #389.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test389 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #390.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test390 () {
		system.open("John Good");
		system.withdraw(1);
		system.getBalance();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #391.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test391 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #392.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test392 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #393.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test393 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #394.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test394 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #395.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test395 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #396.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test396 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #397.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test397 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #398.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test398 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #399.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test399 () {
		system.open("John Good");
		system.withdraw(1);
		system.getHolder();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #400.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test400 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #401.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test401 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #402.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test402 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #403.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test403 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #404.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test404 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #405.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test405 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #406.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test406 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #407.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test407 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) null, amount4);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #408.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test408 () {
		system.open("John Good");
		system.getBalance();
		system.close();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) null, customer4);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #409.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test409 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #410.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test410 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #411.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test411 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #412.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test412 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #413.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test413 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #414.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test414 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #415.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test415 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #416.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test416 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #417.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test417 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #418.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test418 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #419.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test419 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #420.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test420 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #421.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test421 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #422.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test422 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #423.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test423 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #424.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test424 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #425.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test425 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #426.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test426 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #427.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test427 () {
		system.open("John Good");
		system.getBalance();
		system.deposit(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #428.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test428 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #429.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test429 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #430.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test430 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #431.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test431 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #432.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test432 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #433.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test433 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #434.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test434 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #435.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test435 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #436.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test436 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #437.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test437 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #438.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test438 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #439.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test439 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #440.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test440 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #441.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test441 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #442.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test442 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #443.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test443 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #444.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test444 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #445.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test445 () {
		system.open("John Good");
		system.getBalance();
		system.withdraw(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #446.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test446 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #447.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test447 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #448.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test448 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #449.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test449 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #450.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test450 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #451.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test451 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #452.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test452 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #453.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test453 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #454.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test454 () {
		system.open("John Good");
		system.getBalance();
		system.getBalance();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #455.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test455 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #456.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test456 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #457.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test457 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #458.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test458 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #459.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test459 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #460.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test460 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #461.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test461 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #462.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test462 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #463.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test463 () {
		system.open("John Good");
		system.getBalance();
		system.getHolder();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #464.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test464 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("open/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #465.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test465 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("open/error", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #466.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test466 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("close/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #467.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test467 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #468.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test468 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("deposit/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #469.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test469 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #470.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test470 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("withdraw/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #471.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test471 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) null, amount4);
		assertEquals("getBalance/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #472.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test472 () {
		system.open("John Good");
		system.getHolder();
		system.close();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) null, customer4);
		assertEquals("getHolder/ignore", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #473.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test473 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #474.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test474 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #475.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test475 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("close/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #476.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test476 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #477.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test477 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #478.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test478 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("withdraw/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #479.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test479 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #480.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test480 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Boolean result4 = system.withdraw(2);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #481.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test481 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 1, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #482.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test482 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #483.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test483 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #484.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test484 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #485.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test485 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #486.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test486 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #487.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test487 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #488.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test488 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #489.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test489 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #490.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test490 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #491.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test491 () {
		system.open("John Good");
		system.getHolder();
		system.deposit(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #492.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test492 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #493.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test493 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #494.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test494 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #495.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test495 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #496.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test496 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #497.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test497 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #498.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test498 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #499.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test499 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #500.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test500 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(0);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #501.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test501 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #502.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test502 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #503.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test503 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #504.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test504 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #505.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test505 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #506.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test506 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #507.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test507 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #508.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test508 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #509.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test509 () {
		system.open("John Good");
		system.getHolder();
		system.withdraw(1);
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #510.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test510 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #511.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test511 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #512.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test512 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #513.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test513 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #514.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test514 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #515.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test515 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #516.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test516 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #517.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test517 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #518.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test518 () {
		system.open("John Good");
		system.getHolder();
		system.getBalance();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #519.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test519 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		Boolean result4 = system.open("John Good");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #520.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test520 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		Boolean result4 = system.open("");
		// Verify invocation step #4
		assertEquals((Boolean) null, result4);
		assertEquals("open/ignore", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #521.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test521 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		Boolean result4 = system.close();
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("close/ok", system.getScenario());
		assertEquals("Closed", system.getState());
	}

	/**
	 * Translation of TestSequence #522.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test522 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		Boolean result4 = system.deposit(1);
		// Verify invocation step #4
		assertEquals((Boolean) true, result4);
		assertEquals("deposit/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #523.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test523 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		Boolean result4 = system.deposit(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("deposit/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #524.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test524 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		Boolean result4 = system.withdraw(0);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/error", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #525.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test525 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		Boolean result4 = system.withdraw(1);
		// Verify invocation step #4
		assertEquals((Boolean) false, result4);
		assertEquals("withdraw/blocked", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #526.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test526 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		Integer amount4 = system.getBalance();
		// Verify invocation step #4
		assertEquals((Integer) 0, amount4);
		assertEquals("getBalance/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}

	/**
	 * Translation of TestSequence #527.  The main test goal is to reach the
	 * state 'Open' and, from there, execute a novel path of length 3.
	 */
	@Test
	public void test527 () {
		system.open("John Good");
		system.getHolder();
		system.getHolder();
		String customer4 = system.getHolder();
		// Verify invocation step #4
		assertEquals((String) "John Good", customer4);
		assertEquals("getHolder/ok", system.getScenario());
		assertEquals("Open", system.getState());
	}
}
