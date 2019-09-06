package test;

public class SimpleTest {
  public int add(int a, int b) {
    return a + b;
  }

  public static void main(String[] args) {
    SimpleTest t = new SimpleTest();
    t.add(1, 2);
  }
}
