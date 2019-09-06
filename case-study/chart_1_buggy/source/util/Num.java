package util;

public class Num extends Value {
  private long value;

  public Num(long value) {
    this.value = value;
  }

  public boolean isNum() {
    return true;
  }

  public boolean isStr() {
    return false;
  }

  public long getValue() {
    return this.value;
  }

  public String toString() {
    return Long.toString(this.value);
  }
}
