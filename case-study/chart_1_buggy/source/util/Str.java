package util;

public class Str extends Value {
  private String value;

  public Str(String value) {
    this.value = value;
  }

  public boolean isNum() {
    return false;
  }

  public boolean isStr() {
    return true;
  }

  public String getValue() {
    return this.value;
  }

  public String toString() {
    return "\""+this.value+"\"";
  }
}
