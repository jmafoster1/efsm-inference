package util;

import java.util.List;
import java.util.LinkedList;

import java.util.stream.Collectors;

public class Event {
  private String label;
  private LinkedList<Value> inputs = new LinkedList<Value>();
  private LinkedList<Value> outputs = new LinkedList<Value>();

  private static Value objectToValue(Object o) {
    System.out.println(o);
    if (o == null) {
      return new Str("NONE");
    }
    if (o.toString().matches("-?\\d+")) {
      return new Num(Integer.parseInt(o.toString()));
    }
    else {
      return new Str(o.toString());
    }
  }

  public Event(String label, Object[] inputs) {
    LinkedList<Value> inputsList = new LinkedList<Value>();
    for (Object i: inputs) {
      inputsList.add(objectToValue(i));
    }

    this.label = label;
    this.inputs = inputsList;
  }

  public Event(String label, Object[] inputs, Object[] outputs) {
    LinkedList<Value> inputsList = new LinkedList<Value>();
    for (Object i: inputs) {
      inputsList.add(objectToValue(i));
    }

    LinkedList<Value> outputsList = new LinkedList<Value>();
    for (Object i: outputs) {
      outputsList.add(objectToValue(i));
    }

    this.label = label;
    this.inputs = inputsList;
    this.outputs = outputsList;
  }

  public void setOutputs(Object output) {
    LinkedList<Value> outputsList = new LinkedList<Value>();
    outputsList.add(objectToValue(output));
    this.outputs = outputsList;
  }

  public Event(String label) {
    this.label = label;
  }

  public void setThis(Object o) {
    this.inputs.addFirst(objectToValue(o));
  }

  public String toString() {
    List<String> inputs = new LinkedList<String>();
    for (Value s : this.inputs) {
        inputs.add(s.toString());
    }

    List<String> outputs = new LinkedList<String>();
    for (Value s : this.outputs) {
        outputs.add(s.toString());
    }

    return "{\"label\": \""+this.label+"\", \"inputs\": ["+String.join(", ", inputs)+"], \"outputs\": ["+String.join(", ", outputs)+"]}";
  }
}
