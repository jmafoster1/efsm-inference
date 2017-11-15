defmodule FSMTest do
  use ExUnit.Case
  doctest FSM

  test "reads an fsm from json" do
    assert FSM.read("fsm.json") == %{
      "q0" => [
        %{"guards" => [], "label" => "select", "outputs" => [], "updates" => [{"r1", ":=", "i1"}], "dest" => "q1"}
        ],
      "q1" => [
        %{"guards" => [{"r2", ">=", "100"}], "label" => "vend", "outputs" => [{"o1", ":=", "r1"}], "updates" => [{"r2", ":=", "r2", "-", "100"}], "dest" => "q2"},
        %{"guards" => [], "label" => "coin", "outputs" => [], "updates" => [{"r2", ":=", "r2", "+", "i1"}], "dest" => "q1"}
        ],
      "q2" => []
    }

  end

  test "parse a transition string" do
    assert FSM.parse_transition("vend[r2>100,r1=coke]/o1:=r1,o2:=test[r2:=r2-100,r1:=test]", "q2") == %{
      "label" => "vend",
      "guards" => [{"r2", ">", "100"}, {"r1", "=", "coke"}],
      "outputs" => [{"o1", ":=", "r1"}, {"o2", ":=", "test"}],
      "updates" => [{"r2", ":=", "r2", "-", "100"}, {"r1", ":=", "test"}],
      "dest" => "q2"
    }
  end

  test "apply guards true" do
    guards = [{"r2", ">=", "100"}, {"r1", "=", "coke"}]
    registers = %{"r1" => "coke", "r2" => "100"}
    inputs = %{"i1" => "vend"}
    assert FSM.applyGuards(guards, registers, inputs) == true
  end

  test "apply guards false" do
    guards = [{"r2", ">", "100"}, {"r1", "=", "coke"}]
    registers = %{"r1" => "coke", "r2" => "100"}
    inputs = %{"i1" => "vend"}
    assert FSM.applyGuards(guards, registers, inputs) == false
  end

  test "apply outputs" do
    registers = %{"r1" => "coke", "r2" => "100"}
    inputs = %{"i1" => "vend"}
    outputs = [{"o1", ":=", "r1"}, {"o2", ":=", "test"}]
    assert FSM.applyOutputs(outputs, registers, inputs) == [{"o1", "coke"}, {"o2", "test"}]
  end

  test "apply updates" do
    registers = %{"r1" => "coke", "r2" => "-1"}
    inputs = %{"i1" => "vend"}
    updates = [{"r2", ":=", "r2", "-", "100.5"}, {"r1", ":=", "test"}]
    assert FSM.applyUpdates(updates, registers, inputs) == %{"r1" => "test", "r2" => "-101.5"}
  end

  test "parse input string" do
    assert FSM.parseInput("select(coke,sprite)") == %{
      "inputs" => %{"i1" => "coke", "i2" => "sprite"},
      "label" => "select"
    }
  end

  test "parse input list" do
    assert FSM.parseInputList("select(coke),coin(50),coin(50),vend()") == [
      %{"inputs" => %{"i1" => "coke"}, "label" => "select"},
      %{"inputs" => %{"i1" => "50"}, "label" => "coin"},
      %{"inputs" => %{"i1" => "50"}, "label" => "coin"},
      %{"inputs" => %{}, "label" => "vend"}
    ]
    end

  test "accepts a string of inputs" do
    input = FSM.parseInputList("select(coke),coin(50),coin(20),coin(20),coin(20),vend()")
    fsm = assert FSM.read("fsm.json")
    assert FSM.accepts(input, fsm, "q0", %{}) == true
  end

  test "reject a string of inputs" do
    input = FSM.parseInputList("select(coke),coin(50),vend()")
    fsm = assert FSM.read("fsm.json")
    assert FSM.accepts(input, fsm, "q0", %{}) == false
  end
end
