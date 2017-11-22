defmodule EFSMTest do
  use ExUnit.Case

  test "reads efsm from file" do
    {efsm, transitionTable} = EFSM.read("test/support_files/drinks_machine.json")
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "100"}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
    TransitionTable.stop(transitionTable)
  end

  test "accepts a trace" do
    {efsm, transitionTable} = EFSM.read("test/support_files/drinks_machine.json")
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "110"}},
      %{"label" => "vend", "arity" => 0, "args" => %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
  end

  test "accepts a string trace" do
    {efsm, transitionTable} = EFSM.read("test/support_files/drinks_machine.json")
    assert EFSM.acceptsTraceSet([
        ["select(coke)", "coin(100)", "vend()"],
        ["select(coke)", "coin(50)", "coin(50)", "vend()"]
      ], efsm, transitionTable, "q0", %{}) == true
  end

  test "accepts a set of traces" do
    {efsm, transitionTable} = EFSM.read("test/support_files/drinks_machine.json")
    assert EFSM.acceptsTrace(["select(coke)", "coin(100)", "vend()"], efsm, transitionTable, "q0", %{}, 0, []) == true
  end

  test "rejects a trace" do
    {efsm, transitionTable} = EFSM.read("test/support_files/drinks_machine.json")
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "10"}},
      %{"label" => "vend", "arity" => 0, "args" => %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == false
  end

  test "merge states" do
    {efsm, transitionTable} = EFSM.read("test/support_files/unmerged.json")
    assert EFSM.acceptsTraceSet([
        ["select(coke)", "coin(100)", "vend()"],
        ["select(coke)", "coin(50)", "coin(50)", "vend()"]
      ], efsm, transitionTable, "q0", %{}) == true
    efsm = EFSM.mergeStates(efsm,transitionTable,"q5","q3")
    assert EFSM.acceptsTraceSet([
        ["select(coke)", "coin(100)", "vend()"],
        ["select(coke)", "coin(50)", "coin(50)", "vend()"]
      ], efsm, transitionTable, "q0", %{}) == true
  end

  test "to JSON style map" do
    {efsm, transitionTable} = EFSM.read("test/support_files/unmerged.json")
    assert EFSM.to_json_map(efsm, transitionTable) == %{"q0" => %{"select:1[i1=coke]" => "q1"},
      "q1" => %{"coin:1[i1=100]" => "q5", "coin:1[i1=50]" => "q2"},
      "q2" => %{"coin:1[i1=50]" => "q3"}, "q3" => %{"vend:0/o1:=coke" => "q4"},
      "q4" => %{}, "q5" => %{"vend:0/o1:=coke" => "q6"}, "q6" => %{}}
  end

  test "to JSON string" do
    {efsm, transitionTable} = EFSM.read("test/support_files/unmerged.json")
    assert EFSM.to_json(efsm, transitionTable) == "{\"q6\":{},\"q5\":{\"vend:0/o1:=coke\":\"q6\"},\"q4\":{},\"q3\":{\"vend:0/o1:=coke\":\"q4\"},\"q2\":{\"coin:1[i1=50]\":\"q3\"},\"q1\":{\"coin:1[i1=50]\":\"q2\",\"coin:1[i1=100]\":\"q5\"},\"q0\":{\"select:1[i1=coke]\":\"q1\"}}"
  end

  test "to dot" do
    {efsm, transitionTable} = EFSM.read("test/support_files/unmerged.json")
    assert EFSM.to_dot(efsm, transitionTable) == "digraph G {\n  q0 [color=\"black\" fillcolor=\"green\" shape=\"doublecircle\" style=\"filled\"];\n  q1 [color=\"black\" fillcolor=\"white\" shape=\"circle\" style=\"filled\"];\n  q2 [color=\"black\" fillcolor=\"white\" shape=\"circle\" style=\"filled\"];\n  q3 [color=\"black\" fillcolor=\"white\" shape=\"circle\" style=\"filled\"];\n  q4 [color=\"black\" fillcolor=\"white\" shape=\"circle\" style=\"filled\"];\n  q5 [color=\"black\" fillcolor=\"white\" shape=\"circle\" style=\"filled\"];\n  q6 [color=\"black\" fillcolor=\"white\" shape=\"circle\" style=\"filled\"];\n  q0 -> q1 [label=\"select:1[i1=coke]\"];\n  q1 -> q5 [label=\"coin:1[i1=100]\"];\n  q1 -> q2 [label=\"coin:1[i1=50]\"];\n  q2 -> q3 [label=\"coin:1[i1=50]\"];\n  q3 -> q4 [label=\"vend:0/o1:=coke\"];\n  q5 -> q6 [label=\"vend:0/o1:=coke\"];\n}"
  end

end
