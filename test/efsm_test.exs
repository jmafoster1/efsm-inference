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
    IO.inspect EFSM.acceptsTrace(["select(coke)", "coin(100)", "vend()"], efsm, transitionTable, "q0", %{}, 0, []) == true
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
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "100"}},
      %{"label" => "vend", "arity" => 0, "args" => %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "50"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "50"}},
      %{"label" => "vend", "arity" => 0, "args" => %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
    efsm = EFSM.mergeStates(efsm,transitionTable,"q5","q3")
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "50"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "50"}},
      %{"label" => "vend", "arity" => 0, "args" => %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "100"}},
      %{"label" => "vend", "arity" => 0, "args" => %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
  end

  test "to JSON" do
    {efsm, transitionTable} = EFSM.read("test/support_files/unmerged.json")
    assert EFSM.to_json_map(efsm, transitionTable) == %{"q0" => %{"select:1[i1=coke]" => "q1"},
      "q1" => %{"coin:1[i1=100]" => "q5", "coin:1[i1=50]" => "q2"},
      "q2" => %{"coin:1[i1=50]" => "q3"}, "q3" => %{"vend:0/o1:=coke" => "q4"},
      "q4" => %{}, "q5" => %{"vend:0/o1:=coke" => "q6"}, "q6" => %{}}
    File.write("test/support_files/test.json", EFSM.to_json(efsm, transitionTable), [:binary])
  end

  test "to dot" do
    {efsm, transitionTable} = EFSM.read("test/support_files/unmerged.json")
    File.write("test/support_files/test.dot", EFSM.to_dot(efsm, transitionTable), [:binary])
  end

end
