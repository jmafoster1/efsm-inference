defmodule EFSMTest do
  use ExUnit.Case

  setup do
    {:ok, transitionTable} = start_supervised(TransitionTable)
    %{details: transitionTable}
  end

  test "reads efsm from file" do
    {efsm, transitionTable} = EFSM.read("test/support_files/drinks_machine.json")
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "100"}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
    TransitionTable.stop(transitionTable)
  end

  test "accepts a trace", %{details: transitionTable} do
    TransitionTable.put(transitionTable, "q0->q1", %{"guards" => [], "label" => "select", "outputs" => [], "updates" => [{"r1", ":=", "i1"}], "arity" => 1})
    TransitionTable.put(transitionTable, "q1->q1", %{"guards" => [], "label" => "coin", "outputs" => [], "updates" => [{"r2", ":=", "r2", "+", "i1"}], "arity" => 1})
    TransitionTable.put(transitionTable, "q1->q2", %{"guards" => [{"r2", ">=", "100"}], "label" => "vend", "outputs" => [{"o1", ":=", "r1"}], "updates" => [{"r2", ":=", "r2", "-", "100"}], "arity" => 0})
    efsm = %{
    "q0" => %{
        ins: %{},
        outs: %{"q1" => "q0->q1"}
      },
    "q1" => %{
        ins: %{"q0" => "q0->q1", "q1" => "q1->q1"},
        outs: %{"q1" => "q1->q1", "q2" => "q1->q2"}
      },
    "q2" => %{
        ins: %{"q1" => "q1->q2"},
        outs: %{}
      }
    }
    assert EFSM.acceptsTrace([
      %{"label" => "select", "arity" => 1, "args" => %{"i1" => "coke"}},
      %{"label" => "coin", "arity" => 1, "args" => %{"i1" => "110"}},
      %{"label" => "vend", "arity" => 0, "args" => %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
  end

  test "rejects a trace", %{details: transitionTable} do
    TransitionTable.put(transitionTable, "q0->q1", %{"guards" => [], "label" => "select", "outputs" => [], "updates" => [{"r1", ":=", "i1"}], "arity" => 1})
    TransitionTable.put(transitionTable, "q1->q1", %{"guards" => [], "label" => "coin", "outputs" => [], "updates" => [{"r2", ":=", "r2", "+", "i1"}], "arity" => 1})
    TransitionTable.put(transitionTable, "q1->q2", %{"guards" => [{"r2", ">=", "100"}], "label" => "vend", "outputs" => [{"o1", ":=", "r1"}], "updates" => [{"r2", ":=", "r2", "-", "100"}], "arity" => 0})
    efsm = %{
    "q0" => %{
        ins: %{},
        outs: %{"q1" => "q0->q1"}
      },
    "q1" => %{
        ins: %{"q0" => "q0->q1", "q1" => "q1->q1"},
        outs: %{"q1" => "q1->q1", "q2" => "q1->q2"}
      },
    "q2" => %{
        ins: %{"q1" => "q1->q2"},
        outs: %{}
      }
    }
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
