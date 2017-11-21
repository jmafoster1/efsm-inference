defmodule FSMTest do
  use ExUnit.Case

  setup do
    {:ok, transitionTable} = start_supervised(TransitionTable)
    %{details: transitionTable}
  end

  test "reads efsm from file" do
    {efsm, transitionTable} = FSM.read("test/support_files/drinks_machine.json")
    IO.inspect efsm
    IO.inspect TransitionTable.get(transitionTable,efsm["q0"][:outs]["q1"])
    assert FSM.acceptsTrace([
      %{label: "select", arity: 1, args: %{"i1" => "coke"}},
      %{label: "coin", arity: 1, args: %{"i1" => "10"}},
      %{label: "vend", arity: 0, args: %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == false
    TransitionTable.stop(transitionTable)
  end

  test "accepts a trace", %{details: transitionTable} do
    TransitionTable.put(transitionTable, "q0->q1", %{guards: [], label: "select", outputs: [], updates: [{"r1", ":=", "i1"}], arity: 1})
    TransitionTable.put(transitionTable, "q1->q1", %{guards: [], label: "coin", outputs: [], updates: [{"r2", ":=", "r2", "+", "i1"}], arity: 1})
    TransitionTable.put(transitionTable, "q1->q2", %{guards: [{"r2", ">=", "100"}], label: "vend", outputs: [{"o1", ":=", "r1"}], updates: [{"r2", ":=", "r2", "-", "100"}], arity: 0})
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
    File.write("test/support_files/fsm.json", Poison.encode!(efsm), [:binary])
    assert FSM.acceptsTrace([
      %{label: "select", arity: 1, args: %{"i1" => "coke"}},
      %{label: "coin", arity: 1, args: %{"i1" => "110"}},
      %{label: "vend", arity: 0, args: %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == true
  end

  test "rejects a trace", %{details: transitionTable} do
    TransitionTable.put(transitionTable, "q0->q1", %{guards: [], label: "select", outputs: [], updates: [{"r1", ":=", "i1"}], arity: 1})
    TransitionTable.put(transitionTable, "q1->q1", %{guards: [], label: "coin", outputs: [], updates: [{"r2", ":=", "r2", "+", "i1"}], arity: 1})
    TransitionTable.put(transitionTable, "q1->q2", %{guards: [{"r2", ">=", "100"}], label: "vend", outputs: [{"o1", ":=", "r1"}], updates: [{"r2", ":=", "r2", "-", "100"}], arity: 0})
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
    File.write("test/support_files/fsm.json", Poison.encode!(efsm), [:binary])
    assert FSM.acceptsTrace([
      %{label: "select", arity: 1, args: %{"i1" => "coke"}},
      %{label: "coin", arity: 1, args: %{"i1" => "10"}},
      %{label: "vend", arity: 0, args: %{}}
    ], efsm, transitionTable, "q0", %{}, 0, []) == false
  end
end
