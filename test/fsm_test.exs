defmodule FSMTest do
  use ExUnit.Case
  doctest FSM

  test "reads an fsm from json" do
    assert FSM.read("fsm.json") == %{
      "q0" => [
        %{"guards" => [], "label" => "select", "outputs" => [], "updates" => [{"r1", ":=", "i1"}], "dest" => "q1"}
        ],
      "q1" => [
        %{"guards" => [], "label" => "coin", "outputs" => [], "updates" => [{"r2", ":=", "r2", "+", "i1"}], "dest" => "q1"},
        %{"guards" => [{"r2", ">=", "100"}], "label" => "vend", "outputs" => [{"o1", ":=", "r1"}], "updates" => [{"r2", ":=", "r2", "-", "100"}], "dest" => "q2"}
        ],
      "q2" => []
    }

  end

  test "writes to json" do
    fsm = FSM.read("fsm_test.json")
    FSM.save_json("fsm_test_output.json", fsm)
    assert FSM.read("fsm_test.json") == FSM.read("fsm_test_output.json")
  end

  test "writes to dot" do
    fsm = FSM.read("fsm_test.json")
    FSM.save_dot("fsm.dot", fsm)
  end

  test "parse guards with or" do
    assert FSM.read("fsm_or.json") == %{
      "q0" => [
        %{
          "dest" => "q0",
          "guards" => [
            {"r2", ">=", "100"},
            {{"r1", "=", "coke"}, "|", {"r1", "=", "sprite"}}
          ],
          "label" => "vend",
          "outputs" => [{"o1", ":=", "r1"}, {"o2", ":=", "test"}],
          "updates" => [{"r2", ":=", "r2", "-", "100"}]
        }]
      }
  end

  test "parse guards with and" do
    assert FSM.read("fsm_and.json") == %{
      "q0" => [
        %{
          "dest" => "q0",
          "guards" => [
            {"r2", ">=", "100"},
            {{"r1", "=", "coke"}, "&", {"r1", "=", "sprite"}}
          ],
          "label" => "vend",
          "outputs" => [{"o1", ":=", "r1"}, {"o2", ":=", "test"}],
          "updates" => [{"r2", ":=", "r2", "-", "100"}]
        }]
      }
  end

  test "accepts a string of inputs" do
    fsm = assert FSM.read("fsm.json")
    assert FSM.accepts(fsm, "select(coke),coin(50),coin(20),coin(20),coin(20),vend()") == true
  end

  test "reject a string of inputs" do
    fsm = assert FSM.read("fsm.json")
    assert FSM.accepts(fsm, "select(coke),coin(50),vend()") == false
  end

  test "accepts a string of inputs with or" do
    fsm = assert FSM.read("drinks_machine.json")
    assert FSM.accepts(fsm, "select(coke),coin(50),coin(20),coin(20),coin(20),vend()") == true
  end

  test "accepts a string of inputs with or if price not enough" do
    fsm = assert FSM.read("drinks_machine.json")
    assert FSM.accepts(fsm, "select(pepsi),coin(50),coin(20),coin(20),vend()") == false
  end

  test "rejects a string of inputs with or" do
    fsm = FSM.read("drinks_machine.json")
    assert FSM.accepts(fsm, "select(water),coin(100),vend()") == false
  end

  test "gives outputs" do
    fsm = FSM.read("drinks_machine.json")
    assert FSM.accepts(fsm, "select(coke),coin(100),vend()", 1) == {
      true, [
        {"q0", %{"r1" => "coke"}, "select", %{"i1" => "coke"}, %{"o1" => "coke"}},
        {"q1", %{"r1" => "coke", "r2" => "100.0"}, "coin", %{"i1" => "100"}, %{}},
        {"q1", %{"r1" => "coke", "r2" => "0.0"}, "vend", %{}, %{"o1" => "coke"}},
        {"q2", %{"r1" => "coke", "r2" => "0.0"}},
        "Finished"
      ]
    }
  end
end
