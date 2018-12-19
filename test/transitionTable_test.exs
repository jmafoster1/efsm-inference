defmodule TransitionTableTest do
  use ExUnit.Case, async: true

  setup do
    {:ok, transitionTable} = start_supervised(TransitionTable)
    %{details: transitionTable}
  end

  test "stores values by key", %{details: transitionTable} do
    assert TransitionTable.get(transitionTable, "milk") == nil

    TransitionTable.put(transitionTable, "milk", 3)
    assert TransitionTable.get(transitionTable, "milk") == 3
  end

  test "deletes values by key", %{details: transitionTable} do
    TransitionTable.put(transitionTable, "cabbage", 3)
    assert TransitionTable.get(transitionTable, "cabbage") == 3
    TransitionTable.delete(transitionTable,"cabbage")
    assert TransitionTable.get(transitionTable, "cabbage") == nil
  end
end
