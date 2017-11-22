defmodule EFSM do
  def getMatchingTransition(efsm, state, label, arity, args, registers, transitionTable) do
    outs = efsm[state][:outs]
    Enum.filter(outs, fn({_dest, ref}) -> Transition.matchTransition(transitionTable, ref, label, arity, args, registers) end)
  end

  def acceptsTrace([], _efsm, _transitionTable, state, registers, verbosity, trace) do
    if verbosity > 0 do
      trace = [{state, registers} | trace]
      trace = ["Finished" | trace]
      {true, Enum.reverse(trace)}
    else
      true
    end
  end
  def acceptsTrace([h|t], efsm, transitionTable, state, registers, verbosity, trace) do
    possibleTransitions = getMatchingTransition(efsm, state, h["label"], h["arity"], h["args"], registers, transitionTable)
    case possibleTransitions do
      [] -> false
      [{dest, ref}] ->
        details = TransitionTable.get(transitionTable, ref)
        {outputs, updated} = Transition.applyTransition(details, registers, h["args"])
        acceptsTrace(t, efsm, transitionTable, dest, updated, verbosity, [{outputs, updated} | trace])
    end
  end

  @doc """
  Reads an EFSM from json format
  """
  def read(filename) do
    {:ok, transitionTable} = TransitionTable.start_link([])
    initial = Poison.decode!(File.read!(filename))
    blank =  states(Map.to_list(initial), %{})
    efsm = transitions(Map.to_list(initial), blank, transitionTable)
    {efsm, transitionTable}
  end

  def states([], efsm) do
    efsm
  end
  def states([h|t], efsm) do
    {state, _outs} = h
    efsm = Map.put(efsm, state, %{ins: %{}, outs: %{}})
    states(t, efsm)
  end

  def transitions([], efsm, _transitionTable) do
    efsm
  end
  def transitions([h|t], efsm, transitionTable) do
    {state, transitions} = h
    transitions(t, addTransitions(state, Map.to_list(transitions), efsm, transitionTable), transitionTable)
  end

  def addTransitions(_state, [], efsm, _transitionTable) do
    efsm
  end
  def addTransitions(state, [h|t], efsm, transitionTable) do
    {details, dest} = h
    efsm = addTransition(state, details, dest, efsm, transitionTable)
    addTransitions(state, t, efsm, transitionTable)
  end

  def addTransition(from, details, dest, efsm, transitionTable) do
    ref = Transition.parseTransition(details, transitionTable)
    newIns = Map.put(efsm[dest][:ins], from, ref)
    newOuts = Map.put(efsm[from][:outs], dest, ref)
    newFrom = Map.put(efsm[from], :outs, newOuts)
    efsm = Map.put(efsm, from, newFrom)
    newDest = Map.put(efsm[dest], :ins, newIns)
    Map.put(efsm, dest, newDest)
  end
end
