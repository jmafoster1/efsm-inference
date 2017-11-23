defmodule EFSM do
  def getMatchingTransition(efsm, state, label, arity, args, registers, transitionTable) do
    outs = efsm[state][:outs]
    Enum.filter(outs, fn({_dest, ref}) -> Transition.matchTransition(transitionTable, ref, label, arity, args, registers) end)
  end

  def acceptsTraceSet(traces, efsm, transitionTable, state, registers) do
    Enum.all?((for t <- traces, do: acceptsTrace(t, efsm, transitionTable, state, registers, 0, [])))
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
    h = Trace.parseInput(h)
    possibleTransitions = getMatchingTransition(efsm, state, h["label"], h["arity"], h["args"], registers, transitionTable)
    case possibleTransitions do
      [] -> false
      [{dest, ref}] ->
        details = TransitionTable.get(transitionTable, ref)
        IO.inspect {state, details, dest}
        {outputs, updated} = Transition.applyTransition(details, registers, h["args"])
        acceptsTrace(t, efsm, transitionTable, dest, updated, verbosity, [{outputs, updated} | trace])
    end
  end

  def mergeStates(efsm, transitionTable, s1, s2) do
    newState = s1 <> s2
    efsm = Map.put(efsm, newState, %{
      ins: Map.merge(efsm[s1][:ins], efsm[s2][:ins]),
      outs: Map.merge(efsm[s1][:outs], efsm[s2][:outs])
    })
    oldS1Ins = List.zip([
      List.duplicate(s1, length(Map.keys(efsm[s1][:ins]))),
      Map.keys(efsm[s1][:ins]),
      List.duplicate(:outs, length(Map.keys(efsm[s1][:ins])))])
    oldS2Ins = List.zip([
      List.duplicate(s2, length(Map.keys(efsm[s2][:ins]))),
      Map.keys(efsm[s2][:ins]),
      List.duplicate(:outs, length(Map.keys(efsm[s2][:ins])))])
    oldS1Outs = List.zip([
      List.duplicate(s1, length(Map.keys(efsm[s1][:outs]))),
      Map.keys(efsm[s1][:outs]),
      List.duplicate(:ins, length(Map.keys(efsm[s1][:outs])))])
    oldS2Outs = List.zip([
      List.duplicate(s2, length(Map.keys(efsm[s2][:outs]))),
      Map.keys(efsm[s2][:outs]),
      List.duplicate(:ins, length(Map.keys(efsm[s2][:outs])))])

    efsm = updateKeys(efsm, oldS1Ins++oldS2Ins++oldS1Outs++oldS2Outs, newState)
    efsm = Map.drop(efsm, [s1, s2])
    removeNondeterminism(efsm, transitionTable, newState)
  end

  def updateKeys(efsm, [], _newState) do
    efsm
  end
  def updateKeys(efsm, [h|t], newState) do
    updateKeys(updateKey(efsm, h, newState), t, newState)
  end

  def updateKey(efsm, {oldState, state, direction}, newState) when direction == :ins or direction == :outs do
    newIns = Map.put(efsm[state][direction], newState, efsm[state][direction][oldState])
    newIns = Map.delete(newIns, oldState)
    newState = Map.put(efsm[state], direction, newIns)
    Map.put(efsm, state, newState)
  end

  def removeNondeterminism(efsm, transitionTable, merged) do
    outs = Map.to_list(efsm[merged][:outs])
    pairs = pairs(outs)
    removeNondeterminism(efsm, transitionTable, merged, pairs)
  end

  def removeNondeterminism(efsm, _transitionTable, _merged, []) do
    efsm
  end
  def removeNondeterminism(efsm, transitionTable, merged, [h|t]) do
    {{s1, ref1}, {s2, ref2}} = h
    if (Transition.compatible(transitionTable, ref1, ref2) &&
        Map.has_key?(efsm, s1) && Map.has_key?(efsm, s2)) do
      efsm = mergeStates(efsm, transitionTable, s1, s2)
      removeNondeterminism(efsm, transitionTable, merged, t)
    else
      removeNondeterminism(efsm, transitionTable, merged, t)
    end
  end

  def pairs(outs) do
    for lst <- combination(2, outs), do: List.to_tuple(lst)
  end

  def combination(0, _) do
    [[]]
  end
  def combination(_, []) do
    []
  end
  def combination(n, [x|xs]) do
    (for y <- combination(n - 1, xs), do: [x|y]) ++ combination(n, xs)
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

  def to_json_map(efsm, transitionTable) do
    to_json(Map.keys(efsm), efsm, transitionTable)
  end

  @doc """
  Converts an EFSM to json format for textual representation
  """
  def to_json(efsm, transitionTable) do
    Poison.encode!(to_json_map(efsm, transitionTable))
  end

  defp to_json([], _efsm, _transitionTable) do
    %{}
  end
  defp to_json([h|t], efsm, transitionTable) do
    transitions = efsm[h][:outs]
    Map.put(to_json(t, efsm, transitionTable), h, transitions_to_json(Map.to_list(transitions), transitionTable))
  end

  defp transitions_to_json([], _transitionTable) do
    %{}
  end
  defp transitions_to_json([h|t], transitionTable) do
    {dest, ref} = h
    Map.put(transitions_to_json(t, transitionTable), Transition.to_json(transitionTable, ref), dest)
  end

  @doc """
  Converts an EFSM to dot format for visual representation
  """
  def to_dot(fsm, transitionTable) do
    json = to_json_map(fsm, transitionTable)
    {states, transitions} = fsm_to_dot(Map.keys(json), json, [], [])
    "digraph G {\n  " <> Enum.join(states, ";\n  ") <> ";\n  " <> Enum.join(transitions, ";\n  ") <> ";\n}"
  end

  defp fsm_to_dot([], _fsm, states, transitions) do
    {Enum.reverse(states), transitions}
  end
  defp fsm_to_dot([h|t], fsm, states, transitions) do
    state = if h == "q0" do
      "q0 [color=\"black\" fillcolor=\"green\" shape=\"doublecircle\" style=\"filled\"]"
    else
      h <> " [color=\"black\" fillcolor=\"white\" shape=\"circle\" style=\"filled\"]"
    end
    transitions_dot = transitions_to_dot(Map.keys(fsm[h]), h,fsm[h])
    fsm_to_dot(t, fsm, [state | states], transitions ++ transitions_dot)
  end

  defp transitions_to_dot([], _state, _transitions) do
    []
  end
  defp transitions_to_dot([h|t], state, transitions) do
    transition = state <> " -> " <> transitions[h] <> " [label=\"" <> h <> "\"]"
    [transition | transitions_to_dot(t, state, transitions)]
  end
end
