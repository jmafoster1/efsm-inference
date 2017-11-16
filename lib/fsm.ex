defmodule FSM do
  @moduledoc """
  A hopefully clear and concise implementation of an efsm
  """

  @doc """
  Writes data to file
  """
  def write(filename, data) do
    File.write(filename, data, [:binary])
  end

  @doc """
  Writes an efsm to json
  """
  def save_json(filename, fsm) do
    write(filename, Poison.encode!(fsm_to_json(fsm)))
  end

  @doc """
  Writes an efsm to dot
  """
  def save_dot(filename, fsm) do
    write(filename, fsm_to_dot(fsm))
  end

  @doc """
  Converts an EFSM to dot format for visual representation
  """
  def fsm_to_dot(fsm) do
    json = fsm_to_json(fsm)
    {states, transitions} = fsm_to_dot(Map.keys(json), json, [], [])
    "digraph G {\n  " <> Enum.join(states, ";\n  ") <> ";\n  " <> Enum.join(transitions, ";\n  ") <> ";\n}"
  end

  @doc """
  Converts an EFSM to json format for textual representation
  """
  def fsm_to_json(fsm) do
    fsm_to_json(Map.keys(fsm), fsm)
  end

  @doc """
  Reads an EFSM from json format
  """
  def read(filename) do
    initial = Poison.decode!(File.read!(filename))
    parseFSM(Map.keys(initial), initial)
  end

  defp transition_regex() do
    label = "(?<label>\\w+)"
    guard = "(~{0,1}\\w+(=|>|(>=)|(<=)|(!=))\\w+)"
    guard = guard <> "((\\|" <> guard <> ")|" <> "(\\&" <> guard <> "))*"
    guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
    output = "o\\d:=\\w+"
    outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
    update = "((r\\d:=r\\d(\\+|-|\\*|\\/)\\w+)|(r\\d:=\\w+))"
    updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\]){0,1}"
    rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
    {:ok, transition} = Regex.compile(label<>guards<>rhs)
    transition
  end

  def logicSplit(string) do
    disj = ~r{(?<first>(.*))\|(?<second>(.*))}
    conj = ~r{(?<first>(.*))\&(?<second>(.*))}
    neg  = ~r{~(?<first>(.*))}

    split =  Regex.named_captures(conj, string)
    if split != nil do
      {logicSplit(split["first"]), "&", logicSplit(split["second"])}
    else
        split =  Regex.named_captures(disj, string)
      if split != nil do
        {logicSplit(split["first"]), "|", logicSplit(split["second"])}
      else
        split =  Regex.named_captures(neg, string)
        if split != nil do
          {"~", logicSplit(split["first"])}
        else
          List.to_tuple(Regex.split(~r{(>=|<=|<|>|=|!=)} , string, include_captures: true))
        end
      end
    end
  end

  def parse_transition(transitionString, dest) do
    parts = Regex.named_captures(transition_regex(), transitionString)

    parts = if parts["guards"] == "" do
      Map.put(parts, "guards", [])
    else
          parts = Map.put(parts, "guards", String.split(parts["guards"], ","))
          parts = Map.put(parts, "guards", Enum.map(parts["guards"], fn x -> logicSplit(x) end))
    end
    parts = if parts["outputs"] == "" do
      Map.put(parts, "outputs", [])
    else
      parts = Map.put(parts, "outputs", String.split(parts["outputs"], ","))
      Map.put(parts, "outputs", Enum.map(parts["outputs"], fn x -> List.to_tuple(Regex.split(~r{(:=)} , x, include_captures: true)) end))
    end
    parts = if parts["updates"] == "" do
      Map.put(parts, "updates", [])
    else
      parts = Map.put(parts, "updates", String.split(parts["updates"], ","))
      Map.put(parts, "updates", Enum.map(parts["updates"], fn x -> List.to_tuple(Regex.split(~r{(\/|\*|\+|-|:=)} , x, include_captures: true)) end))
    end
    Map.put(parts, "dest", dest)
  end

  def applyGuard({term1, "|", term2}, store) do
    applyGuard(term1, store) or applyGuard(term2, store)
  end
  def applyGuard({term1, "&", term2}, store) do
    applyGuard(term1, store) and applyGuard(term2, store)
  end
  def applyGuard({"~", term1}, store) do
    not applyGuard(term1, store)
  end
  def applyGuard(guard, store) do
    {key, operator, value} = guard
    case operator do
      "=" ->
        store[key] == value
      ">" ->
        Float.parse(store[key]) >  Float.parse(value)
      "<" ->
        Float.parse(store[key]) <  Float.parse(value)
      "<=" ->
        Float.parse(store[key]) <= Float.parse(value)
      ">=" ->
        Float.parse(store[key]) >= Float.parse(value)
      "!=" ->
        Float.parse(store[key]) != Float.parse(value)
    end
  end

  def applyGuards(guards, registers, inputs) do
    Enum.all?(guards, fn(g) -> applyGuard(g, Map.merge(registers, inputs)) end)
  end

  defp applyOutput(output, store) do
    if Map.has_key?(store, output) do
      store[output]
    else
      output
    end
  end

  def applyOutputs(outputs, registers, inputs) do
    store = Map.merge(registers, inputs)
    for {key, ":=", value} <- outputs, do: {key, applyOutput(value, store)}
  end

  def applyUpdate(update, registers, inputs) do
    store = Map.merge(registers, inputs)
    {r1, ":=", r2, op, value} = update
    {r2, _} = if Map.has_key?(store, r2)  do
      Float.parse(store[r2])
    else
      {0, 0}
    end
    {value, _} = Float.parse(value)
    case op do
      "+" ->
        Map.put(registers, r1, Float.to_string(r2+value))
      "-" ->
        Map.put(registers, r1, Float.to_string(r2-value))
      "*" ->
        Map.put(registers, r1, Float.to_string(r2*value))
      "/" ->
        Map.put(registers, r1, Float.to_string(r2/value))
    end
  end

  def applyUpdates([], registers, _inputs) do
    registers
  end
  def applyUpdates([h|t], registers, inputs) do
    store = Map.merge(registers, inputs)
    case h do
      {r1, ":=", r2, op, value} ->
        if Map.has_key?(store, value) do
          applyUpdates(t, applyUpdate({r1, ":=", r2, op, store[value]}, registers, inputs), inputs)
        else
          applyUpdates(t, applyUpdate(h, registers, inputs), inputs)
        end
      {r1, ":=", value} ->
        if Map.has_key?(store, value) do
          applyUpdates(t, Map.put(registers, r1, store[value]), inputs)
        else
          applyUpdates(t, Map.put(registers, r1, value), inputs)
        end
    end
  end

  def parseInput(input) do
    {:ok, regex} = Regex.compile("(?<label>\\w+)\\((?<inputs>(\\w+)(,\\w+)*){0,1}\\)")
    captures = Regex.named_captures(regex, input)
    case captures["inputs"] do
      "" -> Map.put(captures, "inputs", %{})
      _ ->
      captures = Map.put(captures, "inputs", String.split(captures["inputs"], ","))
      enumerated = List.zip([Enum.to_list(1..length(captures["inputs"])), captures["inputs"]])
      pairs = for {key, value} <- enumerated, do: {"i"<>Integer.to_string(key), value}
      %{"label" => captures["label"], "inputs" => Enum.into(pairs, %{})}
    end
  end

  def parseInputList(inputList) do
    for s <- String.split(inputList, ","), do: parseInput(s)
  end

  def accepts(list, efsm, state, registers, verbosity \\ 0)
  def accepts([], _efsm, state, registers, verbosity) do
    if verbosity > 0 do
      IO.inspect {state, registers}
      IO.puts "Finished"
    end
    true
  end
  def accepts([h|t], efsm, state, registers, verbosity) do
    if verbosity > 0 do
      IO.inspect {state, registers, h["label"], h["inputs"]}
    end
    possibleTransitions = Enum.filter(efsm[state], fn(tran) -> tran["label"] == h["label"] && applyGuards(tran["guards"], registers, h["inputs"]) end)
    case possibleTransitions do
      [] -> false
      [transition] ->
        accepts(t, efsm, transition["dest"], applyUpdates(transition["updates"], registers, h["inputs"]), verbosity)
    end
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

  defp fsm_to_json([], _fsm) do
    %{}
  end
  defp fsm_to_json([h|t], fsm) do
    transitions = fsm[h]
    Map.put(fsm_to_json(t, fsm), h, transitions_to_json(transitions))
  end

  defp transitions_to_json([]) do
    %{}
  end
  defp transitions_to_json([h|t]) do
    transition = h["label"]<>list_to_string(h["guards"], "[", "]")<>"/"<>list_to_string(h["outputs"])<>list_to_string(h["updates"], "[", "]")
    Map.put(transitions_to_json(t), transition, h["dest"])
  end

  defp list_to_string(lst, pre \\ "", post \\ "") do
    str = Enum.join(Enum.map(lst, fn tuple -> Enum.join(Tuple.to_list(tuple)) end), ",")
    if str == "" do
      ""
    else
      pre <> str <> post
    end
  end

  defp parseFSM([], _map) do
    %{}
  end
  defp parseFSM([h|t], map) do
    Map.put(parseFSM(t, map), h, parseTransitions(Map.keys(map[h]), map[h]))
  end

  defp parseTransitions([], _map) do
    []
  end
  defp parseTransitions([h|t], map) do
    [parse_transition(h, map[h])|parseTransitions(t, map)]
  end


end
