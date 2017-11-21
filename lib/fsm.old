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

  @doc """
  Indicates whether a given EFSM accepts a given input
  """
  def accepts(efsm, input, verbosity \\ 0, state \\ "q0") do
    accepts(parseInputList(input), efsm, state, %{}, verbosity, [])
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

  defp logicSplit(string) do
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

  defp parse_transition(transitionString, dest) do
    parts = Regex.named_captures(transition_regex(), transitionString)
    parts = if parts["guards"] == "" do
      Map.put(parts, "guards", [])
    else
          parts = Map.put(parts, "guards", String.split(parts["guards"], ","))
          Map.put(parts, "guards", Enum.map(parts["guards"], fn x -> logicSplit(x) end))
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

  # TODO: Allow arithmetic in here, e.g. r1 > i1 + 7
  defp applyGuard({term1, "|", term2}, store) do
    applyGuard(term1, store) or applyGuard(term2, store)
  end
  defp applyGuard({term1, "&", term2}, store) do
    applyGuard(term1, store) and applyGuard(term2, store)
  end
  defp applyGuard({"~", term1}, store) do
    not applyGuard(term1, store)
  end
  defp applyGuard(guard, store) do
    {key, operator, value} = guard
    case operator do
      "=" ->
        store[key] == value
      ">" ->
        applyOp(store[key], value, fn(a, b) -> a > b end)
        # Float.parse(store[key]) >  Float.parse(value)
      "<" ->
        applyOp(store[key], value, fn(a, b) -> a < b end)
        # Float.parse(store[key]) <  Float.parse(value)
      "<=" ->
        applyOp(store[key], value, fn(a, b) -> a <= b end)
        # Float.parse(store[key]) <= Float.parse(value)
      ">=" ->
        applyOp(store[key], value, fn(a, b) -> a >= b end)
        # Float.parse(store[key]) >= Float.parse(value)
      "!=" ->
        store[key] != value
    end
  end

  # TODO: remove this in favour of a function which returns either parsed number or original value
  defp applyOp(a, b, op) do
    x = Float.parse(a)
    y = Float.parse(b)
    if x != :error and y != :error do
      op.(x, y)
    else
      op.(a, b)
    end
  end

  defp applyGuards(guards, registers, args) do
    Enum.all?(guards, fn(g) -> applyGuard(g, Map.merge(registers, args)) end)
  end

  defp applyOutput(output, store) do
    if Map.has_key?(store, output) do
      store[output]
    else
      output
    end
  end

  defp applyOutputs([], _registers, _args) do
    %{}
  end

  defp applyOutputs([h|t], registers, args) do
    store = Map.merge(registers, args)
    {key, ":=", value} = h
    Map.put(applyOutputs(t, registers, args), key, applyOutput(value, store))
  end

  defp applyUpdate(update, registers, args) do
    store = Map.merge(registers, args)
    {r1, ":=", r2, op, value} = update
    # TODO: Improve this to make store lookup explicit
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

  defp applyUpdates([], registers, _args) do
    registers
  end
  defp applyUpdates([h|t], registers, args) do
    store = Map.merge(registers, args)
    case h do
      {r1, ":=", r2, op, value} ->
        if Map.has_key?(store, value) do
          applyUpdates(t, applyUpdate({r1, ":=", r2, op, store[value]}, registers, args), args)
        else
          applyUpdates(t, applyUpdate(h, registers, args), args)
        end
      {r1, ":=", value} ->
        if Map.has_key?(store, value) do
          applyUpdates(t, Map.put(registers, r1, store[value]), args)
        else
          applyUpdates(t, Map.put(registers, r1, value), args)
        end
    end
  end

  defp parseInput(input) do
    {:ok, regex} = Regex.compile("(?<label>\\w+)\\((?<args>(\\w+)(,\\w+)*){0,1}\\)")
    captures = Regex.named_captures(regex, input)
    case captures["args"] do
      "" -> Map.put(captures, "args", %{})
      _ ->
      captures = Map.put(captures, "args", String.split(captures["args"], ","))
      enumerated = List.zip([Enum.to_list(1..length(captures["args"])), captures["args"]])
      pairs = for {key, value} <- enumerated, do: {"i"<>Integer.to_string(key), value}
      %{"label" => captures["label"], "args" => Enum.into(pairs, %{})}
    end
  end

  defp parseInputList(inputList) do
    for s <- inputList, do: IO.inspect(parseInput(s))
  end

  defp accepts([], _efsm, state, registers, verbosity, trace) do
    if verbosity > 0 do
      trace = [{state, registers} | trace]
      trace = ["Finished" | trace]
      {true, Enum.reverse(trace)}
    else
      true
    end
  end
  defp accepts([h|t], efsm, state, registers, verbosity, trace) do
    possibleTransitions = Enum.filter(efsm[state], fn(tran) -> tran["label"] == h["label"] && applyGuards(tran["guards"], registers, h["args"]) end)
    case possibleTransitions do
      [] -> false
      [transition] ->
        registers = applyUpdates(transition["updates"], registers, h["args"])
        trace = if verbosity > 0 do
          [{state, registers, h["label"], h["args"], applyOutputs(transition["outputs"], registers, h["args"])} | trace]
        else
          trace
        end
        accepts(t, efsm, transition["dest"], registers, verbosity, trace)
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
