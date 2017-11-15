defmodule FSM do
  @moduledoc """
  A hopefully clear and concise implementation of an efsm
  """

  @doc """
  Writes an fsm to json
  """
  def write(filename, data) do
    File.write(filename, Poison.encode!(data), [:binary])
  end

  def parseFSM([], _map, parsed) do
    parsed
  end
  def parseFSM([h|t], map, parsed) do
    parseFSM(t, map, Map.put(parsed, h, parseTransitions(Map.keys(map[h]), map[h], [])))
  end

  def parseTransitions([], _map, parsed) do
    parsed
  end
  def parseTransitions([h|t], map, parsed) do
    parseTransitions(t, map, [parse_transition(h, map[h])|parsed])
  end

  def read(filename) do
    initial = Poison.decode!(File.read!(filename))
    parseFSM(Map.keys(initial), initial, %{})
    # initial
  end

  defp transition_regex() do
    label = "(?<label>\\w+)"
    guard = "(\\w+(=|>|(>=)|(<=)|(~=))\\w+)"
    guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
    output = "o\\d:=\\w+"
    outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
    update = "((r\\d:=r\\d(\\+|-|\\*|\\/)\\w+)|(r\\d:=\\w+))"
    updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\]){0,1}"
    rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
    {:ok, transition} = Regex.compile(label<>guards<>rhs)
    transition
  end

  def parse_transition(transitionString, dest) do
    parts = Regex.named_captures(transition_regex(), transitionString)

    parts = if parts["guards"] == "" do
      Map.put(parts, "guards", [])
    else
          parts = Map.put(parts, "guards", String.split(parts["guards"], ","))
          Map.put(parts, "guards", Enum.map(parts["guards"], fn x -> List.to_tuple(Regex.split(~r{(>=|<=|<|>|=)} , x, include_captures: true)) end))
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

  defp applyGuard(guard, store) do
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

  def accepts([], _efsm, state, registers) do
    IO.inspect {state, registers}
    true
  end
  def accepts([h|t], efsm, state, registers) do
    IO.inspect {state, registers, h["inputs"]}
    possibleTransitions = Enum.filter(efsm[state], fn(tran) -> tran["label"] == h["label"] && applyGuards(tran["guards"], registers, h["inputs"]) end)
    case possibleTransitions do
      [] -> false
      [transition] ->
        accepts(t, efsm, transition["dest"], applyUpdates(transition["updates"], registers, h["inputs"]))
    end
  end


end
