defmodule Transition do
  def matchTransition(transitionTable, ref, label, arity, args, registers) do
    details = TransitionTable.get(transitionTable, ref)
    details["label"] == label && details["arity"] == arity && applyGuards(details["guards"], registers, args)
  end

  defp applyGuards(guards, registers, args) do
    Enum.all?(guards, fn(g) -> applyGuard(g, Map.merge(registers, args)) end)
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
        number(store[key]) >  number(value)
      "<" ->
        number(store[key]) <  number(value)
      "<=" ->
        number(store[key]) <= number(value)
      ">=" ->
        number(store[key]) >= number(value)
      "!=" ->
        store[key] != value
    end
  end

  def number(value) do
    case Float.parse(value) do
      :error -> value
      {float, _} -> float
    end
  end

  def applyTransition(details, registers, args) do
    outputs = applyOutputs(details["outputs"], registers, args)
    updated = applyUpdates(details["updates"], registers, args)
    {outputs, updated}
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

  defp transition_regex() do
    label = "(?<label>\\w+)"
    arity = "(:(?<arity>\\d+){0,1})"
    guard = "(~{0,1}\\w+(=|>|(>=)|(<=)|(!=))\\w+)"
    guard = guard <> "((\\|" <> guard <> ")|" <> "(\\&" <> guard <> "))*"
    guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
    output = "o\\d:=\\w+"
    outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
    update = "((r\\d:=r\\d(\\+|-|\\*|\\/)\\w+)|(r\\d:=\\w+))"
    updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\]){0,1}"
    rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
    {:ok, transition} = Regex.compile(label<>arity<>guards<>rhs)
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

  def parseTransition(transitionString, transitionTable) do
    parts = Regex.named_captures(transition_regex(), transitionString)
    parts = if parts["arity"] == "" do
      Map.put(parts, "arity", 0)
    else
      {arity, _} = Integer.parse(parts["arity"])
        Map.put(parts, "arity", arity)
    end
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
    ref = make_ref()
    TransitionTable.put(transitionTable, ref, parts)
    ref
  end


  end
