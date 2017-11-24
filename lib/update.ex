defmodule Update do

  def updateRegex() do
    aexp = "(\\d+|\\w+|'\\w+')"
    aexp = aexp <> "(" <> "(\\+|-|\\*|\/)" <> aexp <> ")*"
    update = "r\\d:=" <> aexp
    update <> "((-" <> update <> ")|" <> "(\\+" <> update <> "))*"
  end

  def applyUpdate({register, value}, registers, args) do
    store = Map.merge(registers, args)
    Map.put(registers, register, to_string(applyAexp(value, store)))
  end

  def applyAexp({v1, "+", v2}, store) do
    applyAexp(v1, store) + applyAexp(v2, store)
  end
  def applyAexp({v1, "*", v2}, store) do
    applyAexp(v1, store) * applyAexp(v2, store)
  end
  def applyAexp({v1, "-", v2}, store) do
    applyAexp(v1, store) - applyAexp(v2, store)
  end
  def applyAexp({v1, "/", v2}, store) do
    applyAexp(v1, store) / applyAexp(v2, store)
  end
  def applyAexp(value, store) do
    Expression.getValue(value, store)
  end

  def toJSON(outputs) do
    str = Enum.join(updatesToString(outputs), ",")
    if str == "" do
      ""
    else
      "[" <> str <> "]"
    end
  end

  def updatesToString([]) do
    []
  end
  def updatesToString([h|t]) do
    {r, o} = h
    if is_tuple(o) do
      [(r <> ":=" <> Enum.join(Tuple.to_list(o))) | updatesToString(t)]
    else
      [(r <> ":=" <> o) | updatesToString(t)]
    end
  end

  def parseUpdate(string) do
    update = ~r/((?<register>(\w+)):=){0,1}(?<aexp>(.*))/
    captures = Regex.named_captures(update, string)
    {captures["register"], parseValue(captures["aexp"])}
  end

  def parseValue(aexp) do
    plus   = ~r{(?<first>(.*))\+(?<second>(.*))}
    minus  = ~r{(?<first>(.*))-(?<second>(.*))}
    times  = ~r{(?<first>(.*))\*(?<second>(.*))}
    divide = ~r{(?<first>(.*))\/(?<second>(.*))}

    split = Regex.named_captures(minus, aexp)
    if split != nil do
      {parseValue(split["first"]), "-", parseValue(split["second"])}
    else
        split =  Regex.named_captures(plus, aexp)
      if split != nil do
        {parseValue(split["first"]), "+", parseValue(split["second"])}
      else
        split =  Regex.named_captures(times, aexp)
        if split != nil do
          {parseValue(split["first"]), "*", parseValue(split["second"])}
        else
          split =  Regex.named_captures(divide, aexp)
          if split != nil do
            {parseValue(split["first"]), "/", parseValue(split["second"])}
          else
            aexp
          end
        end
      end
    end
  end
end
