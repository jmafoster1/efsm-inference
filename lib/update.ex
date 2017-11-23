defmodule Update do

  def applyUpdateOld(update, registers, args) do
    store = Map.merge(registers, args)
    case update do
      {r1, ":=", r2, op, value} ->
        value = Expression.getValue(value, store)
        {r2, _} = if Map.has_key?(registers, r2)  do
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
      {r1, ":=", value} ->
        value = Expression.getValue(value, store)
        if Map.has_key?(store, value) do
          Map.put(registers, r1, store[value])
        else
          Map.put(registers, r1, value)
        end
    end
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
