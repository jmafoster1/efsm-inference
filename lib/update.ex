defmodule Update do

  def updateRegex() do
    aexp = "(\\d+|\\w+|'\\w+')"
    aexp = aexp <> "(" <> "(\\+|-|\\*|\/)" <> aexp <> ")*"
    update = "r\\d:=" <> aexp
    update <> "((-" <> update <> ")|" <> "(\\+" <> update <> "))*"
  end

  def applyUpdate({{:v, register}, value}, registers, args) do
    store = Map.merge(registers, args)
    Map.put(registers, register, to_string(applyAexp(value, store)))
  end

  def applyAexp({:plus, v1, v2}, store) do
    applyAexp(v1, store) + applyAexp(v2, store)
  end
  def applyAexp({:multiply, v1, v2}, store) do
    applyAexp(v1, store) * applyAexp(v2, store)
  end
  def applyAexp({:minus, v1, v2}, store) do
    applyAexp(v1, store) - applyAexp(v2, store)
  end
  def applyAexp({:divide, v1, v2}, store) do
    applyAexp(v1, store) / applyAexp(v2, store)
  end
  def applyAexp(value, store) do
    Expression.getValue(value, store)
  end

  def toJSON(updates) do
    str = Enum.join(Enum.map(updates, fn tuple -> toString(Expression.prefix2Infix(tuple)) end), ",")
    if str == "" do
      ""
    else
      "[" <> str <> "]"
    end
  end

  def toString({r, ":=", t}) do
    r <> ":=" <> toString(t)
  end
  def toString({r, op, t}) do
    r <> op <> toString(t)
  end
  def toString(t) do
    t
  end


  def parseUpdate(string) do
    update = ~r/((?<register>(\w+)):=){0,1}(?<aexp>(.*))/
    captures = Regex.named_captures(update, string)
    {{:v, captures["register"]}, parseValue(captures["aexp"])}
  end

  def parseValue(aexp) do
    plus   = ~r{(?<first>(.*))\+(?<second>(.*))}
    minus  = ~r{(?<first>(.*))-(?<second>(.*))}
    times  = ~r{(?<first>(.*))\*(?<second>(.*))}
    divide = ~r{(?<first>(.*))\/(?<second>(.*))}

    split = Regex.named_captures(minus, aexp)
    if split != nil do
      {:minus, parseValue(split["first"]), parseValue(split["second"])}
    else
        split =  Regex.named_captures(plus, aexp)
      if split != nil do
        {:plus, parseValue(split["first"]), parseValue(split["second"])}
      else
        split =  Regex.named_captures(times, aexp)
        if split != nil do
          {:multiply, parseValue(split["first"]), parseValue(split["second"])}
        else
          split =  Regex.named_captures(divide, aexp)
          if split != nil do
            {:divide, parseValue(split["first"]), parseValue(split["second"])}
          else
            Expression.tag(aexp)
          end
        end
      end
    end
  end
end
