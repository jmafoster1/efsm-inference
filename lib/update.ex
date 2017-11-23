defmodule Update do

  def applyUpdate(update, registers, args) do
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

  def parseUpdate(update) do
    # IO.inspect parseUpdate1(update)
    List.to_tuple(Regex.split(~r{(\/|\*|\+|-|:=)} , update, include_captures: true))
  end

  def parseUpdate1(string) do
    plus   = ~r{(?<first>(.*))\+(?<second>(.*))}
    minus  = ~r{(?<first>(.*))-(?<second>(.*))}
    times  = ~r{(?<first>(.*))\*(?<second>(.*))}
    divide = ~r{(?<first>(.*))\/(?<second>(.*))}
    update = ~r/((?<register>(\w+)):=){0,1}(?<bexp>(.*))/

    IO.inspect Regex.named_captures(update, string)

    split = Regex.named_captures(minus, string)
    value = if split != nil do
      {split["register"], {parseUpdate1(split["first"]), "-", parseUpdate1(split["second"])}}
    else
        split =  Regex.named_captures(plus, string)
      if split != nil do
        {split["register"], {parseUpdate1(split["first"]), "+", parseUpdate1(split["second"])}}
      else
        split =  Regex.named_captures(times, string)
        if split != nil do
          {split["register"], {parseUpdate1(split["first"]), "*", parseUpdate1(split["second"])}}
        else
          split =  Regex.named_captures(divide, string)
          if split != nil do
            {split["register"], {parseUpdate1(split["first"]), "/", parseUpdate1(split["second"])}}
          else
            string
          end
        end
      end
    end
  end
end
