defmodule Update do

  def applyUpdate(update, registers, args) do
    store = Map.merge(registers, args)
    case update do
      {r1, ":=", r2, op, value} ->
        value = if Map.has_key?(store, value) do
          store[value]
        else
          value
        end
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
        value = if Map.has_key?(store, value) do
          store[value]
        else
          value
        end
        if Map.has_key?(store, value) do
          Map.put(registers, r1, store[value])
        else
          Map.put(registers, r1, value)
        end
    end

  end

end
