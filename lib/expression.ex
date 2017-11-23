defmodule Expression do
  def getValue(value, store) do
    literal = String.starts_with?(value, "'") and String.ends_with?(value, "'")
    value = if literal do
      String.slice(value, 1, String.length(value)-2)
    else
      val = store[value]
      if val == nil do
        "0"
      else
        val
      end
    end
    case Float.parse(value) do
      :error -> value
      {float, _} -> float
    end
  end
end
