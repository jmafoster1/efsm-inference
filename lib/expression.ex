defmodule Expression do
  def getValue(value, store) do
    literal = String.starts_with?(value, "'") and String.ends_with?(value, "'")
    value = if literal do
      String.slice(value, 1, String.length(value)-2)
    else
      store[value]
    end
  end
end
