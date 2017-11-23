defmodule Output do
  def applyOutput(output, store) do
    if Map.has_key?(store, output) do
      store[output]
    else
      output
    end
  end

  def outputRegex() do
    "o\\d:=((\\w+)|('\\w+'))"
  end
end
