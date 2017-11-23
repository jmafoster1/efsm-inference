defmodule Output do
  def outputRegex() do
    "o\\d:=((\\w+)|('\\w+'))"
  end

  def parseOutput(x, include_captures \\ true) do
    List.to_tuple(Regex.split(~r{(:=)} , x, include_captures: include_captures))
  end

  def matchOutputs(expected, actual) do
    Enum.all?(for key <- Map.keys(expected), do: expected[key] == actual[key]) and Enum.all?(for key <- Map.keys(actual), do: expected[key] == actual[key])
  end
end
