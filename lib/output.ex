defmodule Output do
  def outputRegex() do
    "o\\d:=((\\w+)|('\\w+'))"
  end

  def parseOutput(x) do
    List.to_tuple(Regex.split(~r{(:=)} , x))
  end

  def matchOutputs(expected, actual, store) do
    Enum.all?(for key <- Map.keys(expected), do: Expression.getValue(expected[key], store) == actual[key]) and Enum.all?(for key <- Map.keys(actual), do: Expression.getValue(expected[key], store) == actual[key])
  end

  def toJSON(outputs) do
    str = Enum.join(Enum.map(outputs, fn tuple -> Enum.join(Tuple.to_list(tuple), ":=") end), ",")
    if str == "" do
      ""
    else
      str
    end
  end
end
