defmodule Output do
  def outputRegex() do
    "o\\d:=((\\w+)|('\\w+'))"
  end

  def parseOutput(x) do
    {o, v} = List.to_tuple(Regex.split(~r{(:=)} , x))
    {{:v, o}, Expression.tag(v)}
  end

  def matchOutputs(expected, actual, store) do
    (Enum.all?(for key <- Map.keys(expected), do: Expression.getValue(expected[key], store) == actual[key]) and
    Enum.all?(for key <- Map.keys(actual), do: Expression.getValue(expected[key], store) == actual[key]))
  end

  def toJSON(outputs) do
    str = Enum.join(Enum.map(outputs, fn tuple -> toString(tuple) end), ",")
    if str == "" do
      ""
    else
      str
    end
  end

  def toString({r, v}) do
    Expression.untag(r) <> ":=" <> Expression.untag(v)
  end
end
