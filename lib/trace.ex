defmodule Trace do
  def parseInput(input) when is_binary(input) do
    {:ok, regex} = Regex.compile("(?<label>\\w+)\\((?<args>(\\w+)(,\\w+)*){0,1}\\)")
    captures = Regex.named_captures(regex, input)
    case captures["args"] do
      "" -> Map.put(Map.put(captures, "args", %{}), "arity", 0)
      _ ->
        captures = Map.put(captures, "args", String.split(captures["args"], ","))
        enumerated = List.zip([Enum.to_list(1..length(captures["args"])), captures["args"]])
        pairs = for {key, value} <- enumerated, do: {"i"<>Integer.to_string(key), value}
        %{"label" => captures["label"], "args" => Enum.into(pairs, %{}), "arity" => length(pairs)}
    end
  end
  def parseInput(input) do
    input
  end
end
