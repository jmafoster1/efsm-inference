defmodule Trace do
  def parseInput(input) when is_binary(input) do
    inputRegex = "(?<label>\\w+)\\((?<args>(\\w+)(,\\w+)*){0,1}\\)(/(?<outputs>("<>Output.outputRegex()<>"(,"<>Output.outputRegex()<>")*"<>")){0,1}){0,1}"
    {:ok, regex} = Regex.compile(inputRegex)
    captures = Regex.named_captures(regex, input)
    pairs = case captures["args"] do
      "" -> []
      _  ->
        args = String.split(captures["args"], ",")
        enumerated = List.zip([Enum.to_list(1..length(args)), args])
        for {key, value} <- enumerated, do: {"i"<>Integer.to_string(key), value}
    end
    expected = if captures["outputs"] == "" do
      %{}
    else
      Enum.into(Enum.map(String.split(captures["outputs"], ","), fn x -> Output.parseOutput(x) end), %{})
    end
    %{
      "label" => captures["label"],
      "args" => Enum.into(pairs, %{}),
      "arity" => length(pairs),
      "expected" => expected
    }
  end
  def parseInput(input) do
    input
  end
end
