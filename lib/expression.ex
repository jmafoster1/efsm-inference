defmodule Expression do
  def prefix2Infix(tuple) do
    case tuple do
      {:lt, t1, t2}       -> {prefix2Infix(t1), "<",  prefix2Infix(t2)}
      {:gt, t1, t2}       -> {prefix2Infix(t1), ">",  prefix2Infix(t2)}
      {:le, t1, t2}       -> {prefix2Infix(t1), "<=", prefix2Infix(t2)}
      {:ge, t1, t2}       -> {prefix2Infix(t1), ">=", prefix2Infix(t2)}
      {:eq, t1, t2}       -> {prefix2Infix(t1), "=",  prefix2Infix(t2)}
      {:ne, t1, t2}       -> {prefix2Infix(t1), "!=", prefix2Infix(t2)}
      {:plus, t1, t2}     -> {prefix2Infix(t1), "+",  prefix2Infix(t2)}
      {:minus, t1, t2}    -> {prefix2Infix(t1), "-",  prefix2Infix(t2)}
      {:multiply, t1, t2} -> {prefix2Infix(t1), "*",  prefix2Infix(t2)}
      {:divide, t1, t2}   -> {prefix2Infix(t1), "/",  prefix2Infix(t2)}
      {:lit, v}           -> "'"<>v<>"'"
      {:v, v}             -> v
      {{:v, r}, t2}  -> {r, ":=", prefix2Infix(t2)}
    end
  end

  def getValue(value, store) do
    if value == {:lit, nil} or value == nil do
      nil
    else
      value = case value do
        {:lit, val} -> val
        {:v, val} ->
          val = store[val]
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

  def isLiteral(value) do
    String.starts_with?(value, "'") and String.ends_with?(value, "'")
  end

  def tag(value) do
    if isLiteral(value) do
      {:lit, String.slice(value, 1, String.length(value) - 2)}
    else
      {:v, value}
    end
  end

  def untag({:v, v}) do
    v
  end
  def untag({:lit, v}) do
    "'"<>v<>"'"
  end
end
