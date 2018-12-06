defmodule Guard do
  # TODO: Allow arithmetic in here, e.g. r1 > i1 + 7
  def applyGuard({:disj, term1, term2}, store) do
    applyGuard(term1, store) or applyGuard(term2, store)
  end
  def applyGuard({:conj, term1, term2}, store) do
    applyGuard(term1, store) and applyGuard(term2, store)
  end
  def applyGuard({:nt, term1}, store) do
    not applyGuard(term1, store)
  end
  def applyGuard(guard, store) do
    {operator, key, value} = guard
    value = Expression.getValue(value, store)
    case operator do
      :eq ->
        Expression.getValue(key, store) == value
      :gt ->
        Expression.getValue(key, store) >  value
      :lt ->
        Expression.getValue(key, store) <  value
      :le ->
        Expression.getValue(key, store) <= value
      :ge ->
        Expression.getValue(key, store) >= value
      :ne ->
        Expression.getValue(key, store) != value
    end
  end

  def toJSON(guards) do
    str = Enum.join(Enum.map(guards, fn tuple -> Enum.join(Tuple.to_list(Expression.prefix2Infix(tuple))) end), ",")
    if str == "" do
      ""
    else
      "[" <> str <> "]"
    end
  end

  def guardRegex() do
    guard = "(~{0,1}((\\w+)|('\\w+'))(=|>|(>=)|(<=)|(!=))((\\w+)|('\\w+')))"
    guard <> "((\\|" <> guard <> ")|" <> "(\\&" <> guard <> "))*"
  end

  def compatible(g1, g2) when is_list(g1) and is_list(g2) do
    Enum.all?(for i <- g1, j <- g2, do: compatible(i, j))
  end
  def compatible(g1, g2) do
    if g1 == g2 do
      true
    else
      false
    end
  end

  def parseGuard(string) do
    disj = ~r{(?<first>(.*))\|(?<second>(.*))}
    conj = ~r{(?<first>(.*))\&(?<second>(.*))}
    neg  = ~r{~(?<first>(.*))}

    split =  Regex.named_captures(conj, string)
    if split != nil do
      {:conj, parseGuard(split["first"]), parseGuard(split["second"])}
    else
        split =  Regex.named_captures(disj, string)
      if split != nil do
        {:disj, parseGuard(split["first"]), parseGuard(split["second"])}
      else
        split =  Regex.named_captures(neg, string)
        if split != nil do
          {:nt, parseGuard(split["first"])}
        else
          parseLiteral(List.to_tuple(Regex.split(~r{(>=|<=|<|>|=|!=)} , string, include_captures: true)))
        end
      end
    end
  end

  def parseLiteral({t1, ">", t2}) do
    {:gt, Expression.tag(t1), (t2)}
  end
  def parseLiteral({t1, "<", t2}) do
    {:lt, Expression.tag(t1), Expression.tag(t2)}
  end
  def parseLiteral({t1, ">=", t2}) do
    {:ge, Expression.tag(t1), Expression.tag(t2)}
  end
  def parseLiteral({t1, "<=", t2}) do
    {:le, Expression.tag(t1), Expression.tag(t2)}
  end
  def parseLiteral({t1, "!=", t2}) do
    {:ne, Expression.tag(t1), Expression.tag(t2)}
  end
  def parseLiteral({t1, "=", t2}) do
    {:eq, Expression.tag(t1), Expression.tag(t2)}
  end
end
