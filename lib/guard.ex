defmodule Guard do
  # TODO: Allow arithmetic in here, e.g. r1 > i1 + 7
  def applyGuard({term1, "|", term2}, store) do
    applyGuard(term1, store) or applyGuard(term2, store)
  end
  def applyGuard({term1, "&", term2}, store) do
    applyGuard(term1, store) and applyGuard(term2, store)
  end
  def applyGuard({"~", term1}, store) do
    not applyGuard(term1, store)
  end
  def applyGuard(guard, store) do
    {key, operator, value} = guard
    value = Expression.getValue(value, store)
    case operator do
      "=" ->
        Expression.getValue(key, store) == value
      ">" ->
        Expression.getValue(key, store) >  value
      "<" ->
        Expression.getValue(key, store) <  value
      "<=" ->
        Expression.getValue(key, store) <= value
      ">=" ->
        Expression.getValue(key, store) >= value
      "!=" ->
        Expression.getValue(key, store) != value
    end
  end

  def guardRegex() do
    guard = "(~{0,1}((\\w+)|('\\w+'))(=|>|(>=)|(<=)|(!=))((\\w+)|('\\w+')))"
    guard <> "((\\|" <> guard <> ")|" <> "(\\&" <> guard <> "))*"
  end

  def compatible([], _) do
    true
  end
  def compatible(_, []) do
    true
  end
  def compatible([_h1|_t1], [_h2|_t2]) do
    true
  end

  def parseGuard(string) do
    disj = ~r{(?<first>(.*))\|(?<second>(.*))}
    conj = ~r{(?<first>(.*))\&(?<second>(.*))}
    neg  = ~r{~(?<first>(.*))}

    split =  Regex.named_captures(conj, string)
    if split != nil do
      {parseGuard(split["first"]), "&", parseGuard(split["second"])}
    else
        split =  Regex.named_captures(disj, string)
      if split != nil do
        {parseGuard(split["first"]), "|", parseGuard(split["second"])}
      else
        split =  Regex.named_captures(neg, string)
        if split != nil do
          {"~", parseGuard(split["first"])}
        else
          List.to_tuple(Regex.split(~r{(>=|<=|<|>|=|!=)} , string, include_captures: true))
        end
      end
    end
  end
end
