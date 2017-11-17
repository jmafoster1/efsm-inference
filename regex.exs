label = "(?<label>\\w+)"
guard = "(~{0,1}\\w+(=|>|(>=)|(<=)|(!=))\\w+)"
guard = guard <> "((\\|" <> guard <> ")|" <> "(\\&" <> guard <> "))*"
guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
output = "o\\d:=\\w+"
outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
update = "((r\\d:=r\\d(\\+|-|\\*|\\/)\\w+)|(r\\d:=\\w+))"
updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\]){0,1}"
rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
{:ok, transition} = Regex.compile(label<>guards<>rhs)

IO.inspect Regex.named_captures(transition, "vend[r2>=100&r1!=water]/o1:=r1[r2:=r2-100]")


defmodule Logic do
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
    case operator do
      "=" ->
        store[key] == value
      ">" ->
        Float.parse(store[key]) >  Float.parse(value)
      "<" ->
        Float.parse(store[key]) <  Float.parse(value)
      "<=" ->
        Float.parse(store[key]) <= Float.parse(value)
      ">=" ->
        Float.parse(store[key]) >= Float.parse(value)
      "!=" ->
        Float.parse(store[key]) != Float.parse(value)
    end
  end


  def logicSplit(string) do
    disj = ~r{(?<first>(.*))\|(?<second>(.*))}
    conj = ~r{(?<first>(.*))\&(?<second>(.*))}
    neg  = ~r{~(?<first>(.*))}

    split =  Regex.named_captures(conj, string)
    if split != nil do
      {logicSplit(split["first"]), "&", logicSplit(split["second"])}
    else
        split =  Regex.named_captures(disj, string)
      if split != nil do
        {logicSplit(split["first"]), "|", logicSplit(split["second"])}
      else
        split =  Regex.named_captures(neg, string)
        if split != nil do
          {"~", logicSplit(split["first"])}
        else
          List.to_tuple(Regex.split(~r{(>=|<=|<|>|=|!=)} , string, include_captures: true))
        end
      end
    end
  end
end

registers = %{"r1" => "juice", "r2" => "100"}

guard = Logic.logicSplit("r2>=100&r1=coke|r1=pepsi")

IO.inspect Logic.applyGuard(guard, registers)
