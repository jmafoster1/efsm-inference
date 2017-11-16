label = "(?<label>\\w+)"
guard = "(~{0,1}\\w+(=|>|(>=)|(<=)|(~=))\\w+)"
guard = guard <> "(\\|~{0,1}" <> guard <> ")*" <> "(\\^~{0,1}" <> guard <> ")*" <> "(~" <> guard <> ")*"
guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
output = "o\\d:=\\w+"
outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
update = "((r\\d:=r\\d(\\+|-|\\*|\\/)\\w+)|(r\\d:=\\w+))"
updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\]){0,1}"
rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
{:ok, transition} = Regex.compile(label<>guards<>rhs)

IO.inspect Regex.named_captures(transition, "vend[~r2>100,r1=coke|r1=pepsi^~r3=test,~r4=test]/o1:=r1,o2:=test[r2:=r2-100,r1:=test]")
