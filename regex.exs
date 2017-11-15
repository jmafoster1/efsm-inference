label = "(?<label>\\w+)"
guard = "(\\w+(=|>|(>=)|(<=)|(~=))\\w+)"
guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
output = "o\\d:=\\w+"
outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
update = "((r\\d:=r\\d(\\+|-|\\*|\\/)\\w+)|(r\\d:=\\w+))"
updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\])"
rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
{:ok, transition} = Regex.compile(label<>guards<>rhs)

IO.inspect Regex.named_captures(transition, "coin/[r2:=r2+i1]")
