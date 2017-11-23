label = "(?<label>\\w+)"
arity = "(:(?<arity>\\d+){0,1})"
guard = "(~{0,1}((\\w+)|('\\w+'))(=|>|(>=)|(<=)|(!=))((\\w+)|('\\w+')))"
guard = guard <> "((\\|" <> guard <> ")|" <> "(\\&" <> guard <> "))*"
guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
output = "o\\d:=((\\w+)|('\\w+'))"
outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
aexp = "(\\d+|\\w+|'\\w+')"
aexp = aexp <> "(" <> "(\\+|-|\\*|\/)" <> aexp <> ")*"
update = "r\\d:=" <> aexp
update = update <> "((-" <> update <> ")|" <> "(\\+" <> update <> "))*"
updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\]){0,1}"
rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
{:ok, transition} = Regex.compile(label<>arity<>guards<>rhs)

IO.inspect Regex.named_captures(transition, "coin:1/[r2:=r2+i1]")
