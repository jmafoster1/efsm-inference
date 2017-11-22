label = "(?<label>\\w+)"
arity = "(:(?<arity>\\d+){0,1})"
guard = "(~{0,1}\\w+(=|>|(>=)|(<=)|(!=))\\w+)"
guard = guard <> "((\\|" <> guard <> ")|" <> "(\\&" <> guard <> "))*"
guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
output = "o\\d:=\\w+"
outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
update = "((r\\d:=r\\d(\\+|-|\\*|\\/)\\w+)|(r\\d:=\\w+))"
updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\]){0,1}"
rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
{:ok, transition} = Regex.compile(label<>arity<>guards<>rhs)

IO.inspect Regex.named_captures(transition, "select:1/o1:=i1[r1:=i1]")
