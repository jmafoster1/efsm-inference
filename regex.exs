label = "(?<label>\\w+)"
arity = "(:(?<arity>\\d+){0,1})"
guard = "(~{0,1}((\\w+)|('\\w+'))(=|>|(>=)|(<=)|(!=))((\\w+)|('\\w+')))"
guard = guard <> "((\\|" <> guard <> ")|" <> "(\\&" <> guard <> "))*"
guards = "(\\[(?<guards>("<>guard<>"(,"<>guard<>")*"<>"))\\]){0,1}"
output = "o\\d:=\\w+"
outputs = "(?<outputs>("<>output<>"(,"<>output<>")*"<>")){0,1}"
update = "((r\\d:=r\\d(\\+|-|\\*|\\/)((\\w+)|('\\w+')))|(r\\d:=((\\w+)|('\\w+'))))"
updates = "(\\[(?<updates>("<>update<>"(,"<>update<>")*"<>"))\\]){0,1}"
rhs = "("<>"\\/"<>outputs<>updates<>"){0,1}"
{:ok, transition} = Regex.compile(label<>arity<>guards<>rhs)

IO.inspect Regex.named_captures(transition, "vend:0[r2>='100'&r1!='water']/o1:=r1[r2:=r2-'100']")
