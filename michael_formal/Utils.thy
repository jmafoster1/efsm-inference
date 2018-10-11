theory Utils
imports Main
begin

fun join :: "string list \<Rightarrow> string \<Rightarrow> string" where
  "join [] _ = ''''" |
  "join [a] _ = a" |
  "join (a#t) d = a@d@(join t d)"
end