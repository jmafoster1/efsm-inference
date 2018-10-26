theory Value
imports Main
begin
datatype "value" = Num int | Str String.literal

abbreviation str :: "string \<Rightarrow> value" where
  "str s \<equiv> Str (String.implode s)"

end