theory Value
imports "Show.Show_Instances"
begin
datatype "value" = Num int | Str String.literal

abbreviation str :: "string \<Rightarrow> value" where
  "str s = str (String.implode s)"

end