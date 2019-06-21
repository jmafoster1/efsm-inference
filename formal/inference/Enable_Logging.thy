theory Enable_Logging
imports Inference EFSM_Dot
begin

definition writeiDot :: "iEFSM \<Rightarrow> String.literal \<Rightarrow> unit" where
  "writeiDot i s = ()"

definition "timestamp = STR ''''"

definition println :: "String.literal \<Rightarrow> unit" where
  "println s = ()"

fun value2string :: "value \<Rightarrow> String.literal" where
  "value2string (Num n) = show_int n" |
  "value2string (value.Str s) = STR ''\"''+s+STR ''\"''"

fun vname2string :: "vname \<Rightarrow> String.literal" where
  "vname2string (vname.I n) = STR ''i''+show_nat n" |
  "vname2string (R s) = STR ''r''+show_nat s"

fun aexp2string :: "aexp \<Rightarrow> String.literal" where
  "aexp2string (L v) = value2string v" |
  "aexp2string (V v) = vname2string v" |
  "aexp2string (Plus a b) = aexp2string a + STR ''+''+aexp2string b" |
  "aexp2string (Minus a b) = aexp2string a + STR ''-''+aexp2string b"

fun gexp2string :: "gexp \<Rightarrow> String.literal" where
  "gexp2string (gexp.Bc True) = STR ''TRUE''" |
  "gexp2string (gexp.Bc False) = STR ''FALSE''" |
  "gexp2string (gexp.Eq a b) = aexp2string a + STR ''=''+aexp2string b" |
  "gexp2string (gexp.Gt a b) = aexp2string a + STR ''>''+aexp2string b" |
  "gexp2string (gexp.Nor a b) = STR ''!(''+gexp2string a + STR ''||''+gexp2string b+STR '')''" |
  "gexp2string (gexp.Null v) = STR ''NULL ''+aexp2string v"

fun join :: "String.literal list \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "join [] _ = STR ''''" |
  "join [h] _ = h" |
  "join (a#b#t) j = a+j+b+(join t j)"

primrec outputs2string :: "aexp list \<Rightarrow> nat \<Rightarrow> String.literal list" where
  "outputs2string [] _ = []" |
  "outputs2string (h#t) n = (STR ''o''+show_nat n+STR '':=''+aexp2string h)#outputs2string t (n+1)"

fun bool2string :: "bool \<Rightarrow> String.literal" where
  "bool2string True = STR ''TRUE''" |
  "bool2string False = STR ''FALSE''"

definition transition2string :: "transition \<Rightarrow> String.literal" where
  "transition2string t = (Label t)+STR '':''+show_nat (Arity t) + STR ''[''+join (map gexp2string (Guard t)) STR '', ''+STR '']/'' +
                         join (outputs2string (Outputs t) 1) STR '', ''+STR ''[''+join (map (\<lambda>(r, u). vname2string (R r) + STR '':='' + aexp2string u) (Updates t)) STR '', ''+STR '']''"

code_printing
  constant "writeiDot" \<rightharpoonup> (Scala) "Dirties.writeiDot" |
  constant "timestamp" \<rightharpoonup> (Scala) "System.currentTimeMillis.toString" |
  constant "println" \<rightharpoonup> (Scala) "println"


end