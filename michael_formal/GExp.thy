theory GExp
imports "~~/src/HOL/IMP/AExp"
begin
datatype gexp = Eq vname aexp | Gt vname aexp | Lt vname aexp | Not gexp | And gexp gexp


abbreviation
  Le :: "vname \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Le v va \<equiv> Not (Gt v va)"

abbreviation
  Ge :: "vname \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Ge v va \<equiv> Not (Lt v va)"

abbreviation
  Ne :: "vname \<Rightarrow> aexp \<Rightarrow> gexp" where
  "Ne v va \<equiv> Not (Eq v va)"

abbreviation gOr :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" where
  "gOr v va \<equiv> Not (And (Not v) (Not va))"

fun gval :: "gexp \<Rightarrow> state \<Rightarrow> bool" where
  "gval (Lt a\<^sub>1 a\<^sub>2) s = (aval (V a\<^sub>1) s < aval a\<^sub>2 s)" |
  "gval (Gt a\<^sub>1 a\<^sub>2) s = (aval (V a\<^sub>1) s > aval a\<^sub>2 s)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) s = (aval (V a\<^sub>1) s = aval a\<^sub>2 s)" |
  "gval (Not a) s = (\<not> gval a s)" |
  "gval (And a\<^sub>1 a\<^sub>2) s = (gval a\<^sub>1 s \<and> gval a\<^sub>2 s)"

end