theory CExp
  imports Syntax
begin

datatype cexp = Bc bool | Eq int | Lt int | Gt int | Not cexp | And cexp cexp

abbreviation
  Leq :: "int \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

abbreviation
  Geq :: "int \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

abbreviation
  Neq :: "int \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

fun ceval :: "cexp \<Rightarrow> vname \<Rightarrow> state \<Rightarrow> bool" where
  "ceval (Bc v) _ _ = v" |
  "ceval (cexp.Eq v) b c = ((aval (V b) c) = v)" |
  "ceval (cexp.Lt v) b c = ((aval (V b) c) < v)" |
  "ceval (cexp.Gt v) b c = ((aval (V b) c) > v)" |
  "ceval (cexp.Not v) b c = (\<not> ceval v b c)" |
  "ceval (And v vb) b c = ((ceval v b c) \<and> (ceval vb b c))"

lemma "ceval (Not (Bc True)) a b = ceval (Bc False) a b"
  by simp

end