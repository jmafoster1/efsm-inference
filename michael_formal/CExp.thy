theory CExp
  imports Syntax
begin

datatype cexp = Bc bool | Eq int | Lt int | Gt int | Not cexp | And cexp cexp

abbreviation Leq :: "int \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

abbreviation Geq :: "int \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

abbreviation Neq :: "int \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> Not (And (Not v) (Not va))"

fun ceval :: "cexp \<Rightarrow> (int \<Rightarrow> bool)" where
  "ceval (Bc b) = (\<lambda>i. b)" |
  "ceval (Eq v) = (\<lambda>i. i = v)" |
  "ceval (Lt v) = (\<lambda>i. i < v)" |
  "ceval (Gt v) = (\<lambda>i. i > v)" |
  "ceval (Not v) = (\<lambda>i. \<not>(ceval v i))" |
  "ceval (And v va) = (\<lambda>i. (ceval v i \<and> ceval va i))"

abbreviation always_false :: "cexp \<Rightarrow> bool" where
  "always_false v \<equiv> (\<forall> i. ceval v i = False)"

abbreviation satisfiable :: "cexp \<Rightarrow> bool" where
  "satisfiable v \<equiv> (\<exists> i. ceval v i = True)"

lemma "ceval (Bc True) = ceval (Not (Bc False))"
  by simp

lemma "ceval (Bc False) = ceval (Not (Bc True))"
  by simp

lemma "\<forall> i. (ceval (And (Eq 1) (Gt 2))) i = False"
  by simp

lemma "ceval (Not (Not v)) = ceval v"
  by simp
end