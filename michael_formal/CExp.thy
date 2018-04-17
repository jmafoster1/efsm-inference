theory CExp
  imports Syntax
begin

datatype cexp = Bc bool | Eq int | Lt int | Gt int | Not cexp | And cexp cexp

(* Less than or equal to *)
abbreviation Leq :: "int \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

(* Greater than or equal to *)
abbreviation Geq :: "int \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

(* Not equal to *)
abbreviation Neq :: "int \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

(* Logical Or in terms of And and Not*)
abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> Not (And (Not v) (Not va))"

(* Does a given value of "i" satisfy the given cexp? *)
fun ceval :: "cexp \<Rightarrow> (int \<Rightarrow> bool)" where
  "ceval (Bc b) = (\<lambda>i. b)" |
  "ceval (Eq v) = (\<lambda>i. i = v)" |
  "ceval (Lt v) = (\<lambda>i. i < v)" |
  "ceval (Gt v) = (\<lambda>i. i > v)" |
  "ceval (Not v) = (\<lambda>i. \<not>(ceval v i))" |
  "ceval (And v va) = (\<lambda>i. (ceval v i \<and> ceval va i))"

(* Are cexps "c" and "c'" satisfied under the same conditions? *)
abbreviation cexp_equiv :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_equiv c c' \<equiv> (\<forall>i. (ceval c i) = (ceval c' i))"

(* Is cexp "c" satisfied under all "i" values? *)
abbreviation valid :: "cexp \<Rightarrow> bool" where
  "valid c \<equiv> (\<forall> i. ceval c i)"

(* Is there some value of "i" which satisfies "c"? *)
abbreviation satisfiable :: "cexp \<Rightarrow> bool" where
  "satisfiable v \<equiv> (\<exists>i. ceval v i)"

(* Does cexp "c" simulate "c'"? *)
abbreviation cexp_simulates :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_simulates c c' \<equiv> (\<forall>i. ceval c' i \<longrightarrow> ceval c i)"

fun "and" :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "and (Bc True) c = c" |
  "and c (Bc True) = c" |
  "and (Bc False) _ = Bc False" |
  "and _ (Bc False) = Bc False" |
  "and (Eq i) (Eq i') = (if i = i' then Eq i else Bc False)" |
  "and c c' = And c c'"

lemma "ceval (Bc True) = ceval (Not (Bc False))"
  by simp

lemma "ceval (Bc False) = ceval (Not (Bc True))"
  by simp

lemma "\<forall> i. (ceval (And (Eq 1) (Gt 2))) i = False"
  by simp

lemma "ceval (Not (Not v)) = ceval v"
  by simp

lemma "cexp_simulates (Bc True) a"
  by simp

lemma "cexp_simulates (Bc False) a \<Longrightarrow> cexp_equiv a (Bc False)"
  by simp

lemma "cexp_simulates (Lt 10) (Lt 5)"
  by simp

lemma simulates_symmetry: "cexp_simulates x x"
  by simp 
end