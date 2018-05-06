theory CExp
  imports Main
begin

datatype cexp = Undef | Bc bool | Eq int | Lt int | Gt int | Nand cexp cexp

abbreviation Not :: "cexp \<Rightarrow> cexp" where
  "Not c \<equiv> Nand c c"

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
  "Or v va \<equiv> Nand (Nand v v) (Nand va va)"

abbreviation And :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "And v va \<equiv> Nand (Nand v va) (Nand v va)"

(* Does a given value of "i" satisfy the given cexp? *)
fun ceval :: "cexp \<Rightarrow> (int \<Rightarrow> bool)" where
  "ceval Undef = (\<lambda>i. False)" |
  "ceval (Bc b) = (\<lambda>i. b)" |
  "ceval (Eq v) = (\<lambda>i. i = v)" |
  "ceval (Lt v) = (\<lambda>i. i < v)" |
  "ceval (Gt v) = (\<lambda>i. i > v)" |
  "ceval (Nand v va) = (\<lambda>i. \<not> (ceval v i \<and> ceval va i))"

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
  "and x y = (case x of
    Bc True \<Rightarrow> y |
    Undef \<Rightarrow> Undef |
    Bc False \<Rightarrow> Bc False |
    Eq i \<Rightarrow> (case y of 
      Eq i' \<Rightarrow> (if i = i' then Eq i else Bc False) |
      _ \<Rightarrow> And x y
    ) |
    _ \<Rightarrow> (case y of
      Bc True \<Rightarrow> x |
      Undef \<Rightarrow> Undef |
      Bc False \<Rightarrow> Bc False |
      _ \<Rightarrow> And x y
    )
  )"

theorem and_is_And:  "ceval (and x y) = ceval (And x y)"
proof (cases "x")
  case (Bc x1)
  then show ?thesis
    apply (case_tac "x1 = True")
    by simp_all
next
  case (Eq x2)
  then show ?thesis
    apply simp
    apply (cases "y")
    by simp_all
next
  case (Lt x3)
  then show ?thesis
    apply simp
    apply (cases "y")
         apply simp_all
    apply (cases "y = Bc True")
    by simp_all
next
  case (Gt x4)
  then show ?thesis
    apply simp
    apply (cases "y")
         apply simp_all
    apply (cases "y = Bc True")
    by simp_all
next
  case (Nand x61 x62)
  then show ?thesis
    apply simp
    apply (cases "y")
         apply simp_all
    apply (cases "y = Bc True")
    by simp_all
next case (Undef)
  then show ?thesis by simp
qed
declare and_is_And [simp]

fun "not" :: "cexp \<Rightarrow> cexp" where
  "not c = (case c of
    Bc True \<Rightarrow> Bc False |
    Bc False \<Rightarrow> Bc True |
    Undef \<Rightarrow> Bc True |
    c \<Rightarrow> Not c
  )"

theorem not_is_Not: "ceval (not x) = ceval (Not x)"
  proof (cases "x")
  case (Bc x1)
  then show ?thesis
    apply (case_tac "x1 = True")
    by simp_all
  next
  case (Eq x2)
  then show ?thesis by simp_all
  next
  case (Lt x3)
  then show ?thesis by simp_all
  next
  case (Gt x4)
  then show ?thesis by simp_all
  next
  case (Nand x61 x62)
  then show ?thesis by simp
next
  case (Undef)
  then show ?thesis by simp
qed
declare not_is_Not [simp]

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

lemma everything_simulates_false: "\<forall>c. cexp_simulates c (Bc False)"
  by simp

lemma "cexp_simulates (Bc False) a \<Longrightarrow> cexp_equiv a (Bc False)"
  by simp

lemma "cexp_simulates (Lt 10) (Lt 5)"
  by simp

lemma simulates_symmetry: "cexp_simulates x x"
  by simp

fun apply_gt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_gt Undef a = (Undef, a)" |
  "apply_gt a Undef = (a, Undef)" |
  "apply_gt (Bc False) a = (Bc False, a)" |
  "apply_gt a (Bc False) = (a, Bc False)" |
  "apply_gt (Bc True) (Bc True) = (Bc True, Bc True)" |
  "apply_gt (Bc True) (Eq v) = (Gt v, Eq v)" |
  "apply_gt (Bc True) (Lt va) = (Bc True, Lt va)" |
  "apply_gt (Bc True) (Gt va) = (Gt va, Gt va)"

(* Can we restrict the second argument to be greater than the first? *)
fun make_gt :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "make_gt Undef _ = Undef" |
  "make_gt _ Undef = Undef" |
  "make_gt (Bc False) _ = Bc False" |
  "make_gt _ (Bc False) = Bc False" |
  "make_gt v (Nand va vb) = Or (make_gt v va) (make_gt v vb)" |
  "make_gt (Nand va vb) v = Or (make_gt v va) (make_gt v vb)" |
  "make_gt (Bc True) (Bc True) = Bc True" |
  "make_gt (Bc True) (Eq va) = Gt va" |
  "make_gt (Bc True) (Lt va) = Bc True" |
  "make_gt (Bc True) (Gt va) = Gt va" |
  "make_gt (Eq v) (Bc True) = Eq v" |
  "make_gt (Eq v) (Eq va) = and (Eq v) (Gt va)" |
  "make_gt (Eq v) (Lt va) = Eq v" |
  "make_gt (Eq v) (Gt va) = and (Eq v) (Gt va)" |
  "make_gt (Lt v) (Bc True) = Lt v" |
  "make_gt (Lt v) (Eq va) = and (Lt v) (Gt va)" |
  "make_gt (Lt v) (Lt va) = Lt v" |
  "make_gt (Lt v) (Gt va) = and (Lt v) (Gt va)" |
  "make_gt (Gt v) _ = Gt v"

(* Can we restrict the second argument to be greater than the first? *)
fun make_lt :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "make_lt Undef _ = Undef" |
  "make_lt _ Undef = Undef" |
  "make_lt (Bc False) _ = Bc False" |
  "make_lt _ (Bc False) = Bc False" |
  "make_lt v (Nand va vb) = Or (make_lt v va) (make_lt v vb)" |
  "make_lt (Nand va vb) v = Or (make_lt v va) (make_lt v vb)" |
  "make_lt (Bc True) (Bc True) = Bc True" |
  "make_lt (Bc True) (Eq va) = Lt va" |
  "make_lt (Bc True) (Lt va) = Lt va" |
  "make_lt (Bc True) (Gt va) = Bc True" |
  "make_lt (Eq v) (Bc True) = Eq v" |
  "make_lt (Eq v) (Eq va) = and (Eq v) (Lt va)" |
  "make_lt (Eq v) (Lt va) = and (Eq v) (Lt va)" |
  "make_lt (Eq v) (Gt va) = Eq v" |
  "make_lt (Lt v) _ = Lt v" |
  "make_lt (Gt v) (Bc True) = Gt v" |
  "make_lt (Gt v) (Eq va) = and (Gt v) (Lt va)" |
  "make_lt (Gt v) (Lt va) = and (Gt v) (Lt va)" |
  "make_lt (Gt v) (Gt va) = Gt v"

fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_plus Undef _ = Undef" |
  "compose_plus _ Undef = Undef" |
  "compose_plus (Bc False) _ = Bc False" |
  "compose_plus _ (Bc False) = Bc False" |
  "compose_plus (Bc True) _ = Bc True" |
  "compose_plus _ (Bc True) = Bc True" |
  "compose_plus v (Nand va vb) = Nand (compose_plus v va) (compose_plus v vb)" |
  "compose_plus (Nand va vb) v = Nand (compose_plus v va) (compose_plus v vb)" |
  "compose_plus (Eq v) (Eq va) = Eq (v+va)" |
  "compose_plus (Eq v) (Lt va) = Lt (v+va)" |
  "compose_plus (Eq v) (Gt va) = Gt (v+va)" |
  "compose_plus (Lt v) (Eq va) = Lt (v+va)" |
  "compose_plus (Lt v) (Lt va) = Lt (v+va)" |
  "compose_plus (Lt v) (Gt va) = Bc True" |
  "compose_plus (Gt v) (Eq va) = Gt (v+va)" |
  "compose_plus (Gt v) (Lt va) = Bc True" |
  "compose_plus (Gt v) (Gt va) = Gt (v+va)"

fun compose_minus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_minus Undef _ = Undef" |
  "compose_minus _ Undef = Undef" |
  "compose_minus (Bc False) _ = Bc False" |
  "compose_minus _ (Bc False) = Bc False" |
  "compose_minus (Bc True) _ = Bc True" |
  "compose_minus _ (Bc True) = Bc True" |
  "compose_minus v (Nand va vb) = Nand (compose_minus v va) (compose_minus v vb)" |
  "compose_minus (Nand va vb) v = Nand (compose_minus v va) (compose_minus v vb)" |
  "compose_minus (Eq v) (Eq va) = Eq (v-va)" |
  "compose_minus (Eq v) (Lt va) = Gt (v-va)" |
  "compose_minus (Eq v) (Gt va) = Lt (v-va)" |
  "compose_minus (Lt v) (Eq va) = Lt (v-va)" |
  "compose_minus (Lt v) (Lt va) = Bc True" |
  "compose_minus (Lt v) (Gt va) = Lt (v-va)" |
  "compose_minus (Gt v) (Eq va) = Gt (v-va)" |
  "compose_minus (Gt v) (Lt va) = Gt (v-va)" |
  "compose_minus (Gt v) (Gt va) = Bc True"
end