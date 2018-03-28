theory Syntax
imports "~~/src/HOL/IMP/Hoare" types
begin

definition Geq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" (infix "\<ge>" 60) where
  "Geq a b  = (Not (Less a b))"
declare Geq_def [simp]

definition Gt :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" (infix ">" 60) where
  "Gt a b = (Less b a)"
declare Gt_def [simp]

definition Leq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" (infix "\<le>" 60) where
  "Leq a b = (Not (Gt a b))"
declare Leq_def [simp]

definition and_infix :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" (infix "\<and>" 60) where
  "and_infix a b = And a b"
declare and_infix_def [simp]

definition eq_infix :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" (infix "=" 100) where
  "eq_infix a b = And (Not (Less a b)) (Not (Less b a))"
declare eq_infix_def [simp]

definition plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" (infix "+" 65) where
  "plus a b = Plus a b"
declare plus_def [simp]

definition true :: guard  where
  "true = [(Bc True)]"
declare true_def [simp]

end