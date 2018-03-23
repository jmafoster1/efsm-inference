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

definition true :: guard  where
  "true = [(Bc True)]"
declare true_def [simp]

end