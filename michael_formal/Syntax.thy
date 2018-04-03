theory Syntax
imports "~~/src/HOL/IMP/Hoare" Types
begin

definition ge_infix :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (infix "\<ge>" 60) where
  "ge_infix a b  = Not (Lt a b)"
declare ge_infix_def [simp]

definition gt_infix :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (infix ">" 60) where
  "gt_infix a b = Gt a b"
declare gt_infix_def [simp]

definition le_infix :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (infix "\<le>" 60) where
  "le_infix a b  = Not (Gt a b)"
declare le_infix_def [simp]

definition lt_infix :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (infix "<" 60) where
  "lt_infix a b = Lt a b"
declare lt_infix_def [simp]

definition eq_infix :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (infix "=" 100) where
  "eq_infix a b = Eq a b"
declare eq_infix_def [simp]

definition ne_infix :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (infix "\<noteq>" 100) where
  "ne_infix a b = Not (Eq a b)"
declare ne_infix_def [simp]

end