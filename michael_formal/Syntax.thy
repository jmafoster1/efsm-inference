theory Syntax
imports AExp Types
begin

(* notation (output) *)
  (* Eq  (infix "=" 50) and *)
  (* Lt (infix "<" 60) and *)
  (* Gt (infix ">" 60) *)

definition ge_infix :: "vname \<Rightarrow> aexp \<Rightarrow> gexp" (infix "\<ge>" 60) where
  "ge_infix a b  = Not (Lt a b)"
declare ge_infix_def [simp]

definition le_infix :: "vname \<Rightarrow> aexp \<Rightarrow> gexp" (infix "\<le>" 60) where
  "le_infix a b  = Not (Gt a b)"
declare le_infix_def [simp]

definition ne_infix :: "vname \<Rightarrow> aexp \<Rightarrow> gexp" (infix "\<noteq>" 100) where
  "ne_infix a b = Not (Eq a b)"
declare ne_infix_def [simp]

end