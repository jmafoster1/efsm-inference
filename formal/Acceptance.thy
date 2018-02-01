theory Acceptance
imports Expressions
begin

definition acceptance_space :: "BExp \<Rightarrow> (nat \<Rightarrow> nil_or_int) set * (nat \<Rightarrow> nil_or_int) set" where
"acceptance_space e \<equiv> 
  ({I . (\<exists>d . beval d I e)},
   {R . (\<exists>i . beval R i e)})"

definition subsumes :: "BExp \<Rightarrow> BExp \<Rightarrow> bool" (infix "\<sqsubseteq>" 80) where
"e1 \<sqsubseteq> e2 \<equiv>
  let (i1,d1) = acceptance_space e1 in
  let (i2,d2) = acceptance_space e2 in
    i1 \<subseteq> i2
    \<and>
    d1 \<subseteq> d2
    \<and> 
    satisfiable (Conj e1 e2)"

definition anti_subsumes :: "BExp \<Rightarrow> BExp \<Rightarrow> bool" (infix "\<sqsupseteq>" 80) where
"e1 \<sqsupseteq> e2 \<equiv> e2 \<sqsubseteq> e1"

lemma subsumes_top [simp]: 
  fixes x
  assumes "satisfiable x"
  shows "x \<sqsubseteq> T"
  using acceptance_space_def assms satisfiable_def subsumes_def by auto
  
lemma subsumes_reflex [simp]: 
  fixes x
  assumes "satisfiable x"
  shows "x \<sqsubseteq> x"
  using assms satisfiable_def subsumes_def by auto

lemma subsumes_bottom [simp]: 
  fixes x
  assumes "satisfiable x"
  shows "x \<sqsubseteq> F \<longleftrightarrow> x = F"
  using assms satisfiable_def subsumes_def by auto

lemma subsumes_trans: 
  fixes x
  fixes y
  fixes z
  assumes "satisfiable x"
  assumes "satisfiable y"
  assumes "satisfiable z"
  shows "((x \<sqsubseteq> y) \<and> (y \<sqsubseteq> z)) \<longrightarrow> x \<sqsubseteq> z"
proof -
  show ?thesis
    apply (simp only: subsumes_def)
    apply (simp only: acceptance_space_def)
    apply simp



lemma subsumes_antisym: "x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longleftrightarrow> x = y"
  apply (induct_tac x)
           apply (induct_tac y)
  apply simp+

    apply (simp only: subsumes_def)
  apply (simp add: acceptance_space_def)
  apply (case_tac x)
           apply (case_tac y)

                    apply simp+
  
(*
  apply (induct_tac x)
           apply (induct_tac y)
*)

lemma test: "(Conj (Lt (Reg 1) (Lit 5)) (Gt (Reg 1) (Lit 1))) \<sqsubseteq> (Conj (Lt (Reg 1) (Lit 7)) (Gt (Reg 1) (Lit 1)))"
  apply (simp only: subsumes_def)
  apply (simp only: acceptance_space_def)
  apply (simp add: beval_def)
  by (smt Collect_mono_iff perhaps_true.elims(2) perhaps_true.simps(3))

lemma test2: "Eq (Input 1) (Lit 1) \<sqsubseteq> Eq (Input 1) (Input 2) "
  apply (simp only: subsumes_def)
  apply (simp only: acceptance_space_def)
  apply (simp add: beval_def)
  apply (rule_tac x="Suc 0" in exI)

  apply (rule perhaps_true.elims)
  

end
