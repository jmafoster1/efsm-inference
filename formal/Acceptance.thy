theory Acceptance
imports Expressions
begin

definition acceptance_space :: "BExp \<Rightarrow> (nat \<Rightarrow> nil_or_int set) * (nat \<Rightarrow> nil_or_int set)" where
"acceptance_space e \<equiv> 
  ((\<lambda> n . {x . (\<exists>d . \<exists>i . beval d (i \<circ> (n,x)) e)}),
   (\<lambda> n . {x . (\<exists>d . \<exists>i . beval (d \<circ> (n,x)) i e)}))"

definition subsumes :: "BExp \<Rightarrow> BExp \<Rightarrow> bool" (infix "\<sqsubseteq>" 80) where
"b1 \<sqsubseteq> b2 \<equiv>
  let (i1,d1) = acceptance_space b1 in
  let (i2,d2) = acceptance_space b2 in
    (\<forall>i . i1(i) \<subseteq> i2(i))
    \<and>
    (\<forall>d . d1(d) \<subseteq> d2(d))"

lemma subsumes_top: "x \<sqsubseteq> T"
  by (simp only: subsumes_def) (simp add: acceptance_space_def)

lemma subsumes_reflex: "x \<sqsubseteq> x"
  by (simp only: subsumes_def) (simp add: acceptance_space_def)

lemma subsumes_trans: "((x \<sqsubseteq> y) \<and> (y \<sqsubseteq> z)) \<longrightarrow> x \<sqsubseteq> z"
  by (simp add: Collect_mono_iff acceptance_space_def subsumes_def)

lemma test: "(Conj (Lt (Reg 1) (Lit 5)) (Gt (Reg 1) (Lit 1))) \<sqsubseteq> (Conj (Lt (Reg 1) (Lit 7)) (Gt (Reg 1) (Lit 1)))"
  apply (simp only: subsumes_def)
  apply (simp only: acceptance_space_def)
  apply (simp add: beval_def)
  by (smt Collect_mono_iff perhaps_true.elims(2) perhaps_true.simps(3))

end
