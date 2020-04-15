theory Increment_Reset_Subsumption
imports "EFSM.Contexts"
begin

declare One_nat_def [simp del]
declare gval.simps [simp]
declare value_eq_def [simp]

lemma satisfies_context_eq_contra: "c (V v) = {|cexp.Eq x|} \<Longrightarrow>
       r v \<noteq> Some x \<Longrightarrow>
       \<not> satisfies_context r c"
  apply (simp add: satisfies_context_def consistent_def datastate2context_def)
  apply clarify
  apply (rule_tac x="(V v)" in exI)
  apply (simp add: cval_def)
  apply (case_tac "r v")
  by auto
(*
lemma satisfies_context_eq: "c (V v) = {|cexp.Eq x|} \<Longrightarrow>
       satisfies_context r c \<Longrightarrow>
       r v = Some x"
  using satisfies_context_eq_contra
  by auto
*)

primrec updates :: "vname \<Rightarrow> update_function list \<Rightarrow> bool" where
  "updates _ [] = False" |
  "updates v (h#t) = (if fst h = v then True else updates v t)"

lemma same_posterior: "ra \<noteq> V (R r) \<Longrightarrow>
      \<not> updates (R r) (Updates t1) \<Longrightarrow>
      Guard t1 = [gexp.Eq (V (I 1)) (L (Num n))] \<Longrightarrow>
      posterior_separate c [gexp.Eq (V (I 1)) (L (Num n))] ((R r, Plus (V (R r)) (V (I 1))) # Updates t1) ra = posterior c t1 ra"
  apply (simp add: posterior_def posterior_separate_def Let_def)
  apply clarify
  apply (simp add: remove_obsolete_constraints_def)
  by auto
(*
lemma test: "r \<noteq> V (I 1) \<Longrightarrow> medial c [gexp.Eq (V (I 1)) (L (Num n))] r = c r"
  by (simp add: medial_def List.maps_def pairs2context_def cval_def)
*)
lemma not_updates_remains_same: "\<not> updates (R r) u \<Longrightarrow>
    Contexts.apply_updates x c u (V (R r)) = c (V (R r))"
proof(induct u)
  case Nil
  then show ?case by simp
next
  case (Cons a u)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (case_tac "aa = R r")
     apply simp
    apply simp
    apply (case_tac b)
    by auto
qed

lemma aux1: "consistent (medial c [gexp.Eq (V (I 1)) (L (Num n))]) \<Longrightarrow>
       c (V (R r)) = {|cexp.Eq (Num (m - n))|} \<Longrightarrow>
       \<not> updates (R r) (Updates t1) \<Longrightarrow>
       posterior_separate c [gexp.Eq (V (I 1)) (L (Num n))] (Updates t1) (V (R r)) = c (V (R r))"
proof(induct "Updates t1")
  case Nil
  then show ?case
    by (simp add: posterior_separate_def Let_def remove_obsolete_constraints_def)
next
  case (Cons a x)
  then show ?case
    apply (simp add: posterior_separate_def Let_def remove_obsolete_constraints_def)
    apply (case_tac "fBex (fset_of_list (Updates t1)) (\<lambda>x. fst x = R r \<and> R r \<noteq> fst x)")
     apply force
    by (simp add: not_updates_remains_same)
qed

lemma "consistent (medial c [gexp.Eq (V (I 1)) (L (Num n))]) \<Longrightarrow>
      \<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
      c (V (R r)) = {|cexp.Eq (Num (m - n))|} \<Longrightarrow>
      posterior_separate c [gexp.Eq (V (I 1)) (L (Num n))] ((R r, Plus (V (R r)) (V (I 1))) # Updates t1) (V (R r)) = {|Eq (Num m)|}"
  apply (simp add: posterior_separate_def Let_def remove_obsolete_constraints_def)
  apply (simp add: medial_def pairs2context_def List.maps_def)
  apply (simp add: fprod_def)
  oops






end
