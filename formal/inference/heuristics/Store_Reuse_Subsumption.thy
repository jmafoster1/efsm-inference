theory Store_Reuse_Subsumption
imports Store_Reuse
begin

declare One_nat_def [simp del]

lemma medial_general_subset: "medial c (Guard (remove_guard_add_update t i r)) ra |\<subseteq>| medial c (Guard t) ra"
  by (simp add: remove_guard_add_update_def medial_filter)

lemma consistent_medial_generalisation: "consistent (medial c (Guard t)) \<Longrightarrow>
                                         consistent (medial c (Guard (remove_guard_add_update t i r)))"
  apply (simp add: consistent_def)
  using medial_general_subset
  by blast

lemma get_medial_filter: "Contexts.get (medial c (filter f G)) x31 |\<subseteq>| Contexts.get (medial c G) x31"
  apply (case_tac x31)
     apply simp
    apply (simp add: medial_filter)
   apply (simp add: le_supI2 medial_filter sup.coboundedI1)
  by (simp add: medial_filter)

lemma fprod_get_medial_filter: "(a, b) |\<in>| Contexts.get (medial c (filter f G)) r |\<times>| Contexts.get (medial c (filter f G)) x32 \<Longrightarrow>
                                (a, b) |\<in>| Contexts.get (medial c G) r |\<times>| Contexts.get (medial c G) x32"
  using get_medial_filter
  by (meson fin_mono fprod_subset)

lemma apply_updates_filter: "Contexts.apply_updates (medial c (filter f G)) c U ra |\<subseteq>| Contexts.apply_updates (medial c G) c U ra"
proof(induct U)
  case Nil
  then show ?case
    by simp
next
  case (Cons a U)
  then show ?case
    apply (cases a)
    apply (case_tac b)
       apply simp
      apply (simp add: medial_filter)
     apply simp
     apply clarify
     apply simp
    using fprod_get_medial_filter fimage_fprod apply metis
     apply simp
     apply clarify
     apply simp
    using fprod_get_medial_filter fimage_fprod by metis
qed

lemma guard2pairs_no_constraints_on_v: "\<not> gexp_constrains g1 (V v) \<Longrightarrow> list_all (\<lambda>(a, c). a \<noteq> V v) (guard2pairs c g1)"
proof(induct g1)
case (Bc x)
  then show ?case
    apply (case_tac x)
    by auto
next
  case (Eq a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (V x)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (Plus a11 a12)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (Minus a11 a12)
    then show ?case
      apply (induct a2)
      by auto
  qed
next
  case (Gt a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      by auto
  next
    case (V x)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (Plus a11 a12)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (Minus a11 a12)
    then show ?case
      apply (induct a2)
      by auto
  qed
next
  case (Null x)
  then show ?case
    by auto
next
case (Nor g11 g12)
  then show ?case
    apply simp
    by (metis (mono_tags, lifting) Ball_set list.pred_map o_apply prod.sel(1) split_def)
qed

lemma pairs2context_no_constraints_on_v: "list_all (\<lambda>(a, c). a \<noteq> V v) l \<Longrightarrow> pairs2context l (V v) = {||}"
proof-
  assume premise: "list_all (\<lambda>(a, c). a \<noteq> V v) l"
  have list_all_empty: "filter (\<lambda>(a, uu). a = V v) l = []"
    using premise
    by (simp add: Ball_set split_def)
  show ?thesis
    by (simp add: pairs2context_def list_all_empty)
qed

lemma pairs2context_no_constraints_on_v_2: "\<not> gexp_constrains g1 (V v) \<Longrightarrow> pairs2context (map (\<lambda>(x, y). (x, not |`| y)) (guard2pairs c g1)) (V v) = {||}"
  using guard2pairs_no_constraints_on_v pairs2context_no_constraints_on_v
  by (metis funion_absorb gexp_constrains.simps(5) guard2pairs.simps(30) map_append pairs2context_append)

lemma generalisation_of_preserves: "is_generalisation_of t' t i r \<Longrightarrow>
    Label t = Label t' \<and>
    Arity t = Arity t' \<and>
    (Outputs t) = (Outputs t')"
  apply (simp add: is_generalisation_of_def)
  using remove_guard_add_update_preserves by auto

lemma generalisation_medial_subset: "is_generalisation_of t' t i r \<Longrightarrow> medial c (Guard t') a |\<subseteq>| medial c (Guard t) a"
  apply (simp add: is_generalisation_of_def)
  using medial_general_subset by blast

lemma generalisation_medial_equiv: "is_generalisation_of t' t i r \<Longrightarrow> medial c (Guard t @ Guard t') = medial c (Guard t)"
  apply (rule ext)
  apply (simp add: is_generalisation_of_def medial_append)
  using medial_general_subset by blast

lemma apply_updates_same: "\<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set U. fst u \<noteq> v \<and> fst u \<noteq> I i \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       remove_obsolete_constraints (Contexts.apply_updates (medial c (Guard t)) c U) (fst |`| fset_of_list U) (V v) = c (V v)"
proof(induct U)
  case Nil
  then show ?case
    apply (simp add: remove_obsolete_constraints_def)
    by auto
next
  case (Cons u us)
  then show ?case
    apply (cases u)
    apply (simp add: remove_obsolete_constraints_def)
    apply (case_tac v)
     apply simp
    apply simp
    apply clarify
    apply standard
     apply (metis (no_types, lifting) empty_variable_constraints)
    apply (case_tac b)
       apply simp
       apply (smt fBexE)
      apply simp
      apply (smt fBexE)
     apply simp
     apply (smt fBexE)
    apply simp
    by (smt fBexE)
qed

lemma posterior_same: "\<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set (Updates t). fst u \<noteq> v \<and> fst u \<noteq> I i \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       posterior c t (V v) = c (V v)"
  by (simp add: posterior_def posterior_separate_def apply_updates_same)

lemma is_generalisation_of_consistent_medial: "is_generalisation_of t' t i r \<Longrightarrow>
    consistent (medial c (Guard t)) \<Longrightarrow> 
    consistent (medial c (Guard t'))"
  by (simp add: is_generalisation_of_def consistent_medial_generalisation)

lemma is_generalisation_of_posterior_subset: "is_generalisation_of t' t i r \<Longrightarrow> a \<noteq> V (R r) \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       posterior c t' a |\<subseteq>| posterior c t a"
  apply (simp add: posterior_def posterior_separate_def)
  apply (simp add: Let_def generalisation_medial_equiv)
   apply (simp add: is_generalisation_of_consistent_medial)
   apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
   apply (simp add: remove_obsolete_constraints_def)
   apply standard
    apply auto[1]
  by (simp add: apply_updates_filter)

lemma posterior_Rr_undef: "\<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       c (V (R r)) = {|Undef|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set (Updates t). fst u \<noteq> R r \<and> fst u \<noteq> I i \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       posterior c t (V (R r)) = {|Undef|}"
  by (simp add: posterior_same)

lemma aux2: "is_generalisation_of t' t i r \<Longrightarrow>
       c (V (R r)) = {|Undef|} \<Longrightarrow>
       \<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set (Updates t). fst u \<noteq> R r \<and> fst u \<noteq> I i \<Longrightarrow>
       fBall (Contexts.apply_updates (medial c (Guard t)) c (Updates t') ra) (\<lambda>c. cval c ra ia = true) \<Longrightarrow>
       Contexts.apply_updates (medial c (Guard t)) c (Updates t) ra \<noteq> {|Undef|} \<Longrightarrow>
       x |\<in>| Contexts.apply_updates (medial c (Guard t)) c (Updates t) ra \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow> ra \<noteq> V (R r) \<Longrightarrow> \<forall>n. \<not> aexp_constrains ra (V (I n)) \<Longrightarrow> cval x ra ia = true"
proof(induct "Updates t")
case Nil
  then show ?case
    apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
    by auto
next
  case (Cons u us)
  then show ?case
    apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
    by auto
qed

lemma generalised_updates:  "is_generalisation_of t' t i r \<Longrightarrow> Updates t' = (R r, (V (I i)))#(Updates t)"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma aux3: "\<not> gexp_constrains a (V v) \<Longrightarrow> pairs2context (guard2pairs c a) (V v) |\<subseteq>| c (V v)"
proof(induct a)
case (Bc x)
  then show ?case
    apply (case_tac x)
     apply (simp add: pairs2context_def)
    by(simp add: pairs2context_def)
next
  case (Eq a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (V x)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (Plus a11 a12)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (Minus a11 a12)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  qed
next
  case (Gt a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (V x)
    then show ?case
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (Plus a11 a12)
    then show ?case 
      apply (induct a2)
      using pairs2context_def
      by auto
  next
    case (Minus a11 a12)
    then show ?case 
      apply (induct a2)
      using pairs2context_def
      by auto
  qed
next
  case (Nor a1 a2)
  then show ?case
    apply (simp add: pairs2context_append)
    apply standard
     apply (simp add: pairs2context_no_constraints_on_v_2)
    by (simp add: pairs2context_no_constraints_on_v_2)
next
  case (Null x)
  then show ?case
    apply (simp add: pairs2context_def)
    by auto
qed

lemma medial_filter_constraints: "medial c (filter (\<lambda>g. \<not> gexp_constrains g (V (I i))) G) (V (I i)) = c (V (I i))"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: medial_def pairs2context_def List.maps_def)
next
  case (Cons a G)
  then show ?case
    apply (simp add: medial_def List.maps_simps pairs2context_append)
    apply standard
    apply standard
     prefer 2
     apply blast
    apply simp
    apply standard
    defer
     apply auto[1]
    by (simp add: aux3)
qed

lemma generealisation_medial: "is_generalisation_of t' t i r \<Longrightarrow>
       medial c (Guard t') (V (I i)) = c (V (I i))"
  apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
  by (simp add: medial_filter_constraints)

lemma generalisation_posterior_consistent: "is_generalisation_of t' t i r \<Longrightarrow>
       c (V (R r)) = {|Undef|} \<Longrightarrow>
       \<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       \<forall>i. \<forall>u\<in>set (Updates t). fst u \<noteq> R r \<and> fst u \<noteq> I i \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       fBall (posterior c t a) (\<lambda>c. cval c a s = true) \<Longrightarrow>
       fBall (posterior c t' a) (\<lambda>c. cval c a s = true)"
  apply (case_tac "a \<noteq> V (R r)")
  using is_generalisation_of_posterior_subset apply blast
  apply (simp add: posterior_def posterior_separate_def Let_def is_generalisation_of_consistent_medial)
  apply (simp add: generalised_updates remove_obsolete_constraints_def)
  apply (case_tac "fBex (fset_of_list (Updates t)) (\<lambda>x. fst x = R r \<and> R r \<noteq> fst x)")
   apply auto[1]
  apply simp
  apply standard
   apply auto[1]
  apply clarify
  by (simp add: generealisation_medial cval_true)

(*
  This shows that if we drop the guard and add an update, and the updated register is undefined
  in the context, c, then the generalised transition subsumes the specific one
*)
lemma is_generalisation_of_subsumes_original: "is_generalisation_of t' t i r \<Longrightarrow>
                                               c (V (R r)) = {|Undef|} \<Longrightarrow>
                                               \<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
                                               \<forall>i. \<forall>u \<in> set (Updates t). fst u \<noteq> (R r) \<and> fst u \<noteq> (I i) \<Longrightarrow>
                                               t' \<^sub>c\<sqsupseteq> t"
    apply (rule subsumption)
       apply (simp add: generalisation_of_preserves)
  using generalisation_medial_subset apply blast
     apply (simp add: generalisation_of_preserves)
    apply (simp add: generalisation_of_preserves)
   apply clarify
   apply (case_tac "consistent (medial c (Guard t))")
    prefer 2
    apply (simp add: posterior_def posterior_separate_def Let_def generalisation_medial_equiv)

   apply (case_tac "ra = V (R r)")
    apply clarify
    apply (simp add: posterior_Rr_undef)
   apply (simp add: posterior_separate_def posterior_def Let_def generalisation_medial_equiv remove_obsolete_constraints_def)
   apply (case_tac "(\<exists>n. aexp_constrains ra (V (I n)))")
    apply auto[1]
   apply (case_tac "fBex (fset_of_list (Updates t')) (\<lambda>x. V (fst x) = ra \<and> ra \<noteq> V (fst x))")
    apply auto[1]
   apply (case_tac "fBex (fset_of_list (Updates t)) (\<lambda>x. V (fst x) = ra \<and> ra \<noteq> V (fst x))")
    apply auto[1]
   apply simp
   apply (simp add: aux2)

  apply (simp only: consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)

  apply (case_tac "consistent (medial c (Guard t))")
   apply (simp add: generalisation_posterior_consistent)

  apply (simp add: posterior_def posterior_separate_def Let_def)
  apply clarify
  by (simp add: cval_false)

lemma restrict_value_of_register: "c (V (R r)) = {|cexp.Eq v|} \<Longrightarrow>
       consistent (\<lambda>x. datastate2context ra x |\<union>| c x) \<Longrightarrow>
       ra (R r) = Some v"
proof-
  assume premise1: "c (V (R r)) = {|cexp.Eq v|}"
  assume premise2: "consistent (\<lambda>x. datastate2context ra x |\<union>| c x)"
  have contra: "\<And>c r v ra. c (V (R r)) = {|cexp.Eq v|} \<Longrightarrow>
       ra (R r) \<noteq> Some v \<Longrightarrow>
       \<not> consistent (\<lambda>x. datastate2context ra x |\<union>| c x)"
  apply (simp add: datastate2context_def consistent_def)
  apply clarify
  apply (rule_tac x="V (R r)" in exI)
  apply simp
  apply (simp add: cval_def gval.simps ValueEq_def)
  apply (case_tac "ra (R r)")
   apply (simp add: gval.simps ValueEq_def)
    by (simp add: gval.simps ValueEq_def)
  show ?thesis
    using contra premise1 premise2
    by auto
qed

lemma length_apply_generalised_outputs: "length (apply_outputs (Outputs t)                         (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. ra (R n)))) =
                                         length (apply_outputs (Outputs (generalise_output t p r)) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. ra (R n))))"
  by (simp add: apply_outputs_alt generalise_output_preserves_output_length)

lemma apply_outputs_equiv: "i < length (Outputs t) \<Longrightarrow>
       i \<noteq> r \<Longrightarrow>
       (apply_outputs (Outputs t) s) ! i = (apply_outputs (Outputs (generalise_output t p r)) s) ! i"
  apply (simp add: generalise_output_def)
  by (simp add: apply_outputs_alt)

(* 
  This shows that if we can guarantee that the value of a particular register is the literal output
  then the generalised output subsumes the specific output
*)

lemma generalise_output_subsumes_original: "nth (Outputs t) r = L v \<Longrightarrow>
                                            c (V (R p)) = {|Eq v|} \<Longrightarrow>
                                            generalise_output t p r \<^sub>c\<sqsupseteq> t"
  apply (simp add: subsumes_def generalise_output_preserves)
  apply standard
   apply (simp add: satisfies_context_def)
   apply clarify
   apply (simp add: list_eq_iff_nth_eq length_apply_generalised_outputs )
   apply clarify
   apply (simp only: apply_outputs_preserves_length)
   apply (case_tac "ia = r")
    prefer 2
    apply (simp add: apply_outputs_equiv)
   apply (simp add: apply_outputs_alt generalise_output_def)
   apply (simp add: restrict_value_of_register)
  apply standard
   apply (simp add: list_eq_iff_nth_eq length_apply_generalised_outputs apply_outputs_alt generalise_output_def)
   apply (rule_tac x=i in exI)
   apply (rule_tac x="<R p := v>" in exI)
   apply (rule allI)
   apply (case_tac "ia = r")
    apply simp
   apply simp
  apply standard
  apply (rule allI)+
   apply (simp add: posterior_separate_append_self posterior_def generalise_output_preserves)
  by (simp add: posterior_def posterior_separate_def  generalise_output_preserves)

primrec stored_reused_aux_per_reg :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused_aux_per_reg t' t 0 p = (if is_generalised_output_of t' t 0 p then Some (0, p) else None)" |
  "stored_reused_aux_per_reg t' t (Suc r) p = (if is_generalised_output_of t' t (Suc r) p then Some (Suc r, p) else stored_reused_aux_per_reg t' t r p)"

primrec stored_reused_aux :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused_aux t' t r 0 = stored_reused_aux_per_reg t' t r 0" |
  "stored_reused_aux t' t r (Suc p) = (case stored_reused_aux_per_reg t' t r (Suc p) of
                                          Some x \<Rightarrow> Some x |
                                          None \<Rightarrow> stored_reused_aux t' t r p
                                        )"

definition stored_reused :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused t' t e = stored_reused_aux t' t (max_reg e) (max_output e)"

(*
    This shows that we can use the model checker to test whether the relevant register is the correct
    value for direct subsumption 
*)
lemma generalise_output_directly_subsumes_original: 
      "stored_reused t' t e = Some (p, r) \<Longrightarrow>
       is_generalised_output_of t' t p r \<Longrightarrow> 
       nth (Outputs t) r = L v \<Longrightarrow>
       \<forall>t. accepts_trace (tm e) t \<and> gets_us_to s' (tm e) 0 <>  t \<longrightarrow> (anterior_context (tm e) t) (V (R p)) = {|Eq v|} \<Longrightarrow>
       directly_subsumes e1 e s s' t' t "
  apply (simp add: is_generalised_output_of_def directly_subsumes_def)
  using generalise_output_subsumes_original[of t r v _ p]
  by metis

definition generalise_output_context_check :: "iEFSM \<Rightarrow> nat \<Rightarrow> value \<Rightarrow> nat \<Rightarrow> bool" where
  "generalise_output_context_check e p v s = (\<forall>t. accepts_trace (tm e) t \<and> gets_us_to s (tm e) 0 <>  t \<longrightarrow> (anterior_context (tm e) t) (V (R p)) = {|Eq v|})"

fun generalise_output_direct_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> bool" where
  "generalise_output_direct_subsumption t' t e s' = (case stored_reused t' t e of
    None \<Rightarrow> False |
    Some (p, r) \<Rightarrow> (if is_generalised_output_of t' t p r then
      case nth (Outputs t) r of
        L v \<Rightarrow> generalise_output_context_check e p v s' |
        _ \<Rightarrow> False
      else False)
  )"

(* This allows us to just run the two functions for quick subsumption *)
lemma generalise_output_directly_subsumes_original_executable: 
      "generalise_output_direct_subsumption t' t e s' \<Longrightarrow> directly_subsumes e1 e s s' t' t"
  apply simp
  apply (case_tac "stored_reused t' t e")
   apply simp
  apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac "is_generalised_output_of t' t aa b")
   defer
   apply simp
  apply simp
  apply (case_tac "Outputs t ! b")
     defer
     apply simp+
  by (simp add: generalise_output_context_check_def generalise_output_directly_subsumes_original)

primrec input_i_stored_in_reg :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "input_i_stored_in_reg t' t i 0 = (if is_generalisation_of t' t i 0 then Some (i, 0) else None)" |
  "input_i_stored_in_reg t' t i (Suc r) = (if is_generalisation_of t' t i (Suc r) then Some (i, (Suc r)) else input_i_stored_in_reg t' t i r)"

primrec input_stored_in_reg_aux :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "input_stored_in_reg_aux t' t 0 r = input_i_stored_in_reg t' t 0 r" |
  "input_stored_in_reg_aux t' t (Suc i) r = (case input_i_stored_in_reg t' t (Suc i) r of
                                              None \<Rightarrow> input_i_stored_in_reg t' t i r |
                                              Some (i, r) \<Rightarrow> Some (i, r)
                                            ) "

definition input_stored_in_reg :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> (nat \<times> nat) option" where
  "input_stored_in_reg t' t e = input_stored_in_reg_aux t' t (max_reg e) (max_input e)"

definition initially_undefined_context_check :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "initially_undefined_context_check e r s = (\<forall>t. accepts_trace (tm e) t \<and> gets_us_to s (tm e) 0 <>  t \<longrightarrow> (anterior_context (tm e) t) (V (R r)) = {|Undef|} \<and> (\<forall>i. (anterior_context (tm e) t) (V (I i)) = {|Bc True|}))"

definition "no_illegal_updates t r = (\<forall>i. \<forall>u \<in> set (Updates t). fst u \<noteq> (R r) \<and> fst u \<noteq> (I i))"

lemma input_stored_in_reg_aux_is_generalisation_aux: "input_stored_in_reg_aux t' t mr mi = Some (i, r) \<Longrightarrow> is_generalisation_of t' t i r"
proof(induct mi)
  case 0
  then show ?case
  proof(induct mr)
    case 0
    then show ?case
      apply (case_tac "is_generalisation_of t' t 0 0")
      by auto
  next
    case (Suc mr)
    then show ?case
      apply simp
      apply (case_tac "is_generalisation_of t' t (Suc mr) 0")
       apply simp
      apply simp
      apply (case_tac "is_generalisation_of t' t mr 0")
      by auto
  qed
next
  case (Suc mi)
  then show ?case
  proof(induct mr)
    case 0
    then show ?case
      apply (case_tac "is_generalisation_of t' t 0 (Suc mi)")
      by auto
  next
    case (Suc mr)
    then show ?case
      apply simp
      apply (case_tac "is_generalisation_of t' t (Suc mr) (Suc mi)")
       apply simp
      apply simp
      apply (case_tac "input_i_stored_in_reg t' t (Suc mr) mi")
       apply simp
       apply (case_tac "is_generalisation_of t' t mr (Suc mi)")
      by auto
  qed
qed


lemma input_stored_in_reg_aux_is_generalisation: "input_stored_in_reg t' t e = Some (i, r) \<Longrightarrow> is_generalisation_of t' t i r"
  by (simp add: input_stored_in_reg_def input_stored_in_reg_aux_is_generalisation_aux)

(*
  This allows us to call these three functions for direct subsumption of generalised
*)
lemma generalised_directly_subsumes_original: 
  "input_stored_in_reg t' t e = Some (i, r) \<Longrightarrow>
   initially_undefined_context_check e r s' \<Longrightarrow>
   no_illegal_updates t r \<Longrightarrow>
   directly_subsumes e1 e s s' t' t"
  using input_stored_in_reg_aux_is_generalisation[of t' t e i r]
  apply (simp add: initially_undefined_context_check_def directly_subsumes_def no_illegal_updates_def)
  apply (case_tac "\<forall>t. accepts_trace (tm e) t \<and> gets_us_to s' (tm e) 0 Map.empty t \<longrightarrow> anterior_context (tm e) t (V (R r)) = {|Undef|}")
   defer
   apply simp
  apply (case_tac "\<forall>t. accepts_trace (tm e) t \<and> gets_us_to s' (tm e) 0 Map.empty t \<longrightarrow> (\<forall>i. anterior_context (tm e) t (V (I i)) = {|cexp.Bc True|})")
   defer
   apply simp
  apply standard
  using is_generalisation_of_subsumes_original[of t' t i r]
   apply simp
  apply (rule_tac x="\<lbrakk>\<rbrakk>" in exI)
  by (simp add: is_generalisation_of_subsumes_original)

definition drop_guard_add_update_direct_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> bool" where
  "drop_guard_add_update_direct_subsumption t' t e s' = (case input_stored_in_reg t' t e of None \<Rightarrow> False |
   Some (i, r) \<Rightarrow> if no_illegal_updates t r then initially_undefined_context_check e r s' else False)"

lemma "drop_guard_add_update_direct_subsumption t' t e s' \<Longrightarrow> directly_subsumes e1 e s s' t' t"
  apply (simp add: drop_guard_add_update_direct_subsumption_def)
  apply (case_tac "input_stored_in_reg t' t e")
   apply simp+
  apply (case_tac a)
  apply simp
  apply (case_tac "no_illegal_updates t b")
   apply (simp add: generalised_directly_subsumes_original)
  by simp

end