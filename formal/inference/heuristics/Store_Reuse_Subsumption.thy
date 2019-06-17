theory Store_Reuse_Subsumption
imports Store_Reuse
begin

declare One_nat_def [simp del]

lemma generalisation_of_preserves: "is_generalisation_of t' t i r \<Longrightarrow>
    Label t = Label t' \<and>
    Arity t = Arity t' \<and>
    (Outputs t) = (Outputs t')"
  apply (simp add: is_generalisation_of_def)
  using remove_guard_add_update_preserves by auto

lemma is_generalisation_of_guard_subset: "is_generalisation_of t' t i r \<Longrightarrow> set (Guard t') \<subseteq> set (Guard t)"
  apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
  by auto

lemma is_generalisation_of_medial: "is_generalisation_of t' t i r \<Longrightarrow> can_take t ip rg \<longrightarrow> can_take t' ip rg"
  using is_generalisation_of_guard_subset medial_subset by blast

lemma is_generalisation_of_preserves_reg: 
  "is_generalisation_of t' t i r \<Longrightarrow>
   apply_updates (Updates t) c (d2r c) r = c (R r)"
  by (simp add: is_generalisation_of_def r_not_updated_stays_the_same)

lemma is_generalisation_of_preserves_reg_2: "is_generalisation_of t' t i r \<Longrightarrow> ra \<noteq> r \<Longrightarrow> apply_updates (Updates t') (join_ir ia c) (d2r (join_ir ia c)) ra = apply_updates (Updates t) (join_ir ia c) (d2r (join_ir ia c)) ra"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma is_generalisation_of_apply_guards: "is_generalisation_of t' t i r \<Longrightarrow>
       apply_guards (Guard t) (join_ir ia c) \<Longrightarrow>
       apply_guards (Guard t') (join_ir ia c)"
  using is_generalisation_of_guard_subset apply_guards_subset by blast

(*
  This shows that if we drop the guard and add an update, and the updated register is undefined
  in the context, c, then the generalised transition subsumes the specific one
*)
lemma is_generalisation_of_subsumes_original:
  "is_generalisation_of t' t i r \<Longrightarrow>
   c r = None \<Longrightarrow>
   subsumes t' c t"
  apply (rule subsumption)
      apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
     apply (simp add: is_generalisation_of_medial)
    apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
   apply (simp add: posterior_def)
  apply clarify
   apply (case_tac "ra = r")
    apply (simp add: is_generalisation_of_preserves_reg join_ir_def)
   apply (simp add: is_generalisation_of_preserves_reg_2)
  apply clarify
  apply (simp add: posterior_def)
  apply (case_tac "apply_guards (Guard t) (join_ir ia c)")
   apply (simp add: is_generalisation_of_apply_guards)
   apply (metis is_generalisation_of_preserves_reg is_generalisation_of_preserves_reg_2 join_ir_def option.simps(3) vname.simps(6))
  by simp

(* 
  This shows that if we can guarantee that the value of a particular register is the literal output
  then the generalised output subsumes the specific output
*)
lemma generalise_output_subsumes_original: "nth (Outputs t) r = L v \<Longrightarrow>
                                            c p = Some v \<Longrightarrow>
                                            subsumes (generalise_output t p r) (r2d c) t"
  oops

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

definition generalise_output_context_check :: "String.literal \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> value \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "generalise_output_context_check l e e' p v s_old s_new = (\<forall>t. accepts_trace (tm e) t \<and> gets_us_to s_new (tm e) 0 <>  t \<longrightarrow> (anterior_context (tm e) t) (V (R p)) = {|Eq v|})"

fun generalise_output_direct_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "generalise_output_direct_subsumption t' t e e' s s' = (case stored_reused t' t e of
    None \<Rightarrow> False |
    Some (p, r) \<Rightarrow> (if is_generalised_output_of t' t p r then
      case nth (Outputs t) r of
        L v \<Rightarrow> generalise_output_context_check (Label t) e e' p v s s' |
        _ \<Rightarrow> False
      else False)
  )"

(* This allows us to just run the two functions for quick subsumption *)
lemma generalise_output_directly_subsumes_original_executable: 
      "generalise_output_direct_subsumption t' t e e' s s' \<Longrightarrow> directly_subsumes e1 e s s' t' t"
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

(* t' is the generalised transition *)
primrec input_i_stored_in_reg :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "input_i_stored_in_reg t' t i 0 = (if is_generalisation_of t' t i 0 then Some (i, 0) else None)" |
  "input_i_stored_in_reg t' t i (Suc r) = (if is_generalisation_of t' t i (Suc r) then Some (i, (Suc r)) else input_i_stored_in_reg t' t i r)"

(* t' is the generalised transition *)
primrec input_stored_in_reg_aux :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "input_stored_in_reg_aux t' t 0 r = input_i_stored_in_reg t' t 0 r" |
  "input_stored_in_reg_aux t' t (Suc i) r = (case input_i_stored_in_reg t' t (Suc i) r of
                                              None \<Rightarrow> input_i_stored_in_reg t' t i r |
                                              Some (i, r) \<Rightarrow> Some (i, r)
                                            ) "

(* t' is the generalised transition *)
definition input_stored_in_reg :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> (nat \<times> nat) option" where
  "input_stored_in_reg t' t e = (case input_stored_in_reg_aux t' t (max_reg e) (max_input e) of
                                 None \<Rightarrow> None |
                                 Some (i, r) \<Rightarrow> if length (filter (\<lambda>(r', u). r' = R r) (Updates t')) = 1 then Some (i, r) else None
)"

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
  apply (simp add: input_stored_in_reg_def)
  apply (cases "input_stored_in_reg_aux t' t (max_reg e) (max_input e)")
   apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac "length (filter (\<lambda>(r', u). r' = R b) (Updates t')) = 1")
   apply (simp add: input_stored_in_reg_aux_is_generalisation_aux)
  by simp

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

lemma drop_guard_add_update_direct_subsumption_implies_direct_subsumption:
  "drop_guard_add_update_direct_subsumption t' t e s' \<Longrightarrow> directly_subsumes e1 e s s' t' t"
  apply (simp add: drop_guard_add_update_direct_subsumption_def)
  apply (case_tac "input_stored_in_reg t' t e")
   apply simp+
  apply (case_tac a)
  apply simp
  apply (case_tac "no_illegal_updates t b")
   apply (simp add: generalised_directly_subsumes_original)
  by simp

lemma input_stored_in_reg_in_updates: "input_stored_in_reg t t' e = Some (aa, ba) \<Longrightarrow> (R ba, V (I aa)) \<in> set (Updates t)"
proof(induction "Updates t")
  case Nil
  then show ?case
    using input_stored_in_reg_def Nil.prems generalised_updates input_stored_in_reg_aux_is_generalisation by fastforce
next
  case (Cons a x)
  then show ?case
    using input_stored_in_reg_def Cons.prems generalised_updates input_stored_in_reg_aux_is_generalisation by fastforce
qed

lemma input_stored_in_reg_reg_updated_once: "input_stored_in_reg t t' e = Some (aa, r) \<Longrightarrow>
       length (filter (\<lambda>(r', u). r' = R r) (Updates t)) = 1"
  apply (simp add: input_stored_in_reg_def)
  apply (case_tac "input_stored_in_reg_aux t t' (max_reg e) (max_input e)")
   apply simp
  apply (case_tac a)
  apply clarify
  apply simp
  apply (case_tac "length (filter (\<lambda>(r', u). r' = R ba) (Updates t)) = 1")
  by auto

lemma only_one_update: "length (filter (\<lambda>(r', u). r' = R r) U) = 1 \<Longrightarrow>
      (R r, V (I aa)) \<in> set U \<Longrightarrow>
      (R r, u) \<in> set U \<Longrightarrow>
       u = V (I aa)"
proof(induct U)
  case Nil
  then show ?case by simp
next
  case (Cons a U)
  then show ?case
    apply simp
    apply (case_tac a)
    apply simp
    apply clarify
    apply (case_tac "ab = R r")
     apply simp
     apply (metis (mono_tags, lifting) case_prod_conv filter_empty_conv)
    by simp
qed

lemma register_updated_once:
  "input_stored_in_reg t t' e = Some (aa, ba) \<Longrightarrow>
  \<forall>u. (R ba, u) \<in> set (Updates t) \<longrightarrow> u = V (I aa)"
  using only_one_update input_stored_in_reg_reg_updated_once input_stored_in_reg_in_updates by blast

lemma remove_obsolete_constraints_leaves_registers: 
       "remove_obsolete_constraints (Contexts.apply_updates (medial c (Guard t)) c (Updates t)) (fst |`| fset_of_list (Updates t)) (V (R r)) =
       (Contexts.apply_updates (medial c (Guard t)) c (Updates t)) (V (R r))"
  apply (simp add: remove_obsolete_constraints_def no_illegal_updates_def)
  by auto

lemma input_stored_in_reg_aux_not_none: "input_stored_in_reg t t' e = Some (aa, ba) \<Longrightarrow>
input_stored_in_reg_aux t t' (max_reg e) (max_input e) \<noteq> None"
  apply (simp add: input_stored_in_reg_def)
  apply (cases "input_stored_in_reg_aux t t' (max_reg e) (max_input e)")
  by auto

lemma input_stored_in_reg_updatess_reg_to_input: 
      "input_stored_in_reg t t' e = Some (aa, ba) \<Longrightarrow>
       consistent (medial c (Guard t)) \<Longrightarrow>
       posterior c t (V (R ba)) = (medial c (Guard t)) (V (I aa))"
  apply (simp add: posterior_def posterior_separate_def)
  apply (simp add: remove_obsolete_constraints_leaves_registers)
  using generalised_updates input_stored_in_reg_aux_is_generalisation by fastforce

lemma input_stored_in_reg_guards_input: "input_stored_in_reg t t' e = Some (aa, ba) \<Longrightarrow> (\<exists> v. gexp.Eq (V (I aa)) (L v) \<in> set (Guard t'))"
  apply (simp add: input_stored_in_reg_def)
  apply (case_tac "input_stored_in_reg_aux t t' (max_reg e) (max_input e)")
   apply simp
  apply simp
  apply (case_tac a)
  apply clarify
  apply simp
  apply (case_tac "length (filter (\<lambda>(r', u). r' = R baa) (Updates t)) = 1")
   defer
   apply simp
  apply simp
  apply clarify
  apply simp
  apply (case_tac "max_reg e")
   apply (case_tac "max_input e")
    apply simp
    apply (case_tac "is_generalisation_of t t' 0 0")
     apply (simp add: is_generalisation_of_def)
    apply simp
   apply (case_tac "is_generalisation_of t t' 0 (Suc nat)")
    apply (simp add: is_generalisation_of_def)
  using input_stored_in_reg_aux_is_generalisation_aux is_generalisation_of_def apply blast
  apply simp
  apply (case_tac "max_input e")
   apply simp
   apply (case_tac "is_generalisation_of t t' (Suc nat) 0")
    apply (simp add: is_generalisation_of_def)
   apply simp
   apply (metis fst_conv is_generalisation_of_def option.inject option.simps(3))
  apply simp
  apply (case_tac "is_generalisation_of t t' (Suc nat) (Suc nata)")
   apply (simp add: is_generalisation_of_def)
  apply simp
  by (metis (no_types, lifting) input_i_stored_in_reg.simps(2) input_stored_in_reg_aux.simps(2) input_stored_in_reg_aux_is_generalisation_aux is_generalisation_of_def)

lemma input_stored_in_reg_medial_not_undef:
  "input_stored_in_reg t t' e = Some (aa, ba) \<Longrightarrow>
   medial c (Guard t') (V (I aa)) \<noteq> {|Undef|}"
  using input_stored_in_reg_guards_input[of t t' e aa ba]
  using equality_guard_gives_equality_constraint[of aa "Guard t'" c]
  by auto

lemma input_stored_in_reg_medial_equiv: "input_stored_in_reg t t' e = Some (aa, ba) \<Longrightarrow>
       medial c (Guard t @ Guard t') = medial c (Guard t')"
  using input_stored_in_reg_aux_is_generalisation[of t t' e aa ba]
  apply simp
  using generalisation_medial_equiv[of t t' aa ba c]
  apply simp
  using medial_append_commutative
  by simp
end