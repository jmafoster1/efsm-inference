theory Store_Reuse_Subsumption
imports Store_Reuse
begin

lemma generalisation_of_preserves: "is_generalisation_of t' t i r \<Longrightarrow>
    Label t = Label t' \<and>
    Arity t = Arity t' \<and>
    (Outputs t) = (Outputs t')"
  apply (simp add: is_generalisation_of_def)
  using remove_guard_add_update_preserves by auto

lemma is_generalisation_of_guard_subset: "is_generalisation_of t' t i r \<Longrightarrow> set (Guard t') \<subseteq> set (Guard t)"
  apply (simp add: is_generalisation_of_def remove_guard_add_update_def)
  by auto

lemma is_generalisation_of_medial: "is_generalisation_of t' t i r \<Longrightarrow> can_take_transition t ip rg \<longrightarrow> can_take_transition t' ip rg"
  using is_generalisation_of_guard_subset medial_subset generalisation_of_preserves
  by (metis (no_types, lifting) can_take_def can_take_transition_def)

lemma is_generalisation_of_preserves_reg: 
  "is_generalisation_of t' t i r \<Longrightarrow>
   apply_updates (Updates t) (join_ir ia c) c r = c r"
  by (simp add: is_generalisation_of_def r_not_updated_stays_the_same)

lemma is_generalisation_of_preserves_reg_2:
  "is_generalisation_of t' t i r \<Longrightarrow>
   ra \<noteq> r \<Longrightarrow>
   apply_updates (Updates t) (join_ir ia c) c ra = apply_updates (Updates t') (join_ir ia c) c ra"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma is_generalisation_of_apply_guards: "is_generalisation_of t' t i r \<Longrightarrow>
       apply_guards (Guard t) j \<Longrightarrow>
       apply_guards (Guard t') j"
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
   apply (simp add: posterior_def can_take_def is_generalisation_of_apply_guards generalisation_of_preserves)
   apply clarify
   apply (case_tac "r' = r")
    apply (metis is_generalisation_of_preserves_reg option.distinct(1) option.sel posterior_separate_def)
   apply (metis is_generalisation_of_preserves_reg_2 option.inject option.simps(3) posterior_separate_def)
  by (metis is_generalisation_of_preserves_reg is_generalisation_of_preserves_reg_2 option.distinct(1) option.sel posterior_def posterior_separate_def)

lemma apply_outputs_literal: "P ! r = L v \<Longrightarrow>
       r < length (apply_outputs P (join_ir i c)) \<Longrightarrow>
       apply_outputs P (join_ir i c) ! r = Some v"
proof(induct P)
  case Nil
  then show ?case
    by (simp add: apply_outputs_preserves_length)
next
  case (Cons a P)
  then show ?case
    apply (simp add: apply_outputs_preserves_length)
    apply (simp add: apply_outputs_def)
    using less_Suc_eq_0_disj nth_map by auto
qed

lemma apply_outputs_register:
  "c p = Some v \<Longrightarrow>
   r < length (apply_outputs P (join_ir i c)) \<Longrightarrow>
   apply_outputs (P[r := V (R p)]) (join_ir i c) ! r = Some v"
proof(induct P)
  case Nil
  then show ?case
    by (simp add: apply_outputs_preserves_length)
next
  case (Cons a P)
  then show ?case
    apply (simp add: apply_outputs_preserves_length)
    apply (simp add: apply_outputs_def)
    apply (cases r)
     apply (simp add: join_ir_def)
    by (simp add: join_ir_def)
qed

lemma apply_outputs_unupdated:
  "ia \<noteq> r \<Longrightarrow> 
   ia < length (apply_outputs P j) \<Longrightarrow>
   apply_outputs P j ! ia = apply_outputs (P[r := v])j ! ia"
proof(induct P)
case Nil
  then show ?case
    by (simp add: apply_outputs_preserves_length)
next
  case (Cons a P)
  then show ?case
    apply (simp add: apply_outputs_preserves_length)
    apply (simp add: apply_outputs_def)
    apply (cases r)
     apply simp
    by (simp add: map_update nth_Cons')
qed

lemma generalise_output_posterior:
"posterior (generalise_output t p r) i ra = posterior t i ra"
  by (simp add: can_take_def generalise_output_preserves posterior_def)

lemma generalise_output_eq:
  "(Outputs t) ! r = L v \<Longrightarrow>
   c p = Some v \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir i c) = apply_outputs (list_update (Outputs t) r (V (R p))) (join_ir i c)"
  apply (rule nth_equalityI)
   apply (simp add: apply_outputs_preserves_length)
  apply (case_tac "ia = r")
   apply (metis apply_outputs_literal apply_outputs_register apply_outputs_unupdated)
  by (metis apply_outputs_literal apply_outputs_register apply_outputs_unupdated)

(* 
  This shows that if we can guarantee that the value of a particular register is the literal output
  then the generalised output subsumes the specific output
*)
lemma generalise_output_subsumes_original: 
  "Outputs t ! r = L v \<Longrightarrow>
   c p = Some v \<Longrightarrow>
   subsumes (generalise_output t p r) c t"
  apply (rule subsumption)
      apply (simp add: generalise_output_def)
     apply (simp add: generalise_output_def can_take_def can_take_transition_def)
    apply (simp add: generalise_output_def generalise_output_eq)
  using generalise_output_preserves_updates posterior_separate_def apply auto[1]
  using generalise_output_posterior by auto

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
  "stored_reused t' t e = stored_reused_aux t' t (total_max_reg e) (max_output e)"

lemma stored_reused_aux_is_generalised_output_of: 
"stored_reused_aux t' t mr mp = Some (p, r) \<Longrightarrow> is_generalised_output_of t' t p r"
proof(induct mr)
  case 0
  then show ?case
  proof(induct mp)
    case 0
    then show ?case
      apply simp
      by (metis option.distinct(1) option.inject prod.inject)
  next
    case (Suc mp)
    then show ?case
      apply simp
      apply (case_tac "is_generalised_output_of t' t 0 (Suc mp)")
       apply simp
      by simp
  qed
next
  case (Suc mr)
  then show ?case
  proof(induct mp)
    case 0
    then show ?case
      apply simp
      by (metis option.inject prod.inject)
  next
    case (Suc mp)
    then show ?case
      apply simp
      apply (case_tac "stored_reused_aux_per_reg t' t mr (Suc mp)")
       apply simp
       apply (case_tac "is_generalised_output_of t' t (Suc mr) (Suc mp)")
        apply simp
       apply simp
      apply simp
      apply (case_tac "is_generalised_output_of t' t (Suc mr) (Suc mp)")
       apply simp
      by simp
  qed
qed

lemma stored_reused_is_generalised_output_of:
  "stored_reused t' t e = Some (p, r) \<Longrightarrow>
   is_generalised_output_of t' t p r"
  by (simp add: stored_reused_def stored_reused_aux_is_generalised_output_of)

(*
    This shows that we can use the model checker to test whether the relevant register is the correct
    value for direct subsumption 
*)
lemma generalise_output_directly_subsumes_original: 
      "stored_reused t' t e = Some (p, r) \<Longrightarrow>
       nth (Outputs t) r = L v \<Longrightarrow>
       \<forall>t a. accepts_trace (tm e) t \<and> gets_us_to s' (tm e) 0 <>  t \<longrightarrow> (anterior_context (tm e) t) = Some a \<longrightarrow> a p = Some v \<Longrightarrow>
       directly_subsumes e1 e s s' t' t "
  using stored_reused_is_generalised_output_of[of t' t e p r]
  apply (simp add: directly_subsumes_def)
  apply standard
   apply clarify
   apply (case_tac "posterior_sequence (tm e) 0 Map.empty pa")
  using accepts_gives_context apply fastforce
   apply simp
    apply (simp add: is_generalised_output_of_def)
  using generalise_output_subsumes_original apply blast
    apply (simp add: is_generalised_output_of_def)
  using generalise_output_subsumes_original by fastforce

definition generalise_output_context_check :: "String.literal \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> value \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "generalise_output_context_check l e e' p v s_old s_new = (\<forall>t a. accepts_trace (tm e) t \<and> gets_us_to s_new (tm e) 0 <>  t \<longrightarrow> (anterior_context (tm e) t) = Some a \<longrightarrow> a p = Some v)"

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
  "input_stored_in_reg t' t e = (case input_stored_in_reg_aux t' t (total_max_reg e) (total_max_input e) of
                                 None \<Rightarrow> None |
                                 Some (i, r) \<Rightarrow> if length (filter (\<lambda>(r', u). r' = r) (Updates t')) = 1 then Some (i, r) else None
)"

definition initially_undefined_context_check :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "initially_undefined_context_check e r s = (\<forall>t a. accepts_trace (tm e) t \<and> gets_us_to s (tm e) 0 <> t \<longrightarrow> (anterior_context (tm e) t) = Some a \<and> a r = None)"

definition "no_illegal_updates t r = (\<forall>u \<in> set (Updates t). fst u \<noteq> r)"

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


lemma input_stored_in_reg_is_generalisation: "input_stored_in_reg t' t e = Some (i, r) \<Longrightarrow> is_generalisation_of t' t i r"
  apply (simp add: input_stored_in_reg_def)
  apply (cases "input_stored_in_reg_aux t' t (total_max_reg e) (total_max_input e)")
   apply simp
  apply (case_tac a)
  apply simp
  by (metis input_stored_in_reg_aux_is_generalisation_aux option.distinct(1))

(*
  This allows us to call these three functions for direct subsumption of generalised
*)
lemma generalised_directly_subsumes_original: 
  "input_stored_in_reg t' t e = Some (i, r) \<Longrightarrow>
   initially_undefined_context_check e r s' \<Longrightarrow>
   no_illegal_updates t r \<Longrightarrow>
   directly_subsumes e1 e s s' t' t"
  using input_stored_in_reg_is_generalisation[of t' t e i r]
  apply (simp add: initially_undefined_context_check_def directly_subsumes_def no_illegal_updates_def)
  using is_generalisation_of_subsumes_original by fastforce

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

lemma is_generalisation_of_constrains_input: "is_generalisation_of t' t i r \<Longrightarrow> \<exists>v. gexp.Eq (V (vname.I i)) (L v) \<in> set (Guard t)"
  by (simp add: is_generalisation_of_def)

lemma is_generalisation_of_derestricts_input: "is_generalisation_of t' t i r \<Longrightarrow> \<forall>g \<in> set (Guard t'). \<not> gexp_constrains g (V (vname.I i))"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma is_generalisation_of_same_arity: "is_generalisation_of t' t i r \<Longrightarrow> Arity t = Arity t'"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma is_generalisation_of_i_lt_arity: "is_generalisation_of t' t i r \<Longrightarrow> i < Arity t"
  by (simp add: is_generalisation_of_def)

lemma "\<forall>i. \<not> can_take_transition t i r \<and> \<not> can_take_transition t' i r \<Longrightarrow>
       Label t = Label t' \<Longrightarrow>
       Arity t = Arity t' \<Longrightarrow>
       subsumes t' r t"
  apply (simp add: subsumes_def)
   apply (simp add: posterior_separate_def can_take_transition_def)
  by (simp add: can_take_transition_def posterior_def posterior_separate_def)

lemma can_take_must_be_eq: 
  "Eq (V (vname.I i)) (L v) \<in> set (Guard t) \<Longrightarrow>
       ia ! i \<noteq> v \<Longrightarrow>
       i < Arity t \<Longrightarrow>
       length ia = Arity t \<Longrightarrow>
       \<not> can_take_transition t ia r"
  apply (simp add: can_take_transition_def can_take_def apply_guards_def)
  apply (simp add: Bex_def)
  apply (rule_tac x= "Eq (V (vname.I (i))) (L v)" in exI)
  apply (simp add: join_ir_def)
  using input2state_nth[of i ia]
  by simp

lemma restrict_i_cant_swap: 
      "is_generalisation_of t' t i r \<Longrightarrow>
       Eq (V (vname.I i)) (L v) \<in> set (Guard t) \<Longrightarrow>
       length ia = Arity t \<Longrightarrow>
       ia ! i \<noteq> v \<Longrightarrow>
       Arity t' = Arity t \<Longrightarrow>
       \<not> apply_guards (Guard t) (join_ir ia c)"
  using is_generalisation_of_i_lt_arity[of t' t i r]
  using can_take_must_be_eq[of i v t ia c]
  unfolding can_take_transition_def can_take_def
  by simp

lemma ex_v_neq_value: "ia ! i = (v::value) \<Longrightarrow> \<exists>v'. v' \<noteq> v"
  apply (cases v)
  by auto

lemma inputs_v_neq_value: "i < length ia \<Longrightarrow> ia ! i = (v::value) \<Longrightarrow> \<exists>ia'. length ia' = length ia \<and> ia'!i \<noteq> v"
  using ex_v_neq_value[of ia i v]
  apply simp
  apply clarify
  apply (rule_tac x="ia[i := v']" in exI)
  by simp

lemma aval_unconstrained:
  " \<not> aexp_constrains a (V (vname.I i)) \<Longrightarrow>
  i < length ia \<Longrightarrow>
  v = ia ! i \<Longrightarrow>
  v' \<noteq> v \<Longrightarrow>
  aval a (join_ir ia c) = aval a (join_ir (ia[i := v']) c)"
proof(induct a)
  case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (simp add: join_ir_def)
    apply (cases x)
     defer
     apply simp
    apply simp
    apply (case_tac "x1 < length ia")
     apply (simp add: input2state_nth)
    by (simp add: input2state_out_of_bounds)
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma gval_unconstrained: 
 " \<not> gexp_constrains a (V (vname.I i)) \<Longrightarrow>
  i < length ia \<Longrightarrow>
  v = ia ! i \<Longrightarrow>
  gval a (join_ir ia c) = gval a (join_ir (ia[i := v']) c)"
proof(induct a)
case (Bc x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Eq x1a x2)
  then show ?case
    apply simp
    by (metis aval_unconstrained list_update_same_conv)
next                   
  case (Gt x1a x2)
  then show ?case
    apply simp
    by (metis aval_unconstrained list_update_same_conv)
next
  case (Nor a1 a2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    apply simp
    by (metis aval_unconstrained list_update_same_conv)
qed

lemma is_generalisation_of_can_swap_out_i:
   "is_generalisation_of t' t i r \<Longrightarrow>
   i < length ia \<Longrightarrow>
   v = ia ! i \<Longrightarrow>
   \<forall>g\<in>set (Guard t').  gval g (join_ir ia c) = gval g (join_ir (ia[i := v']) c)"
  using is_generalisation_of_derestricts_input gval_unconstrained by blast

lemma input_stored_in_reg_not_subsumed: 
  "input_stored_in_reg t' t e = Some (i, r) \<Longrightarrow>
   \<exists>i. can_take_transition t' i c \<Longrightarrow>
   \<not> subsumes t c t'"
  using input_stored_in_reg_is_generalisation[of t' t e i r]
  using is_generalisation_of_constrains_input[of t' t i r]
  using is_generalisation_of_derestricts_input[of t' t i r]
  apply simp
  apply (rule bad_guards)
  apply clarify
  apply (simp add: can_take_transition_def can_take_def)
  apply clarify
  apply (case_tac "v")
   apply (rule_tac x="ia[i:=Str s]" in exI)
   apply simp
   apply standard
    apply (simp add: apply_guards_def)
    apply (metis gval_unconstrained is_generalisation_of_i_lt_arity is_generalisation_of_same_arity)
   apply (simp add: apply_guards_def Bex_def)
   apply standard
   apply (rule_tac x="Eq (V (vname.I i)) (L (Num x1))" in exI)
   apply (simp add: join_ir_def input2state_nth is_generalisation_of_i_lt_arity str_not_num)

   apply (rule_tac x="ia[i:=Num s]" in exI)
   apply simp
   apply standard
    apply (simp add: apply_guards_def)
    apply (metis gval_unconstrained is_generalisation_of_i_lt_arity is_generalisation_of_same_arity)
   apply (simp add: apply_guards_def Bex_def)
   apply standard
   apply (rule_tac x="Eq (V (vname.I i)) (L (value.Str x2))" in exI)
  by (simp add: join_ir_def input2state_nth is_generalisation_of_i_lt_arity str_not_num)

lemma drop_guard_add_update_direct_subsumption_not_implies_direct_subsumption:
  "drop_guard_add_update_direct_subsumption t t' e s' \<Longrightarrow>
  \<exists>p. accepts (tm e1) 0 Map.empty p \<and>
      gets_us_to s (tm e1) 0 Map.empty p \<and>
      accepts (tm e) 0 Map.empty p \<and>
      gets_us_to s' (tm e) 0 Map.empty p \<Longrightarrow>
   \<not>directly_subsumes e1 e s s' t' t"
  apply (simp add: drop_guard_add_update_direct_subsumption_def)
  apply (case_tac "input_stored_in_reg t t' e")
   apply simp
  apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac "no_illegal_updates t' b")
   apply (simp add: no_illegal_updates_def initially_undefined_context_check_def directly_subsumes_def)
   apply auto[1]
  by simp

end