theory Store_Reuse_Subsumption
imports Store_Reuse Least_Upper_Bound
begin

lemma generalisation_of_preserves: "is_generalisation_of t' t i r \<Longrightarrow>
    Label t = Label t' \<and>
    Arity t = Arity t' \<and>
    (Outputs t) = (Outputs t')"
  apply (simp add: is_generalisation_of_def)
  using remove_guard_add_update_preserves by auto

lemma is_generalisation_of_guard_subset: "is_generalisation_of t' t i r \<Longrightarrow> set (Guard t') \<subseteq> set (Guard t)"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma is_generalisation_of_medial: "is_generalisation_of t' t i r \<Longrightarrow> can_take_transition t ip rg \<longrightarrow> can_take_transition t' ip rg"
  using is_generalisation_of_guard_subset medial_subset generalisation_of_preserves
  by (metis (no_types, lifting) can_take_def can_take_transition_def)

lemma is_generalisation_of_preserves_reg: 
  "is_generalisation_of t' t i r \<Longrightarrow>
   apply_updates (Updates t) (join_ir ia c) c $ r = c $ r"
  by (simp add: is_generalisation_of_def r_not_updated_stays_the_same)

lemma is_generalisation_of_preserves_reg_2:
  "is_generalisation_of t' t i r \<Longrightarrow>
   ra \<noteq> r \<Longrightarrow>
   apply_updates (Updates t) (join_ir ia c) c $ ra = apply_updates (Updates t') (join_ir ia c) c $ ra"
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
   c $ r = None \<Longrightarrow>
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

lemma generalise_output_posterior:
"posterior (generalise_output t p r) i ra = posterior t i ra"
  by (simp add: can_take_def generalise_output_preserves posterior_def)

lemma generalise_output_eq:
  "Pt ! r = Eq (L v) \<Longrightarrow>
   c $ p = Some v \<Longrightarrow>
   check_outs Pt (join_ir i c) P = check_outs (list_update Pt r (Eq (V (R p)))) (join_ir i c) P"
  apply (rule check_outs_equiv)
   apply simp
  apply (rule nth_equalityI)
   apply simp
  apply (case_tac "ia = r")
   apply (simp add: datastate(1))
  by simp

(* 
  This shows that if we can guarantee that the value of a particular register is the literal output
  then the generalised output subsumes the specific output
*)
lemma generalise_output_subsumes_original: 
  "Outputs t ! r = Eq (L v) \<Longrightarrow>
   c $ p = Some v \<Longrightarrow>
   subsumes (generalise_output t p r) c t"
  apply (rule subsumption)
      apply (simp add: generalise_output_def)
     apply (simp add: generalise_output_def can_take_def can_take_transition_def)
    apply (simp add: generalise_output_def generalise_output_eq)
  using generalise_output_preserves_updates posterior_separate_def apply auto[1]
  using generalise_output_posterior by auto

primrec stored_reused_aux_per_reg :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused_aux_per_reg t' t 0 p = (
    if is_generalised_output_of t' t 0 p then
      Some (0, p)
    else
       None
  )" |
  "stored_reused_aux_per_reg t' t (Suc r) p = (
    if is_generalised_output_of t' t (Suc r) p then
      Some (Suc r, p)
    else
      stored_reused_aux_per_reg t' t r p
  )"

primrec stored_reused_aux :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused_aux t' t r 0 = stored_reused_aux_per_reg t' t r 0" |
  "stored_reused_aux t' t r (Suc p) = (case stored_reused_aux_per_reg t' t r (Suc p) of
                                          Some x \<Rightarrow> Some x |
                                          None \<Rightarrow> stored_reused_aux t' t r p
                                        )"

definition stored_reused :: "transition \<Rightarrow> transition \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused t' t = stored_reused_aux t' t (max (Transition.total_max_reg t) (Transition.total_max_reg t')) (max (length (Outputs t)) (length (Outputs t')))"

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
  "stored_reused t' t = Some (p, r) \<Longrightarrow>
   is_generalised_output_of t' t p r"
  by (simp add: stored_reused_def stored_reused_aux_is_generalised_output_of)

lemma is_generalised_output_of_subsumes: 
  "is_generalised_output_of t' t r p \<Longrightarrow>
   nth (Outputs t) p = Eq (L v) \<Longrightarrow>
   c $ r = Some v \<Longrightarrow>
   subsumes t' c t"
  apply (rule subsumption)
      apply (simp add: generalise_output_preserves_arity generalise_output_preserves_label is_generalised_output_of_def)
     apply (simp add: can_take_transition_def generalise_output_def is_generalised_output_of_def)
    apply clarify
    apply (simp add: generalise_output_eq)
    apply (simp add: generalise_output_def is_generalised_output_of_def)
  using generalise_output_preserves_updates is_generalised_output_of_def posterior_separate_def 
  generalise_output_posterior is_generalised_output_of_def by auto

lemma lists_neq_if: "\<exists>i. l ! i \<noteq> l' ! i \<Longrightarrow> l \<noteq> l'"
  by auto

lemma generalise_output_directly_subsumes_original: 
      "stored_reused t' t = Some (r, p) \<Longrightarrow>
       nth (Outputs t) p = Eq (L v) \<Longrightarrow>
       (\<forall>p. accepts_trace (tm e1) p \<and> gets_us_to s (tm e1) 0 <>  p \<longrightarrow>
            accepts_trace (tm e2) p \<and> gets_us_to s' (tm e2) 0 <>  p \<longrightarrow>
       (\<exists>c. anterior_context (tm e2) p = Some c \<and> c $ r = Some v)) \<Longrightarrow>
       directly_subsumes e1 e2 s s' t' t "
  apply (simp add: directly_subsumes_def)
  apply standard
   apply clarify
  using stored_reused_is_generalised_output_of[of t' t r p]
        is_generalised_output_of_subsumes[of t' t r p v]
   apply auto[1]
  by (meson \<open>\<And>c. \<lbrakk>is_generalised_output_of t' t r p; Outputs t ! p = opred.Eq (L v); c $ r = Some v\<rbrakk> \<Longrightarrow> subsumes t' c t\<close> \<open>stored_reused t' t = Some (r, p) \<Longrightarrow> is_generalised_output_of t' t r p\<close> finfun_const_apply)

definition "generalise_output_context_check v r s\<^sub>1 s\<^sub>2 e\<^sub>1 e\<^sub>2 = 
(\<forall>t. accepts_trace (tm e\<^sub>1) t \<and> gets_us_to s\<^sub>1 (tm e\<^sub>1) 0 <> t \<longrightarrow>
     accepts_trace (tm e\<^sub>2) t \<and> gets_us_to s\<^sub>2 (tm e\<^sub>2) 0 <>  t \<longrightarrow>
 (\<exists>c. anterior_context (tm e\<^sub>2) t = Some c \<and> c $ r = Some v))"

lemma generalise_output_context_check_directly_subsumes_original: 
      "stored_reused t' t = Some (r, p) \<Longrightarrow>
       nth (Outputs t) p = Eq (L v) \<Longrightarrow>
       generalise_output_context_check v r s s' e1 e2 \<Longrightarrow>
       directly_subsumes e1 e2 s s' t' t "
  by (simp add: generalise_output_context_check_def generalise_output_directly_subsumes_original)

definition generalise_output_direct_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "generalise_output_direct_subsumption t' t e e' s s' = (case stored_reused t' t of
    None \<Rightarrow> False |
    Some (r, p) \<Rightarrow> 
      (case nth (Outputs t) p of
        Eq (L v) \<Rightarrow> generalise_output_context_check v r s s' e e' |
        _ \<Rightarrow> False)
  )"

(* This allows us to just run the two functions for quick subsumption *)
lemma generalise_output_directly_subsumes_original_executable: 
      "generalise_output_direct_subsumption t' t e e' s s' \<Longrightarrow> directly_subsumes e e' s s' t' t"
  apply (simp add: generalise_output_direct_subsumption_def)
  apply (case_tac "stored_reused t' t")
   apply simp
  apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac "Outputs t ! b")
       apply simp
      apply simp
      apply (case_tac x2)
         apply (simp add: generalise_output_context_check_directly_subsumes_original)
  by auto

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
  "input_stored_in_reg t' t e = (
    case input_stored_in_reg_aux t' t (total_max_reg e) (max (Arity t) (Arity t')) of
      None \<Rightarrow> None |
      Some (i, r) \<Rightarrow>
        if length (filter (\<lambda>(r', u). r' = r) (Updates t')) = 1 then
          Some (i, r)
        else None
  )"

definition initially_undefined_context_check :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "initially_undefined_context_check e r s = (\<forall>t. accepts_trace (tm e) t \<and> gets_us_to s (tm e) 0 <> t \<longrightarrow> (\<exists>a. (anterior_context (tm e) t) = Some a \<and> a $ r = None))"

lemma no_incoming_to_zero: "\<forall>(id, (from, to), t)|\<in>|e. 0 < to \<Longrightarrow>
       (aaa, ba) |\<in>| possible_steps (tm e) s d l i p \<Longrightarrow>
       aaa \<noteq> 0"
  using in_possible_steps in_tm
  by fast

lemma no_return_to_zero:
  "\<forall>(id, (from, to), t)|\<in>|e. 0 < to \<Longrightarrow>
   \<forall>r n. \<not> gets_us_to 0 (tm e) (Suc n) r t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: no_further_steps)
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (rule gets_us_to.cases)
       apply simp
      apply simp
     defer
    apply simp
    apply clarify
    apply simp
    apply (case_tac aaa)
     apply (metis no_incoming_to_zero Cons.prems not0_implies_Suc)
    apply simp
    by (metis Cons.prems no_incoming_to_zero not0_implies_Suc)
qed

lemma no_accepting_return_to_zero:
  "\<forall>(id, (from, to), t)|\<in>|e. to \<noteq> 0 \<Longrightarrow>
   accepts_trace (tm e) (a#t) \<Longrightarrow>
   \<not>gets_us_to 0 (tm e) 0 <> (a#t)"
  apply clarify
  apply (rule gets_us_to.cases)
     apply simp+
   apply clarify
  apply (case_tac ab)
    apply (metis fst_eqD no_incoming_to_zero snd_eqD)
   apply (simp add: no_return_to_zero)
  apply simp
  apply clarify
  using accepts_cons_step by blast

lemma no_return_to_zero_must_be_empty:
  "\<forall>(id, (from, to), t)|\<in>|e. to \<noteq> 0 \<Longrightarrow>
   accepts_trace (tm e) t \<and> gets_us_to 0 (tm e) 0 <> t \<Longrightarrow>
   t = []"
proof(induct t)
case Nil
  then show ?case
    by simp
next
case (Cons a t)
  then show ?case
    apply simp
    apply (rule accepts.cases)
      apply auto[1]
     apply simp
    using no_accepting_return_to_zero by auto
qed

lemma anterior_context_empty: "\<forall>(id, (from, to), t)|\<in>|e. to \<noteq> 0 \<Longrightarrow>
           accepts_trace (tm e) t \<Longrightarrow> gets_us_to 0 (tm e) 0 <> t \<Longrightarrow> anterior_context (tm e) t = Some <>"
  using no_return_to_zero_must_be_empty[of e]
        anterior_context_empty
  by auto

lemma no_incoming_to_initial_gives_empty_reg: "\<forall>(id, (from, to), t) |\<in>| e. to \<noteq> 0 \<Longrightarrow> initially_undefined_context_check e r 0"
  apply (simp only: initially_undefined_context_check_def)
  apply clarify
  apply standard
  apply (simp add: anterior_context_empty)
  by auto

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
  apply (cases "input_stored_in_reg_aux t' t (Inference.total_max_reg e) (max (Arity t) (Arity t'))")
   apply simp
  apply (case_tac a)
  apply simp
  apply (case_tac "length (filter (\<lambda>(r', u). r' = b) (Updates t')) = 1")
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
  using input_stored_in_reg_is_generalisation[of t' t e i r]
  apply (simp add: initially_undefined_context_check_def directly_subsumes_def no_illegal_updates_def)
  using is_generalisation_of_subsumes_original finfun_const_apply
  by (metis option.inject)

definition drop_guard_add_update_direct_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> bool" where
  "drop_guard_add_update_direct_subsumption t' t e s' = (
    case input_stored_in_reg t' t e of
      None \<Rightarrow> False |
      Some (i, r) \<Rightarrow>
        if no_illegal_updates t r then
          initially_undefined_context_check e r s'
        else False
    )"

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

lemma aval_unconstrained:
  " \<not> aexp_constrains a (V (vname.I i)) \<Longrightarrow>
  i < length ia \<Longrightarrow>
  v = ia ! i \<Longrightarrow>
  v' \<noteq> v \<Longrightarrow>
  aval a (join_ir ia c) = aval a (join_ir (list_update ia i v') c)"
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
  gval a (join_ir ia c) = gval a (join_ir (list_update ia i v') c)"
proof(induct a)
  case (Bc x)
  then show ?case 
    by (simp add: unconstrained_variable_swap_gval)
next
  case (Eq x1a x2)
  then show ?case 
    by (metis apply_guards(7) aval_unconstrained gexp_constrains.simps(3) list_update_id)
next
  case (Gt x1a x2)
  then show ?case 
    by (metis apply_guards(6) aval_unconstrained gexp_constrains.simps(4) list_update_id)
next
  case (Null x)
  then show ?case 
    by (metis aval_unconstrained gexp_constrains.simps(2) gval.simps(5) list_update_id)
next
  case (In x1a x2)
  then show ?case 
    by (metis aval.simps(2) aval_unconstrained gexp_constrains.simps(6) gval.simps(6) list_update_id)
next
  case (Nor a1 a2)
  then show ?case
    by simp
qed


(*
  If input i is stored in register r by transition t then if we can take transition t' then for some
  input I then transition t does not subsume t' 
*)
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
   apply (rule_tac x="list_update ia i (Str s)" in exI)
   apply simp
   apply standard
    apply (simp add: apply_guards_def)
    apply (metis gval_unconstrained is_generalisation_of_i_lt_arity is_generalisation_of_same_arity)
   apply (simp add: apply_guards_def Bex_def)
   apply standard
   apply (rule_tac x="gexp.Eq (V (vname.I i)) (L (Num x1))" in exI)
   apply (simp add: join_ir_def input2state_nth is_generalisation_of_i_lt_arity str_not_num)
   apply (rule_tac x="list_update ia i (Num s)" in exI)
   apply simp
   apply standard
    apply (simp add: apply_guards_def)
    apply (metis gval_unconstrained is_generalisation_of_i_lt_arity is_generalisation_of_same_arity)
   apply (simp add: apply_guards_def Bex_def)
   apply standard
   apply (rule_tac x="gexp.Eq (V (vname.I i)) (L (value.Str x2))" in exI)
  by (simp add: join_ir_def input2state_nth is_generalisation_of_i_lt_arity str_not_num)

lemma aval_updated: "(r, u) \<in> set U \<Longrightarrow> r \<notin> set (map fst (removeAll (r, u) U)) \<Longrightarrow> apply_updates U s c $ r = aval u s"
proof(induct U)
  case Nil
  then show ?case
    by simp
next
  case (Cons a U)
  then show ?case
    apply simp
    apply (case_tac "(r, u) = a")
    by auto
qed

lemma can_take_append_subset: "set (Guard t') \<subset> set (Guard t) \<Longrightarrow>
can_take a (Guard t @ Guard t') ia c = can_take a (Guard t) ia c"
  by (metis apply_guards_append apply_guards_subset_append can_take_def dual_order.strict_implies_order)

(*
  Does t = select:1[i1=coke] subsume t' = select:1/r1:=i1?
  Clearly it does not
*)
lemma general_not_subsume_orig:
  "Arity t' = Arity t \<Longrightarrow>
   set (Guard t') \<subset> set (Guard t) \<Longrightarrow>
   (r, (V (I i))) \<in> set (Updates t') \<Longrightarrow>
   r \<notin> set (map fst (removeAll (r, V (I i)) (Updates t'))) \<Longrightarrow>
   r \<notin> set (map fst (Updates t)) \<Longrightarrow>
   \<exists>i. can_take_transition t i c \<Longrightarrow>
   c $ r = None \<Longrightarrow>
   i < Arity t \<Longrightarrow>
   \<not> subsumes t c t'"
  apply (rule inconsistent_updates2)
  apply (erule_tac exE)
  apply (rule_tac x="apply_updates (Updates t') (join_ir ia c) c" in exI)
  apply (rule_tac x="apply_updates (Updates t) (join_ir ia c) c" in exI)
  apply standard
   apply (rule_tac x=ia in exI)
   apply (simp add: posterior_separate_def can_take_append_subset can_take_transition_def)
  using apply_guards_subset can_take_def apply auto[1]
  apply (rule_tac x="\<lambda>x. x = None" in exI)
  apply (rule_tac x=r in exI)
  apply standard
   apply (simp add: r_not_updated_stays_the_same)
  apply (simp add: aval_updated can_take_transition_def can_take_def)
  apply (rule_tac x="ia ! i" in exI)
  by (simp add: aval_updated join_ir_def input2state_nth)

lemma input_stored_in_reg_updates_reg: "input_stored_in_reg t2 t1 a = Some (i, r) \<Longrightarrow> (r, V (I i)) \<in> set (Updates t2)"
  using input_stored_in_reg_is_generalisation[of t2 t1 a i r]
  apply simp
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

definition "possibly_not_value_ctx v r t\<^sub>1 s\<^sub>2 e\<^sub>2 s\<^sub>1 e\<^sub>1 =
  (\<exists>p. accepts_trace (tm e\<^sub>1) p \<and> gets_us_to s\<^sub>1 (tm e\<^sub>1) 0 <>  p \<and>
       accepts_trace (tm e\<^sub>2) p \<and> gets_us_to s\<^sub>2 (tm e\<^sub>2) 0 <> p \<and>
       (case anterior_context (tm e\<^sub>2) p of None \<Rightarrow> False | Some c \<Rightarrow>
       (\<exists>i. can_take_transition t\<^sub>1 i c) \<and>
       c $ r \<noteq> Some v)
  )"

definition "accepts_and_gets_us_to_both a b s s' = (
  \<exists>p. accepts_trace (tm a) p \<and>
      gets_us_to s (tm a) 0 <> p \<and>
      accepts_trace (tm b) p \<and>
      gets_us_to s' (tm b) 0 <> p)"

definition updates_subset :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> bool" where
  "updates_subset t t' e = (
     case input_stored_in_reg t' t e of None \<Rightarrow> False | Some (i, r) \<Rightarrow>
     Arity t' = Arity t \<and>
     set (Guard t') \<subset> set (Guard t) \<and>
     r \<notin> set (map fst (removeAll (r, V (I i)) (Updates t'))) \<and>
     r \<notin> set (map fst (Updates t)) \<and>
     max_input_list (Guard t) < Some (Arity t) \<and>
     satisfiable_list (smart_not_null [0..<(Arity t)] (Guard t)) \<and>
     max_reg_list (Guard t) = None \<and>
     i < Arity t
  )"

definition "drop_update_add_guard_direct_subsumption a b s s' t1 t2 = 
  (case input_stored_in_reg t2 t1 a of
   None \<Rightarrow> False |
   Some (i, r) \<Rightarrow>
     accepts_and_gets_us_to_both a b s s' \<and>
     initially_undefined_context_check b r s' \<and>
     updates_subset t1 t2 a
  )"

lemma updates_subset_conditions: 
  "updates_subset t1 t2 e \<Longrightarrow>
   input_stored_in_reg t2 t1 e = Some (i, r) \<Longrightarrow>
   c $ r = None \<Longrightarrow>
   \<not> subsumes t1 c t2"
  apply (simp add: updates_subset_def)
  using can_take_satisfiable[of t1 c]
  apply simp
  apply (rule general_not_subsume_orig)
  using input_stored_in_reg_updates_reg satisfiable_list_snn
  by auto

lemma drop_update_add_guard_direct_subsumption:
  "drop_update_add_guard_direct_subsumption a b s s' t1 t2 \<Longrightarrow>
  \<not>directly_subsumes a b s s' t1 t2"
  apply (simp add: drop_update_add_guard_direct_subsumption_def)
  apply (case_tac "input_stored_in_reg t2 t1 a")
   apply simp
  apply (simp add: directly_subsumes_def)
  apply (case_tac aa)
  apply (rule disjI1)
  apply (simp add: accepts_and_gets_us_to_both_def)
  apply clarify
  apply (rule_tac x=p in exI)
  apply (simp add: initially_undefined_context_check_def)
  using updates_subset_conditions by blast

end