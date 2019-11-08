theory Code_Generation
  imports 
   "HOL-Library.Code_Target_Numeral"
   Inference SelectionStrategies
   Type_Inference
   "heuristics/Store_Reuse_Subsumption"
   "heuristics/Increment_Reset"
   "heuristics/Same_Register"
   "heuristics/Ignore_Inputs"
   "heuristics/Least_Upper_Bound"
   "heuristics/Equals"
   "heuristics/Symbolic_Regression"
   "heuristics/Distinguishing_Guards"
   EFSM_Dot
   Code_Target_FSet
   Code_Target_Set
   Code_Target_List
   Use_Small_Numbers
efsm2sal
begin

declare One_nat_def [simp del]

(*
  Let's use the native operators for booleans and pairs
*)
code_printing
  constant HOL.conj \<rightharpoonup> (Scala) "_ && _" |
  constant HOL.disj \<rightharpoonup> (Scala) "_ || _" |
  constant "HOL.equal :: bool \<Rightarrow> bool \<Rightarrow> bool" \<rightharpoonup> (Scala) infix 4 "==" |
  constant "fst" \<rightharpoonup> (Scala) "_.'_1" |
  constant "snd" \<rightharpoonup> (Scala) "_.'_2"|
  constant "(1::nat)" \<rightharpoonup> (Scala) "Nat.Nata((1))"

(*
  This gives us a speedup as we don't need to check that a register is undefined in the initial
  state if there is no way to get back there. This is true by definition.
*)
definition "initially_undefined_context_check_full = initially_undefined_context_check"

lemma [code]:
"initially_undefined_context_check e r s = (
  if s = 0 \<and> (\<forall>((from, to), t) |\<in>| e. to \<noteq> 0) then
    True
  else
    initially_undefined_context_check_full e r s
  )"
  apply (case_tac "s = 0 \<and> (\<forall>((from, to), t)|\<in>|e. to \<noteq> 0)")
   apply (simp add: no_incoming_to_initial_gives_empty_reg)
  using initially_undefined_context_check_full_def by presburger

(* This gives us a speedup because we can check this before we have to call out to z3 *)
fun mutex :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "mutex (Eq (V v) (L l)) (Eq (V v') (L l')) = (if v = v' then l \<noteq> l' else False)" |
  "mutex (gexp.In v l) (Eq (V v') (L l')) = (v = v' \<and> l' \<notin> set l)" |
  "mutex (Eq (V v') (L l')) (gexp.In v l) = (v = v' \<and> l' \<notin> set l)" |
  "mutex (gexp.In v l) (gexp.In v' l') = (v = v' \<and> set l \<inter> set l' = {})" |
  "mutex _ _ = False"

lemma mutex_not_gval: "mutex x y \<Longrightarrow> gval (gAnd y x) s \<noteq> true"
  apply (induct x y rule: mutex.induct)
  apply (simp, metis option.inject)
  by auto

(* (\<exists>(i, s1) \<in> set (get_ins (Guard t1)).
   \<exists>(i', s2) \<in> set (get_ins (Guard t2)).
   i = i' \<and>
   \<not> (set s2) \<subseteq> (set s1) \<and>
   restricted_once (I i) (Guard t2)) *)

definition choice_cases :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice_cases t1 t2 = (
     if \<exists>(x, y) \<in> set (List.product (Guard t1) (Guard t2)). mutex x y then
       False
     else if Guard t1 = Guard t2 then
       satisfiable (fold gAnd (rev (Guard t1)) (gexp.Bc True))
     else
       satisfiable ((fold gAnd (rev (Guard t1@Guard t2)) (gexp.Bc True)))
   )"

lemma existing_mutex_not_true: "\<exists>x\<in>set G. \<exists>y\<in>set G. mutex x y \<Longrightarrow> \<not> apply_guards G s"
  apply clarify
  apply (simp add: apply_guards_rearrange)
  apply (case_tac "y \<in> set (x#G)")
   defer
   apply simp
  apply (simp only: apply_guards_rearrange)
  apply simp
  apply (simp only: apply_guards_double_cons)
  using mutex_not_gval
  by simp

lemma [code]: "choice t t' = choice_cases t t'"
  apply (simp only: choice_alt choice_cases_def)
  apply (case_tac "\<exists>x\<in>set (map (\<lambda>(x, y). mutex x y) (List.product (Guard t) (Guard t'))). x")
   apply (simp add: choice_alt_def)
   apply (metis existing_mutex_not_true Un_iff set_append)
  apply (case_tac "Guard t = Guard t'")
   apply (simp add: choice_alt_def apply_guards_append)
   apply (simp add: apply_guards_foldr fold_conv_foldr satisfiable_def)
  by (simp add: apply_guards_foldr choice_alt_def fold_conv_foldr satisfiable_def)

fun guardMatch_code :: "gexp list \<Rightarrow> gexp list \<Rightarrow> bool" where
  "guardMatch_code [(gexp.Eq (V (vname.I i)) (L (Num n)))] [(gexp.Eq (V (vname.I i')) (L (Num n')))] = (i = 0 \<and> i' = 0)" |
  "guardMatch_code _ _ = False"

lemma [code]: "guardMatch t1 t2 = guardMatch_code (Guard t1) (Guard t2)"
  apply (simp add: guardMatch_def)
  using guardMatch_code.elims(2) by fastforce

fun outputMatch_code :: "output_function list \<Rightarrow> output_function list \<Rightarrow> bool" where
  "outputMatch_code [L (Num n)] [L (Num n')] = True" |
  "outputMatch_code _ _ = False"

lemma [code]: "outputMatch t1 t2 = outputMatch_code (Outputs t1) (Outputs t2)"
  by (metis outputMatch_code.elims(2) outputMatch_code.simps(1) outputMatch_def)

fun always_different_outputs :: "aexp list \<Rightarrow> aexp list \<Rightarrow> bool" where
  "always_different_outputs [] [] = False" |
  "always_different_outputs [] (a#_) = True" |
  "always_different_outputs (a#_) [] = True" |
  "always_different_outputs ((L v)#t) ((L v')#t') = (if v = v' then always_different_outputs t t' else True)" |
  "always_different_outputs (h#t) (h'#t') = always_different_outputs t t'"

lemma always_different_outputs_outputs_never_equal:
  "always_different_outputs O1 O2 \<Longrightarrow>
   apply_outputs O1 s \<noteq> apply_outputs O2 s"
  apply(induct O1 O2 rule: always_different_outputs.induct)
  by (simp_all add: apply_outputs_def)

fun tests_input_equality :: "nat \<Rightarrow> gexp \<Rightarrow> bool" where
  "tests_input_equality i (gexp.Eq (V (vname.I i')) (L _)) = (i = i')" |
  "tests_input_equality _ _ = False"

fun no_illegal_updates_code :: "update_function list \<Rightarrow> nat \<Rightarrow> bool" where
  "no_illegal_updates_code [] _ = True" |
  "no_illegal_updates_code ((r', u)#t) r = (r \<noteq> r' \<and> no_illegal_updates_code t r)"

lemma no_illegal_updates_code_aux: "(\<forall>u\<in>set u. fst u \<noteq> r) = no_illegal_updates_code u r"
proof(induct u)
case Nil
  then show ?case
    by simp
next
case (Cons a u)
  then show ?case
    apply (cases a)
    apply (case_tac aa)
    by auto
qed

lemma no_illegal_updates_code [code]: "no_illegal_updates t r = no_illegal_updates_code (Updates t) r"
  by (simp add: no_illegal_updates_def no_illegal_updates_code_aux)

fun input_updates_register_aux :: "update_function list \<Rightarrow> nat option" where
  "input_updates_register_aux ((n, V (vname.I n'))#_) = Some n'" |
  "input_updates_register_aux (h#t) = input_updates_register_aux t" |
  "input_updates_register_aux [] = None"

definition input_updates_register :: "transition_matrix \<Rightarrow> (nat \<times> String.literal)" where
  "input_updates_register e = (
    case fthe_elem (ffilter (\<lambda>(_, t). input_updates_register_aux (Updates t) \<noteq> None) e) of
      (_, t) \<Rightarrow> (case
        input_updates_register_aux (Updates t) of
          Some n \<Rightarrow> (n, Label t)
      )
  )"

definition "dirty_directly_subsumes = directly_subsumes"

definition always_different_outputs_direct_subsumption ::"iEFSM \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> bool" where
"always_different_outputs_direct_subsumption m1 m2 s s' t2 = (
   (\<exists>p. accepts (tm m1) 0 <> p \<and>
    gets_us_to s (tm m1) 0 <> p \<and>
    accepts (tm m2) 0 <> p \<and>
    gets_us_to s' (tm m2) 0 <> p \<and>
    (case anterior_context (tm m2) p of Some c \<Rightarrow> (\<exists>i. can_take_transition t2 i c))))"

lemma always_different_outputs_can_take_transition_not_subsumed:
  "always_different_outputs (Outputs t1) (Outputs t2) \<Longrightarrow>
   \<forall>c. posterior_sequence (tm m2) 0 <> p = Some c \<longrightarrow> (\<exists>i. can_take_transition t2 i c) \<longrightarrow> \<not> subsumes t1 c t2"
  apply standard
  apply standard
  apply standard
  apply (rule bad_outputs)
  by (metis always_different_outputs_outputs_never_equal)

lemma always_different_outputs_direct_subsumption: 
  "always_different_outputs (Outputs t1) (Outputs t2) \<Longrightarrow>
   always_different_outputs_direct_subsumption m1 m2 s s' t2 \<Longrightarrow>
   \<not> directly_subsumes m1 m2 s s' t1 t2"
  apply (simp add: directly_subsumes_def always_different_outputs_direct_subsumption_def)
  apply standard
  apply clarify
  apply (rule_tac x=p in exI)
  apply simp
  using always_different_outputs_can_take_transition_not_subsumed accepts_trace_gives_context accepts_gives_context
  by fastforce

definition negate :: "gexp list \<Rightarrow> gexp" where
  "negate g = gNot (fold gAnd g (Bc True))"

lemma gval_negate_cons: "gval (negate (a # G)) s = gval (gNot a) s \<or>\<^sub>? gval (negate G) s"
  apply (simp only: negate_def gval_gNot gval_fold_equiv_gval_foldr)
  by (simp only: foldr.simps comp_def gval_gAnd de_morgans_2)

lemma negate_true_guard: "(gval (negate G) s = true) = (gval (fold gAnd G (Bc True)) s = false)"
  by (metis (no_types, lifting) gval_gNot maybe_double_negation maybe_not.simps(1) negate_def)

lemma gval_negate_not_invalid: "(gval (negate gs) (join_ir i ra) \<noteq> invalid) = (gval (fold gAnd gs (Bc True)) (join_ir i ra) \<noteq> invalid)"
  using gval_gNot maybe_not_invalid negate_def by auto

lemma quick_negation:
  "max_reg_list (Guard t) = None \<Longrightarrow>
   max_input_list (Guard t) < Some (Arity t) \<Longrightarrow>
   satisfiable_list (negate (Guard t) # ensure_not_null (Arity t)) \<Longrightarrow>
   \<exists>i. length i = Arity t \<and> \<not> apply_guards (Guard t) (join_ir i r)"
  apply (simp add: satisfiable_list_def satisfiable_def fold_apply_guards apply_guards_cons del: fold.simps)
  apply clarify
  apply (rule_tac x="take_or_pad i (Arity t)" in exI)
  apply (simp add: length_take_or_pad)
  apply (simp add: apply_guards_ensure_not_null_length take_or_pad_def negate_true_guard)
  apply (simp add: apply_guards_fold)
  by (metis (no_types, lifting) less_eq_Some_trans gval_fold_swap_regs gval_fold_take trilean.simps(2))

definition "satisfiable_negation t = (max_reg_list (Guard t) = None \<and>
   max_input_list (Guard t) < Some (Arity t) \<and>
   satisfiable_list (negate (Guard t) # ensure_not_null (Arity t)))"

lemma satisfiable_negation_cant_subsume:
  assumes prem: "satisfiable_negation t"
  shows "\<not> subsumes t c (drop_guards t)"
proof-
  have ponens: "\<forall>i. (length i = Arity t \<and> (length i = Arity t \<longrightarrow> \<not> apply_guards (Guard t) (join_ir i c))) =
                (length i = Arity t \<and> \<not> apply_guards (Guard t) (join_ir i c))"
    by auto
  show ?thesis
    apply (rule bad_guards)
    apply (simp add: can_take_transition_def can_take_def drop_guards_def ponens)
    using satisfiable_negation_def quick_negation prem
    by auto
qed

definition "dirty_always_different_outputs_direct_subsumption = always_different_outputs_direct_subsumption"

lemma [code]: "always_different_outputs_direct_subsumption m1 m2 s s' t = (
  if Guard t = [] then
    accepts_and_gets_us_to_both m1 m2 s s'
  else
    dirty_always_different_outputs_direct_subsumption m1 m2 s s' t
  )"
  apply (simp add: always_different_outputs_direct_subsumption_def)
  apply (simp add: accepts_and_gets_us_to_both_def)
  apply safe
     apply auto[1]
    apply (rule_tac x=p in exI)
  using can_take_transition_empty_guard accepts_gives_context apply fastforce
   apply (simp add: dirty_always_different_outputs_direct_subsumption_def)
  using always_different_outputs_direct_subsumption_def apply blast
  by (simp add: always_different_outputs_direct_subsumption_def dirty_always_different_outputs_direct_subsumption_def)

definition guard_subset_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "guard_subset_subsumption t1 t2 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> set (Guard t1) \<subseteq> set (Guard t2) \<and> Outputs t1 = Outputs t2 \<and> Updates t1 = Updates t2)"

lemma guard_subset_subsumption: "guard_subset_subsumption t1 t2 \<Longrightarrow> directly_subsumes a b s s' t1 t2"
  apply (rule subsumes_in_all_contexts_directly_subsumes)
  apply (simp add: guard_subset_subsumption_def)
  apply clarify
  apply (rule subsumption)
      apply simp
     apply (simp add: can_take_transition_def can_take_def apply_guards_def)
     apply auto[1]
    apply simp+
   apply (simp add: posterior_separate_def can_take_def apply_guards_def)
   apply auto[1]
  apply (simp add: posterior_def posterior_separate_def can_take_def apply_guards_def)
  by auto

lemma lob_distinguished_direct_subsumption:
  "always_different_outputs_direct_subsumption e1 e2 s s' t1 \<Longrightarrow>
   lob_distinguished t1 t2 \<Longrightarrow>
   \<not> directly_subsumes e1 e2 s s' t2 t1"
  apply (simp add: directly_subsumes_def always_different_outputs_direct_subsumption_def)
  apply (rule disjI1)
  apply (erule exE)
  apply (rule_tac x=p in exI)
  apply simp
  apply (case_tac "\<exists>c. anterior_context (tm e2) p = Some c")
   defer
   apply (simp add: accepts_trace_gives_context)
  apply (simp add: lob_distinguished_def)
  apply (erule exE)
  apply (rule_tac x=c in exI)
  apply simp
  apply (erule conjE)+
  using distinguishing_subsumption[of t2 t1]
  by simp

lemma lob_distinguished_2_direct_subsumption:
  "always_different_outputs_direct_subsumption e1 e2 s s' t2 \<Longrightarrow>
   lob_distinguished_2 t1 t2 \<Longrightarrow>
   \<not> directly_subsumes e1 e2 s s' t1 t2"
  apply (simp add: directly_subsumes_def always_different_outputs_direct_subsumption_def)
  apply (rule disjI1)
  apply (erule exE)
  apply (rule_tac x=p in exI)
  apply simp
  apply (case_tac "\<exists>c. anterior_context (tm e2) p = Some c")
   defer
   apply (simp add: accepts_trace_gives_context)
  apply (erule exE)
  apply (rule_tac x=c in exI)
  apply standard
   apply simp
  apply (rule bad_guards)
  apply clarify
  apply (case_tac "anterior_context (tm e2) p")
   apply simp
  apply (simp add: lob_distinguished_2_def Bex_def)
  apply clarify
  apply simp
  apply (case_tac "\<exists>x' \<in> set b. x \<noteq> x'")
   defer
   apply (simp add: must_be_another)
  apply (simp add: Bex_def)
  apply (erule exE)
  apply (rule_tac x="list_update i aa xa" in exI)
  apply standard
   apply (simp add: can_take_transition_def can_take_def another_swap_inputs)
  apply (simp add: can_take_transition_def can_take_def)
  by (metis Eq_apply_guards input2state_nth join_ir_def length_list_update nth_list_update_eq option.inject vname.simps(5))

lemma lob_distinguished_3_direct_subsumption:
  "always_different_outputs_direct_subsumption e1 e2 s s' t2 \<Longrightarrow>
   lob_distinguished_3 t1 t2 \<Longrightarrow>
   \<not> directly_subsumes e1 e2 s s' t1 t2"
  apply (simp add: directly_subsumes_def always_different_outputs_direct_subsumption_def)
  apply (rule disjI1)
  apply (erule exE)
  apply (erule conjE)+
  apply (case_tac "anterior_context (tm e2) p")
   apply (simp add: accepts_trace_anterior_not_none)
  apply (rule_tac x=p in exI)
  apply simp
  apply (erule exE)
  apply (simp add: lob_distinguished_3_def)
  using lob_distinguished_3_not_subsumes by blast

definition "guard_subset_eq_outputs_updates t1 t2 = (Label t1 = Label t2 \<and>
   Arity t1 = Arity t2 \<and>
   Outputs t1 = Outputs t2 \<and>
   Updates t1 = Updates t2 \<and>
   set (Guard t2) \<subseteq> set (Guard t1))"

definition "guard_superset_eq_outputs_updates t1 t2 = (Label t1 = Label t2 \<and>
   Arity t1 = Arity t2 \<and>
   Outputs t1 = Outputs t2 \<and>
   Updates t1 = Updates t2 \<and>
   set (Guard t2) \<supset> set (Guard t1))"

definition directly_subsumes_cases :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes_cases e1 e2 s1 s2 t1 t2 = (
    if t1 = t2
      then True
    else if simple_mutex t2 t1
      then False
    else if always_different_outputs (Outputs t1) (Outputs t2) \<and> always_different_outputs_direct_subsumption e1 e2 s1 s2 t2
      then False
    else if guard_subset_eq_outputs_updates t2 t1
      then True
    else if in_not_subset t1 t2
      then False
    else if opposite_gob t1 t2
      then False
    else if always_different_outputs_direct_subsumption e1 e2 s1 s2 t2 \<and> lob_distinguished_2 t1 t2
      then False
    else if always_different_outputs_direct_subsumption e1 e2 s1 s2 t2 \<and> lob_distinguished_3 t1 t2
      then False
    else if can_still_take e1 e2 s1 s2 t1 t2
      then True
    else if is_lob t2 t1
      then True
    else if drop_guard_add_update_direct_subsumption t1 t2 e2 s2
      then True
    else if drop_update_add_guard_direct_subsumption e1 e2 s1 s2 t1 t2
      then False
    else if generalise_output_direct_subsumption t1 t2 e1 e2 s1 s2
      then True
    else if diff_outputs_ctx e1 e2 s1 s2 t1 t2
      then False
    else if t1 = drop_guards t2
      then True
    else if one_extra_update t1 t2 s2 (tm e2)
      then True
    \<comment> \<open>else if t2 = drop_guards t1 \<and> satisfiable_negation t1
      then False\<close>
    else dirty_directly_subsumes e1 e2 s1 s2 t1 t2
  )"

lemma if_elim: "c \<longrightarrow> a = d \<Longrightarrow> \<not> c \<longrightarrow> d = b \<Longrightarrow> d = (if c then a else b)"
  by simp

lemma directly_subsumes_cases [code]:  "directly_subsumes m1 m2 s s' t1 t2 = directly_subsumes_cases m1 m2 s s' t1 t2"
  unfolding directly_subsumes_cases_def
  apply (rule if_elim)
   apply (simp add: directly_subsumes_self)
  apply (clarify, rule if_elim)
   apply (simp add: simple_mutex_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: always_different_outputs_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: guard_subset_eq_outputs_updates_def guard_subset_eq_outputs_updates_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: in_not_subset_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: opposite_gob_directly_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: lob_distinguished_2_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: lob_distinguished_3_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: can_still_take_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: is_lob_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: drop_guard_add_update_direct_subsumption_implies_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: drop_update_add_guard_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: generalise_output_directly_subsumes_original_executable)
  apply (clarify, rule if_elim)
   apply (simp add: diff_outputs_direct_subsumption)
  apply (clarify, rule if_elim)
   apply (simp add: drop_inputs_subsumption subsumes_in_all_contexts_directly_subsumes)
  apply (clarify, rule if_elim)
   apply (simp add: one_extra_update_direct_subsumption)
  by (simp add: dirty_directly_subsumes_def)

definition is_generalisation_of :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_generalisation_of t' t i r = (
    t' = remove_guard_add_update t i r \<and>
    i < Arity t \<and>
    r \<notin> set (map fst (Updates t)) \<and>
    (length (filter (tests_input_equality i) (Guard t)) \<ge> 1)
  )"

lemma tests_input_equality:
  "(\<exists>v. gexp.Eq (V (vname.I xb)) (L v) \<in> set G) = (1 \<le> length (filter (tests_input_equality xb) G))"
proof(induct G)
  case Nil
  then show ?case by simp
next
  case (Cons a G)
  then show ?case
    apply (cases a)
        apply simp
       apply simp
       apply (case_tac x21)
          apply simp
         apply simp
         apply (case_tac "x2 = vname.I xb")
          apply simp
          defer
          defer
          apply simp+
     apply (case_tac x22)
        apply auto[1]
       apply simp+
    apply (case_tac x22)
    using tests_input_equality.elims(2) by auto
qed
                                                                  
lemma [code]: "Store_Reuse.is_generalisation_of x xa xb xc = is_generalisation_of x xa xb xc"
  apply (simp add: Store_Reuse.is_generalisation_of_def is_generalisation_of_def)
  using tests_input_equality by blast

definition iEFSM2dot :: "iEFSM \<Rightarrow> nat \<Rightarrow> unit" where
  "iEFSM2dot _ _ = ()"

definition logStates :: "nat \<Rightarrow> nat \<Rightarrow> unit" where
  "logStates _ _ = ()"

(* This is the infer function but with logging *)
function infer_with_log :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "infer_with_log stepNo k e r m check np = (
    case inference_step e (rev (sorted_list_of_fset (k_score k e r))) m check np of
      None \<Rightarrow> e |
      Some new \<Rightarrow> let 
        temp = iEFSM2dot new stepNo;
        temp2 = logStates (size (S new)) (size (S e)) in
        if (S new) |\<subset>| (S e) then
          infer_with_log (stepNo + 1) k new r m check np
        else e
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(_, _, e, _). size (S e)]")
   apply simp
  using measures_fsubset by auto

declare make_pta.simps [code]
(* declare make_pta_fold [code] *)
declare GExp.satisfiable_def [code del]
declare initially_undefined_context_check_full_def [code del]
declare generalise_output_context_check_def [code del]
declare dirty_always_different_outputs_direct_subsumption_def [code del]
declare diff_outputs_ctx_def [code del]
declare random_member_def [code del]
declare dirty_directly_subsumes_def [code del]
declare accepts_and_gets_us_to_both_def [code del]
declare initially_undefined_context_check_def [code del]
declare can_still_take_ctx_def [code del]

code_printing
  constant accepts_and_gets_us_to_both \<rightharpoonup> (Scala) "Dirties.acceptsAndGetsUsToBoth" |
  constant iEFSM2dot \<rightharpoonup> (Scala) "PrettyPrinter.iEFSM2dot(_, _)" |
  constant logStates \<rightharpoonup> (Scala) "Log.logStates(_, _)" |
  constant "dirty_directly_subsumes" \<rightharpoonup> (Scala) "Dirties.scalaDirectlySubsumes" |
  constant "GExp.satisfiable" \<rightharpoonup> (Scala) "Dirties.satisfiable" |
  constant "initially_undefined_context_check_full" \<rightharpoonup> (Scala) "Dirties.initiallyUndefinedContextCheck" |
  constant "generalise_output_context_check" \<rightharpoonup> (Scala) "Dirties.generaliseOutputContextCheck" |
  constant "dirty_always_different_outputs_direct_subsumption" \<rightharpoonup> (Scala) "Dirties.alwaysDifferentOutputsDirectSubsumption" |
  constant "diff_outputs_ctx" \<rightharpoonup> (Scala) "Dirties.diffOutputsCtx" |
  constant "can_still_take" \<rightharpoonup> (Scala) "Dirties.canStillTake" |
  constant "random_member" \<rightharpoonup> (Scala) "Dirties.randomMember"

code_printing
  constant "show_nat" \<rightharpoonup> (Scala) "Code'_Numeral.integer'_of'_nat((_)).toString()"
  | constant "show_int" \<rightharpoonup> (Scala) "Code'_Numeral.integer'_of'_int((_)).toString()"
  | constant "join" \<rightharpoonup> (Scala) "_.mkString((_))"

(* I'd ideally like to fix this at some point *)
lemma [code]: "infer = infer_with_log 0"
  apply (simp add: fun_eq_iff)
  apply clarify
  unfolding Let_def add_0
  sorry

(*
  Mapping finfuns to Scala native Maps
*)
code_printing
  type_constructor finfun \<rightharpoonup> (Scala) "Map[_, _]"
  | constant "finfun_const" \<rightharpoonup> (Scala) "Map().withDefaultValue((_))"
  | constant "finfun_update" \<rightharpoonup> (Scala) "_ + (_ -> _)"
  | constant "finfun_apply" \<rightharpoonup> (Scala) "_((_))"
  | constant "finfun_to_list" \<rightharpoonup> (Scala) "_.keySet.toList"
declare finfun_to_list_const_code [code del]
declare finfun_to_list_update_code [code del]

lemma [code]: "satisfies_trace e s d l = satisfies_trace_prim e s d l"
  by (simp add: satisfies_trace_prim)

lemma [code]: "accepts e s d t = accepts_prim e s d t"
  by (simp add: accepts_prim)

(* declare make_branch.simps [code del] *)
(* code_printing constant "make_branch" \<rightharpoonup> (Scala) "Dirties.makeBranch" *)

declare startsWith_def [code del]
code_printing constant startsWith \<rightharpoonup> (Scala) "_.startsWith((_))"

declare endsWith_def [code del]
code_printing constant endsWith \<rightharpoonup> (Scala) "_.endsWith((_))"

declare dropRight_def [code del]
code_printing constant dropRight \<rightharpoonup> (Scala) "_.dropRight(Code'_Numeral.integer'_of'_nat((_)).toInt)"

declare substring_def [code del]
code_printing constant "substring" \<rightharpoonup> (Scala) "_.substring(Code'_Numeral.integer'_of'_nat((_)).toInt)"

declare parseInt_def [code del]
code_printing constant parseInt \<rightharpoonup> (Scala) "Int.int'_of'_integer(BigInt(_.toInt))"

definition "And = GExp.gAnd"

declare get_function_def [code del]
code_printing constant get_function \<rightharpoonup> (Scala) "Dirties.getFunction"

declare get_regs_def [code del]
code_printing constant get_regs \<rightharpoonup> (Scala) "Dirties.getRegs"

declare get_update_def [code del]
code_printing constant get_update \<rightharpoonup> (Scala) "Dirties.getUpdate"

export_code
  (* Essentials *)
  try_heuristics
  try_heuristics_check
  learn
  nondeterministic
  input_updates_register
  step
  maxS
  add_transition
  make_pta
  make_pta_abstract
  AExp.enumerate_vars
  sorted_list_of_set
  (* Scoring functions *)
  naive_score naive_score_eq
  naive_score_outputs
  naive_score_comprehensive
  naive_score_comprehensive_eq_high
  origin_states
  (* Heuristics *)
  drop_inputs
  same_register
  insert_increment_2
  heuristic_1
  heuristic_2
  transitionwise_drop_inputs
  lob
  gob
  gung_ho
  equals
  not_equals
  infer_output_functions
  infer_output_functions_2
  infer_output_update_functions
  distinguish
  historical_infer_output_update_functions
  (* Nondeterminism metrics *)
  nondeterministic_pairs
  nondeterministic_pairs_labar
  nondeterministic_pairs_labar_dest
  (* Utilities *)
  iefsm2dot
  efsm2dot
  guards2sal
  guards2sal_num
  fold_In
  max_int
  use_smallest_ints
  And
  enumerate_vars
in Scala
file "../../inference-tool/src/main/scala/inference/Inference.scala"

end