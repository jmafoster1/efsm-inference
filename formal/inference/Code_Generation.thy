theory Code_Generation
  imports 
   "HOL-Library.Code_Target_Numeral"
   Inference SelectionStrategies
   Type_Inference
   "heuristics/Store_Reuse_Subsumption"
   "heuristics/Increment_Reset"
   "heuristics/Same_Register"
   "heuristics/Ignore_Inputs"
begin

declare One_nat_def [simp del]

code_printing
  constant HOL.conj \<rightharpoonup> (Scala) "_ && _" |
  constant HOL.disj \<rightharpoonup> (Scala) "_ || _" |
  constant Cons \<rightharpoonup> (Scala) "_::_" |
  constant rev \<rightharpoonup> (Scala) "_.reverse" |
  constant List.member \<rightharpoonup> (Scala) "_ contains _" |
  constant "List.remdups" \<rightharpoonup> (Scala) "_.distinct" |
  constant "List.length" \<rightharpoonup> (Scala) "Nat.Nata(_.length)"

fun guard_filter_code :: "nat \<Rightarrow> gexp \<Rightarrow> bool" where
  "guard_filter_code inputX (gexp.Eq a b) = (a \<noteq> (V (vname.I inputX)) \<and> b \<noteq> (V (vname.I inputX)))" |
  "guard_filter_code _ _ = True"

lemma fold_conv_foldr: "fold f xs = foldr f (rev xs)"
  by (simp add: foldr_conv_fold)

lemma [code]: "choice t t' = ((Label t) = (Label t') \<and>
                      (Arity t) = (Arity t') \<and>
                      satisfiable ((fold gAnd (rev (Guard t@Guard t')) (gexp.Bc True))))"
  apply (simp only: fold_conv_foldr rev_rev_ident)
  unfolding satisfiable_def choice_def apply_guards_def
  apply (simp only: gval_foldr_true)
  by auto

code_pred satisfies_trace.

declare ListMem_iff [code]

fun guardMatch_alt :: "gexp list \<Rightarrow> gexp list \<Rightarrow> bool" where
  "guardMatch_alt [(gexp.Eq (V (vname.I i)) (L (Num n)))] [(gexp.Eq (V (vname.I i')) (L (Num n')))] = (i = 0 \<and> i' = 0)" |
  "guardMatch_alt _ _ = False"

lemma [code]: "guardMatch t1 t2 = guardMatch_alt (Guard t1) (Guard t2)"
  apply (simp add: guardMatch_def)
  using guardMatch_alt.elims(2) by fastforce

fun outputMatch_alt :: "output_function list \<Rightarrow> output_function list \<Rightarrow> bool" where
  "outputMatch_alt [L (Num n)] [L (Num n')] = True" |
  "outputMatch_alt _ _ = False"

lemma [code]: "outputMatch t1 t2 = outputMatch_alt (Outputs t1) (Outputs t2)"
  by (metis outputMatch_alt.elims(2) outputMatch_alt.simps(1) outputMatch_def)

fun always_different_outputs :: "aexp list \<Rightarrow> aexp list \<Rightarrow> bool" where
  "always_different_outputs [] [] = False" |
  "always_different_outputs [] (a#_) = True" |
  "always_different_outputs (a#_) [] = True" |
  "always_different_outputs ((L v)#t) ((L v')#t') = (if v = v' then always_different_outputs t t' else True)" |
  "always_different_outputs (h#t) (h'#t') = always_different_outputs t t'"

lemma always_different_outputs_outputs_never_equal: "always_different_outputs O1 O2 \<Longrightarrow> apply_outputs O1 s \<noteq> apply_outputs O2 s"
proof(induct O1 O2 rule: always_different_outputs.induct)
  case 1
  then show ?case
    by simp
next
  case (2 a uu)
  then show ?case
    by (simp add: apply_outputs_def)
next
  case (3 a uv)
  then show ?case
    by (simp add: apply_outputs_def)
next
  case (4 v t v' t')
  then show ?case
    by (simp add: apply_outputs_def)
next
  case ("5_1" v t h' t')
  then show ?case
    by (simp add: apply_outputs_def)
next
  case ("5_2" v va t h' t')
  then show ?case
    by (simp add: apply_outputs_def)
next
case ("5_3" v va t h' t')
  then show ?case
    by (simp add: apply_outputs_def)
next
  case ("5_4" h t v t')
  then show ?case
    by (simp add: apply_outputs_def)
next
  case ("5_5" h t v va t')
  then show ?case
    by (simp add: apply_outputs_def)
next
  case ("5_6" h t v va t')
  then show ?case
    by (simp add: apply_outputs_def)
qed

fun tests_input_equality :: "nat \<Rightarrow> gexp \<Rightarrow> bool" where
  "tests_input_equality i (gexp.Eq (V (vname.I i')) (L _)) = (i = i')" |
  "tests_input_equality _ _ = False"

definition is_generalised_output_of :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_generalised_output_of t' t e i r = (\<exists>to \<in> fset (S e). \<exists> from \<in> fset (S e). \<exists> uid \<in> fset (uids e). t' = generalise_output t i r \<and> (uid, (from, to), t') |\<in>| e)"

lemma to_in_S: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| xb \<longrightarrow> to |\<in>| S xb)"
  apply (simp add: S_def)
  by blast

lemma from_in_S: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| xb \<longrightarrow> from |\<in>| S xb)"
  apply (simp add: S_def)
  by blast

lemma uid_in_uids: "(\<exists>to from uid. (uid, (from, to), t) |\<in>| xb \<longrightarrow> uid |\<in>| uids xb)"
  apply (simp add: uids_def)
  by blast

(* definition "no_illegal_updates t r i = (\<forall>i. \<forall>u \<in> set (Updates t). fst u \<noteq> (R r) \<and> fst u \<noteq> (I i))" *)
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

definition random_member :: "'a fset \<Rightarrow> 'a option" where
  "random_member f = (if f = {||} then None else Some (Eps (\<lambda>x. x |\<in>| f)))"

definition step :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> outputs \<times> registers) option" where
"step e s r l i = (let possibilities = possible_steps e s r l i in
                   if possibilities = {||} then None
                   else
                     case random_member possibilities of
                     None \<Rightarrow> None |
                     Some (s', t) \<Rightarrow>
                     Some (t, s', (EFSM.apply_outputs (Outputs t) (join_ir i r)), (EFSM.apply_updates (Updates t) (join_ir i r) r))
                  )"

lemma [code]: "EFSM.step x xa xb xc xd = step x xa xb xc xd"
  by (simp add: EFSM.step_def step_def Let_def random_member_def)

declare random_member_def [code del]

code_printing constant "random_member" \<rightharpoonup> (Scala) "Dirties.randomMember"

fun input_updates_register_aux :: "update_function list \<Rightarrow> nat option" where
  "input_updates_register_aux ((n, V (vname.I n'))#_) = Some n'" |
  "input_updates_register_aux (h#t) = input_updates_register_aux t" |
  "input_updates_register_aux [] = None"

definition input_updates_register :: "iEFSM \<Rightarrow> (nat \<times> String.literal)" where
  "input_updates_register e = (case fthe_elem (ffilter (\<lambda>(_, _, t). input_updates_register_aux (Updates t) \<noteq> None) e) of (_, _, t) \<Rightarrow> case input_updates_register_aux (Updates t) of Some n \<Rightarrow> (n, Label t))"

definition "dirty_directly_subsumes = directly_subsumes"
declare dirty_directly_subsumes_def [code del]
code_printing constant "dirty_directly_subsumes" \<rightharpoonup> (Scala) "Dirties.scalaDirectlySubsumes"

definition always_different_outputs_direct_subsumption ::"iEFSM \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
"always_different_outputs_direct_subsumption m1 m2 s s' t1 t2 = (
   (\<exists>p. accepts (tm m1) 0 Map.empty p \<and>
    gets_us_to s (tm m1) 0 Map.empty p \<and>
    accepts (tm m2) 0 Map.empty p \<and>
    gets_us_to s' (tm m2) 0 Map.empty p \<and>
    (\<forall>c. anterior_context (tm m2) p = Some c \<longrightarrow> (\<exists>i. can_take t2 i c))))"

lemma always_different_outputs_can_take_not_subsumed: "always_different_outputs (Outputs t1) (Outputs t2) \<Longrightarrow>
       \<forall>c. posterior_sequence (tm m2) 0 Map.empty p = Some c \<longrightarrow> (\<exists>i. can_take t2 i c) \<longrightarrow> \<not> subsumes t1 c t2"
  apply standard
  apply standard
  apply standard
  apply (rule bad_outputs)
  using always_different_outputs_outputs_never_equal
  by metis

lemma always_different_outputs_direct_subsumption: 
  "always_different_outputs (Outputs t1) (Outputs t2) \<and> always_different_outputs_direct_subsumption m1 m2 s s' t1 t2 \<Longrightarrow> \<not> directly_subsumes m1 m2 s s' t1 t2"
  apply (simp add: directly_subsumes_def always_different_outputs_direct_subsumption_def)
  apply standard
  apply clarify
  apply (rule_tac x=p in exI)
  apply simp
  using always_different_outputs_can_take_not_subsumed accepts_trace_gives_context
  by (meson accepts_gives_context)

definition directly_subsumes_cases :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes_cases a b s s' t1 t2 = (
    if t1 = t2
      then True
    else if always_different_outputs (Outputs t1) (Outputs t2) \<and> always_different_outputs_direct_subsumption a b s s' t1 t2
      then False
    else if drop_guard_add_update_direct_subsumption t1 t2 b s'
      then True
    else if generalise_output_direct_subsumption t1 t2 b a s s'
      then True
    else dirty_directly_subsumes a b s s' t1 t2
  )"

lemma [code]: "directly_subsumes m1 m2 s s' t1 t2 = directly_subsumes_cases m1 m2 s s' t1 t2"
  unfolding directly_subsumes_cases_def
  apply (case_tac "t1 = t2")
   apply (simp add: directly_subsumes_self)
  apply (case_tac "always_different_outputs_direct_subsumption a b s s' t1 t2")
  apply (simp add: always_different_outputs_direct_subsumption dirty_directly_subsumes_def drop_guard_add_update_direct_subsumption_implies_direct_subsumption generalise_output_directly_subsumes_original_executable)
  apply (case_tac "drop_guard_add_update_direct_subsumption t1 t2 m2 s'")
  apply (meson always_different_outputs_direct_subsumption drop_guard_add_update_direct_subsumption_implies_direct_subsumption)
  apply (case_tac "generalise_output_direct_subsumption t1 t2 m2 m1 s s'")
   apply (meson always_different_outputs_direct_subsumption generalise_output_directly_subsumes_original_executable)
  by (simp add: always_different_outputs_direct_subsumption dirty_directly_subsumes_def)

definition is_generalisation_of :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_generalisation_of t' t i r = (t' = remove_guard_add_update t i r \<and>
                                    i < Arity t \<and>
                                    r \<notin> set (map fst (Updates t)) \<and>
                                    (length (filter (tests_input_equality i) (Guard t)) \<ge> 1))"

lemma tests_input_equality: "(\<exists>v. gexp.Eq (V (vname.I xb)) (L v) \<in> set G) = (1 \<le> length (filter (tests_input_equality xb) G))"
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
                                                                  
lemma[code]: "Store_Reuse.is_generalisation_of x xa xb xc = is_generalisation_of x xa xb xc"
  apply (simp add: Store_Reuse.is_generalisation_of_def is_generalisation_of_def)
  using tests_input_equality by blast

declare GExp.satisfiable_def [code del]
declare initially_undefined_context_check_def [code del]
declare generalise_output_context_check_def [code del]
declare always_different_outputs_direct_subsumption_def [code del]

code_printing
  constant "GExp.satisfiable" \<rightharpoonup> (Scala) "Dirties.satisfiable" |
  constant "initially_undefined_context_check" \<rightharpoonup> (Scala) "Dirties.initiallyUndefinedContextCheck" |
  constant "generalise_output_context_check" \<rightharpoonup> (Scala) "Dirties.generaliseOutputContextCheck" |
  constant "always_different_outputs_direct_subsumption" \<rightharpoonup> (Scala) "Dirties.alwaysDifferentOutputsDirectSubsumption"

(* Use the native implementations of list functions *)
definition "flatmap l f = List.maps f l"

lemma [code]:"List.maps f l = flatmap l f"
  by (simp add: flatmap_def)

definition map :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b list" where
  "map l f = List.map f l"

lemma [code]:"List.map f l = map l f"
  by (simp add: map_def)

declare foldl_conv_fold [code]
declare foldr_conv_foldl [code]
declare map_filter_map_filter [code_unfold del]

lemma [code]: "removeAll a l = filter (\<lambda>x. x \<noteq> a) l"
  by (induct l arbitrary: a) simp_all

definition filter :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list" where
  "filter l f = List.filter f l"

declare filter.simps [code del]
lemma [code]: "List.filter l f = filter f l"
  by (simp add: filter_def)

definition all :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "all l f = list_all f l"

lemma [code]: "list_all f l = all l f"
  by (simp add: all_def)

code_printing
  constant "zip" \<rightharpoonup> (Scala) "(_ zip _)" |
  constant "flatmap" \<rightharpoonup> (Scala) "_.flatMap((_))" |
  constant "List.null" \<rightharpoonup> (Scala) "_.isEmpty" |
  constant "map" \<rightharpoonup> (Scala) "_.map((_))" |
  constant "filter" \<rightharpoonup> (Scala) "_.filter((_))" |
  constant "all" \<rightharpoonup> (Scala) "_.forall((_))"

export_code try_heuristics aexp_type_check learn drop_inputs same_register input_updates_register insert_increment_2 nondeterministic finfun_apply infer_types heuristic_1 naive_score in Scala
  file "../../inference-tool/src/main/scala/inference/Inference.scala"

end