theory Code_Generation
  imports 
   "HOL-Library.Code_Target_Numeral" Inference "../FSet_Utils" SelectionStrategies EFSM_Dot
   Type_Inference Enable_Logging
   "heuristics/Store_Reuse_Subsumption"
   "heuristics/Increment_Reset"
   "heuristics/Same_Register"
begin

declare One_nat_def [simp del]

declare GExp.satisfiable_def [code del]
declare choice_def [code del]

declare consistent_def [code del]
declare CExp.satisfiable_def [code del]
declare CExp.valid_def [code del]
declare initially_undefined_context_check_def [code del]
declare generalise_output_context_check_def [code del]
declare Ii_true_def [code del]

code_printing
  constant "GExp.satisfiable" \<rightharpoonup> (Scala) "Dirties.satisfiable" |
  constant "initially_undefined_context_check" \<rightharpoonup> (Scala) "Dirties.initiallyUndefinedContextCheck" |
  constant "generalise_output_context_check" \<rightharpoonup> (Scala) "Dirties.generaliseOutputContextCheck" |
  constant "Ii_true" \<rightharpoonup> (Scala) "Dirties.IiTrue"

code_printing
  constant HOL.conj \<rightharpoonup> (Scala) "_ && _" |
  constant HOL.disj \<rightharpoonup> (Scala) "_ || _" |
  constant Cons \<rightharpoonup> (Scala) "_::_" |
  constant rev \<rightharpoonup> (Scala) "_.reverse" |
  constant List.member \<rightharpoonup> (Scala) "_ contains _" |
  constant "List.remdups" \<rightharpoonup> (Scala) "_.distinct" |
  constant "List.length" \<rightharpoonup> (Scala) "Nat.Nata(_.length)"

(*code_printing
  type_constructor prod \<rightharpoonup> (Scala) infix 2 "," |
  constant Pair \<rightharpoonup> (Scala) "!((_),/ (_))"*)

(* lemma [code]: "step e s r l i = (if size (possible_steps e s r l i) = 1 then ( *)
                     (* let (s', t) = (fthe_elem (possible_steps e s r l i)) in *)
                     (* Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (EFSM.apply_updates (Updates t) (join_ir i r) r)) *)
                   (* ) *)
                   (* else None)" *)
  (* apply (simp add: step_def) *)
  (* apply (simp add: is_singleton_altdef One_nat_def) *)
  (* by (metis One_nat_def fis_singleton.transfer is_singleton_altdef) *)

fun guard_filter_code :: "nat \<Rightarrow> gexp \<Rightarrow> bool" where
  "guard_filter_code inputX (gexp.Eq a b) = (a \<noteq> (V (I inputX)) \<and> b \<noteq> (V (I inputX)))" |
  "guard_filter_code _ _ = True"

lemma[code]: "origin uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. (fst x = uid)) t))))"
  by (simp only: origin_def exists_is_fst)

lemma[code]: "dest uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. (fst x = uid)) t))))"
  by (simp only: dest_def exists_is_fst)

lemma gval_fold: "(gval (fold gAnd G (gexp.Bc True)) s = true) = (\<forall>g\<in>set (map (\<lambda>g. gval g s) G). g = true)"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: gval.simps)
next
  case (snoc x xs)
  then show ?case
    by (simp add: gval_gAnd_True)
qed

lemma choice_aux: "(\<exists>s. apply_guards G s \<and> apply_guards G' s) = GExp.satisfiable ((fold gAnd (G@G') (gexp.Bc True)))"
  apply (simp only: GExp.satisfiable_def gval_fold apply_guards_alt)
  by auto

lemma [code]: "choice t t' = ((Label t) = (Label t') \<and>
                      (Arity t) = (Arity t') \<and>
                      GExp.satisfiable ((fold gAnd (Guard t@Guard t') (gexp.Bc True))))"
  unfolding choice_def
  using choice_aux
  by blast

code_pred satisfies_trace.

declare ListMem_iff [code]

fun guardMatch_alt :: "gexp list \<Rightarrow> gexp list \<Rightarrow> bool" where
  "guardMatch_alt [(gexp.Eq (V (I i)) (L (Num n)))] [(gexp.Eq (V (I i')) (L (Num n')))] = (i = 1 \<and> i' = 1)" |
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

lemma aux1: "h # t = Outputs t1 \<Longrightarrow>
      Minus v va # t' = Outputs t2 \<Longrightarrow>
      always_different_outputs (Outputs t1) (Outputs t2) =  always_different_outputs t t'"
  by (metis always_different_outputs.simps(10))

lemma always_different_outputs: "always_different_outputs o1 o2 \<Longrightarrow>
    \<forall>i r. apply_outputs o1 (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
          apply_outputs o2 (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n)))"
  by (induct o1 o2 rule: always_different_outputs.induct, auto)
                                                                  
lemma outputs_never_equal_no_subsumption: "always_different_outputs (Outputs t1) (Outputs t2) \<Longrightarrow> \<not>subsumes t1 c t2"
  by (metis outputs_never_equal join_ir_def always_different_outputs)

fun tests_input_equality :: "nat \<Rightarrow> gexp \<Rightarrow> bool" where
  "tests_input_equality i (gexp.Eq (V (I i')) (L _)) = (i = i')" |
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
  "no_illegal_updates_code ((I _, u)#t) r = False" |
  "no_illegal_updates_code ((R r', u)#t) r = (r \<noteq> r' \<and> no_illegal_updates_code t r)"

lemma no_illegal_updates_code_aux: "(\<forall>i. \<forall>u\<in>set u. fst u \<noteq> R r \<and> fst u \<noteq> I i) = no_illegal_updates_code u r"
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

definition step :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> outputs \<times> datastate) option" where
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
  "input_updates_register_aux ((R n, V (I n'))#_) = Some n'" |
  "input_updates_register_aux (h#t) = input_updates_register_aux t" |
  "input_updates_register_aux [] = None"

definition input_updates_register :: "iEFSM \<Rightarrow> (nat \<times> String.literal)" where
  "input_updates_register e = (case fthe_elem (ffilter (\<lambda>(_, _, t). input_updates_register_aux (Updates t) \<noteq> None) e) of (_, _, t) \<Rightarrow> case input_updates_register_aux (Updates t) of Some n \<Rightarrow> (n, Label t))"

definition "dirty_directly_subsumes = directly_subsumes"
declare dirty_directly_subsumes_def [code del]
code_printing constant "dirty_directly_subsumes" \<rightharpoonup> (Scala) "Dirties.scalaDirectlySubsumes"

definition directly_subsumes_cases :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "directly_subsumes_cases a b s s' t1 t2 = (
    if t1 = t2
      then True
    else if always_different_outputs (Outputs t1) (Outputs t2)
      then False
    else if drop_guard_add_update_direct_subsumption t1 t2 b s'
      then True
    else if generalise_output_direct_subsumption t1 t2 b a s s'
      then True
    else if original_doesnt_directly_subsume_generalised_prems a b s s' t1 t2
      then False
    else dirty_directly_subsumes a b s s' t1 t2
  )"

lemma [code]: "directly_subsumes a b s s' t1 t2 = directly_subsumes_cases a b s s' t1 t2"
  unfolding directly_subsumes_cases_def
  apply (case_tac "t1 = t2")
   apply (simp add: directly_subsumes_self)
  apply (case_tac "always_different_outputs (Outputs t1) (Outputs t2)")
   apply (simp add: cant_directly_subsume outputs_never_equal_no_subsumption)
  apply (case_tac "drop_guard_add_update_direct_subsumption t1 t2 b s'")
   apply (simp add: drop_guard_add_update_direct_subsumption_implies_direct_subsumption)
  apply (case_tac "generalise_output_direct_subsumption t1 t2 b a s s'")
   apply (simp add: generalise_output_directly_subsumes_original_executable)
  apply (case_tac "original_doesnt_directly_subsume_generalised_prems a b s s' t1 t2")
   apply simp
   apply (case_tac "stored_reused t1 t2 b")
    apply (simp add: original_doesnt_directly_subsume_generalised)
   apply (case_tac aa)
   apply (simp add: original_doesnt_directly_subsume_generalised)
  by (simp add: dirty_directly_subsumes_def)

definition is_generalisation_of :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_generalisation_of t' t i r = (t' = remove_guard_add_update t i r \<and> (length (filter (tests_input_equality i) (Guard t)) \<ge> 1))"

lemma tests_input_equality: "(\<exists>v. gexp.Eq (V (I xb)) (L v) \<in> set G) = (1 \<le> length (filter (tests_input_equality xb) G))"
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
         apply (case_tac "x2 = I xb")
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
  by (simp add: tests_input_equality)

export_code try_heuristics learn same_register input_updates_register insert_increment_2 nondeterministic finfun_apply infer_types heuristic_1 iefsm2dot efsm2dot naive_score in Scala
  file "../../inference-tool/src/main/scala/inference/Inference.scala"

end