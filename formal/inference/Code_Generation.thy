theory Code_Generation
  imports 
   "HOL-Library.Code_Target_Numeral" Inference "../FSet_Utils" SelectionStrategies EFSM_Dot
   Type_Inference
   Trace_Matches
begin

definition scalaChoiceAux :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "scalaChoiceAux t t' = False"

definition scalaNondeterministicSimulates :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "scalaNondeterministicSimulates a b c = False"

definition scalaDirectlySubsumes :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "scalaDirectlySubsumes a b c d e = False"

declare GExp.satisfiable_def [code del]
declare directly_subsumes_def [code del]

declare consistent_def [code del]
declare CExp.satisfiable_def [code del]
declare CExp.valid_def [code del]

code_printing
  constant "GExp.satisfiable" \<rightharpoonup> (Scala) "Dirties.satisfiable" |
  constant "directly_subsumes" \<rightharpoonup> (Scala) "Dirties.scalaDirectlySubsumes"

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

lemma [code]: "step e s r l i = (if size (possible_steps e s r l i) = 1 then (
                     let (s', t) = (fthe_elem (possible_steps e s r l i)) in
                     Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (EFSM.apply_updates (Updates t) (join_ir i r) r))
                   )
                   else None)"
  apply (simp add: step_def)
  apply (simp add: is_singleton_altdef)
  by (metis One_nat_def fis_singleton.transfer is_singleton_altdef)

lemma [code]: "nondeterministic_step e s r l i = (
  if possible_steps e s r l i \<noteq> {||} then (
    let (s', t) =  (Eps (\<lambda>x. x |\<in>| (possible_steps e s r l i))) in
    Some (t, s', (EFSM.apply_outputs (Outputs t) (join_ir i r)), (EFSM.apply_updates (Updates t) (join_ir i r) r)))
  else None)"
  apply (simp add: nondeterministic_step_def)
  by auto

lemma apply_guards_equals_conjoin: "apply_guards g s = (gval (GExp.conjoin g) s = Some True)"
proof(induct g)
  case Nil
  then show ?case
    by (simp add: gval.simps)
next
  case (Cons a g)
  then show ?case
    apply simp
    apply (case_tac "gval a s")
     apply simp
    apply simp
    apply (case_tac "gval (GExp.conjoin g) s")
     apply simp
    by simp
qed

lemma [code]: "(choice t1 t2) = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> GExp.satisfiable (gAnd (GExp.conjoin (Guard t1)) (GExp.conjoin (Guard t2))))"
  apply (simp add: choice_def GExp.satisfiable_def)
  apply safe
   apply (rule_tac x=s in exI)
   apply (simp add: apply_guards_equals_conjoin)
  apply (rule_tac x=s in exI)
  apply (case_tac "gval (GExp.conjoin (Guard t1)) s")
   apply (simp add: apply_guards_equals_conjoin)
  apply (case_tac "gval (GExp.conjoin (Guard t2)) s")
  apply (simp add: apply_guards_equals_conjoin)
  by (simp add: apply_guards_equals_conjoin)

fun guard_filter_code :: "nat \<Rightarrow> guard \<Rightarrow> bool" where
  "guard_filter_code inputX (gexp.Eq a b) = (a \<noteq> (V (I inputX)) \<and> b \<noteq> (V (I inputX)))" |
  "guard_filter_code _ _ = True"

lemma[code]: "guard_filter = guard_filter_code"
  unfolding guard_filter_def
  apply (rule ext)+
  apply (case_tac g)
  prefer 2
    apply (case_tac "x21 = (V (I inputX))")
     apply auto[1]
    apply (case_tac "x22 = (V (I inputX))")
  by auto

lemma[code]: "leaves uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. (fst x = uid)) t))))"
  by (simp only: leaves_def exists_is_fst)

lemma[code]: "arrives uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. (fst x = uid)) t))))"
  by (simp only: arrives_def exists_is_fst)

code_pred satisfies_trace.

declare ListMem_iff [code]

primrec ran :: "nat \<Rightarrow> nat set" where
  "ran 0 = {0}" |
  "ran (Suc n) = insert (Suc n) (ran n)"

lemma "i \<in> ran n = (i \<le> n)"
proof(induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    by auto
qed

definition is_generalisation_of :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> bool" where
  "is_generalisation_of t' t e = (\<exists>i \<in> (ran (max_input e)).
                                  \<exists>r \<in> (ran (max_reg e)).
                                  \<exists>to \<in> fset (S e).
                                  \<exists>from \<in> fset (S e).
                                  \<exists>uid \<in> fset (uids e).  i < max_reg e \<and> from |\<in>| S e \<and>  t' = remove_guard_add_update t i r \<and> (uid, (from, to), t') |\<in>| e)"


export_code is_generalisation_of iterative_learn finfun_apply infer_types heuristic_1 iefsm2dot efsm2dot GExp.conjoin naive_score null_generator null_modifier nondeterministic learn in Scala
  (* module_name "Inference" *)
  file "../../inference-tool/src/main/scala/inference/Inference.scala"

end