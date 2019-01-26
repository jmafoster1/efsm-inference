theory Code_Generation
  imports 
   "HOL-Library.Code_Target_Numeral" Inference "../FSet_Utils" SelectionStrategies EFSM_Dot
begin

definition scalaChoiceAux :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "scalaChoiceAux t t' = False"

definition scalaNondeterministicSimulates :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "scalaNondeterministicSimulates a b c = False"

definition scalaDirectlySubsumes :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "scalaDirectlySubsumes a b c d e = False"

declare GExp.satisfiable_def [code del]
declare nondeterministic_simulates_def [code del]
declare directly_subsumes_def [code del]

code_printing
  constant "GExp.satisfiable" \<rightharpoonup> (Scala) "Dirties.satisfiable" |
  constant "nondeterministic_simulates" \<rightharpoonup> (Scala) "Dirties.scalaNondeterministicSimulates" |
  constant "directly_subsumes" \<rightharpoonup> (Scala) "Dirties.scalaDirectlySubsumes"

code_printing
  constant HOL.conj \<rightharpoonup> (Scala) "_ && _" |
  constant HOL.disj \<rightharpoonup> (Scala) "_ || _"

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
    by simp
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

export_code efsm2dot GExp.conjoin String.explode String.implode naive_score null_generator null_modifier learn in Scala
  (* module_name "Inference" *)
  file "../../inference-tool/src/main/scala/inference/Inference.scala"

end