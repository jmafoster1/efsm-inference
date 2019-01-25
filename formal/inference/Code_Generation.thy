theory Code_Generation
  imports Inference "HOL-Library.Code_Target_Numeral" "../FSet_Utils" SelectionStrategies
begin

definition scalaChoiceAux :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "scalaChoiceAux t t' = False"

definition scalaNondeterministicSimulates :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "scalaNondeterministicSimulates a b c = False"

definition scalaDirectlySubsumes :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "scalaDirectlySubsumes a b c d e = False"

definition choice_aux :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice_aux t t' = (\<exists> s. apply_guards (Guard t) s \<and> apply_guards (Guard t') s)"

definition choice_code :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice_code t t' = ((Label t) = (Label t') \<and> (Arity t) = (Arity t') \<and> choice_aux t t')"

declare choice_aux_def [code del]
declare nondeterministic_simulates_def [code del]
declare directly_subsumes_def [code del]

code_printing
  constant "choice_aux" \<rightharpoonup> (Scala) "Dirties.scalaChoiceAux" |
  constant "nondeterministic_simulates" \<rightharpoonup> (Scala) "Dirties.scalaNondeterministicSimulates" |
  constant "directly_subsumes" \<rightharpoonup> (Scala) "Dirties.scalaDirectlySubsumes"

code_printing
  constant HOL.conj \<rightharpoonup> (Scala) "_ && _" |
  constant HOL.disj \<rightharpoonup> (Scala) "_ || _"

(*code_printing
  type_constructor prod \<rightharpoonup> (Scala) infix 2 "," |
  constant Pair \<rightharpoonup> (Scala) "!((_),/ (_))"*)

lemma [code]: "choice = choice_code"
  apply (rule ext)+
  by (simp add: choice_def choice_code_def choice_aux_def)

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

definition "show = String.implode"

export_code "show" String.explode String.implode naive_score null_generator null_modifier learn in Scala
  (* module_name "Inference"  *)
  file "../../inference-tool/src/main/scala/inference/Inference.scala"

end