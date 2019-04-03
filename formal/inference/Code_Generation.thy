theory Code_Generation
  imports 
   "HOL-Library.Code_Target_Numeral" Inference "../FSet_Utils" SelectionStrategies EFSM_Dot
   Type_Inference Enable_Logging
   "heuristics/Store_Reuse"
   "heuristics/Increment_Reset"
   "heuristics/Same_Register"
begin

declare One_nat_def [simp del]

declare GExp.satisfiable_def [code del]
declare directly_subsumes_def [code del]
declare choice_def [code del]

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
  apply (simp add: is_singleton_altdef One_nat_def)
  by (metis One_nat_def fis_singleton.transfer is_singleton_altdef)

fun guard_filter_code :: "nat \<Rightarrow> guard \<Rightarrow> bool" where
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

definition is_generalisation_of :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_generalisation_of t' t e i r = (\<exists>to \<in> fset (S e). \<exists> from \<in> fset (S e). \<exists> uid \<in> fset (uids e). t' = remove_guard_add_update t i r \<and> (uid, (from, to), t') |\<in>| e)"

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

lemma [code]:  "Store_Reuse.is_generalisation_of x xa xb xc xd = is_generalisation_of x xa xb xc xd"
  apply (simp add: is_generalisation_of_def Store_Reuse.is_generalisation_of_def)
  apply (case_tac "x = remove_guard_add_update xa xc xd")
   defer
   apply simp
  apply simp
  using to_in_S from_in_S uid_in_uids
  by (meson dest_from_in_S_uid_in_uids notin_fset)

lemma [code]: "Store_Reuse.is_generalised_output_of x xa xb xc xd = is_generalised_output_of x xa xb xc xd"
  apply (simp add: is_generalised_output_of_def Store_Reuse.is_generalised_output_of_def)
  apply (case_tac "x = generalise_output xa xc xd")
   defer
   apply simp
  apply simp
  using to_in_S from_in_S uid_in_uids
  by (meson dest_from_in_S_uid_in_uids notin_fset)

export_code is_proper_generalised_output_of is_proper_generalisation_of always_different_outputs try_heuristics learn same_register insert_increment insert_increment_2 nondeterministic finfun_apply infer_types heuristic_1 iefsm2dot efsm2dot naive_score null_modifier in Scala
  (* module_name "Inference" *)
  file "../../inference-tool/src/main/scala/inference/Inference.scala"

end