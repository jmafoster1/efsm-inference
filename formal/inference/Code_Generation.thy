theory Code_Generation
  imports 
   "HOL-Library.Code_Target_Numeral" Inference "../FSet_Utils" SelectionStrategies EFSM_Dot
   Type_Inference
   Trace_Matches
   Increment_Reset
   Same_Register
begin

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
  apply (simp add: is_singleton_altdef)
  by (metis One_nat_def fis_singleton.transfer is_singleton_altdef)

fun guard_filter_code :: "nat \<Rightarrow> guard \<Rightarrow> bool" where
  "guard_filter_code inputX (gexp.Eq a b) = (a \<noteq> (V (I inputX)) \<and> b \<noteq> (V (I inputX)))" |
  "guard_filter_code _ _ = True"

lemma[code]: "leaves uid t = fst (fst (snd (fthe_elem (ffilter (\<lambda>x. (fst x = uid)) t))))"
  by (simp only: leaves_def exists_is_fst)

lemma[code]: "arrives uid t = snd (fst (snd (fthe_elem (ffilter (\<lambda>x. (fst x = uid)) t))))"
  by (simp only: arrives_def exists_is_fst)

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
  using One_nat_def guardMatch_alt.elims(2) by fastforce

fun outputMatch_alt :: "output_function list \<Rightarrow> output_function list \<Rightarrow> bool" where
  "outputMatch_alt [L (Num n)] [L (Num n')] = True" |
  "outputMatch_alt _ _ = False"

lemma [code]: "outputMatch t1 t2 = outputMatch_alt (Outputs t1) (Outputs t2)"
  by (metis outputMatch_alt.elims(2) outputMatch_alt.simps(1) outputMatch_def)

definition writeiDot :: "iEFSM \<Rightarrow> String.literal \<Rightarrow> unit" where
  "writeiDot i s = ()"

definition "timestamp = STR ''''"

definition merge_and_print :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "merge_and_print x y t = (let merged = (if x > y then merge_states_aux x y t else merge_states_aux y x t);
                                print = (writeiDot merged (STR ''dotfiles/log/''+timestamp+STR ''.dot'')) in merged)"

lemma merge_and_print: "merge_states = merge_and_print"
  apply (rule ext)+
  by (simp add: merge_states_def merge_and_print_def)

primrec iterative_try_heuristics_print :: "(log \<Rightarrow> update_modifier) list \<Rightarrow> log \<Rightarrow> update_modifier" where
  "iterative_try_heuristics_print [] l = null_modifier" |
  "iterative_try_heuristics_print (h#t) l = (\<lambda>a b c d e. case (h l) a b c d e of None \<Rightarrow> iterative_try_heuristics_print t l a b c d e |
                                            Some e' \<Rightarrow> let print = (writeiDot e' (STR ''dotfiles/log/''+timestamp+STR ''.dot'')) in Some e')"

lemma try_and_print: "iterative_try_heuristics h l = iterative_try_heuristics_print h l"
proof(induct h)
  case Nil
  then show ?case by simp
next
  case (Cons a h)
  then show ?case
    apply simp
    by metis
qed

code_printing
  constant "writeiDot" \<rightharpoonup> (Scala) "Dirties.writeiDot" |
  constant "timestamp" \<rightharpoonup> (Scala) "System.currentTimeMillis.toString"

fun resolve_nondeterminism :: "nondeterministic_pair list \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM option" where
  "resolve_nondeterminism [] _ new _ check = (if deterministic new \<and> check (tm new) then Some new else None)" |
  "resolve_nondeterminism ((from, (to1, to2), ((t1, u1), (t2, u2)))#ss) oldEFSM newEFSM m check = (let
     destMerge = (merge_states (arrives u1 newEFSM) (arrives u2 newEFSM) newEFSM);
     t1FromOld = leaves u1 oldEFSM;
     t2FromOld = leaves u2 oldEFSM;
     newFrom = leaves u1 destMerge;
     t1NewTo = arrives u1 destMerge;
     t2NewTo = arrives u2 destMerge in 
     case Inference.make_distinct (merge_transitions oldEFSM destMerge t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1 u1 t2 u2 m) of
       None \<Rightarrow> resolve_nondeterminism ss oldEFSM newEFSM m check |
      \<^cancel>\<open>we get rid of the rev here so we resolve nondeterminism forwards in the machine\<close>
       Some new \<Rightarrow> 
         let newScores = (\<^cancel>\<open>rev\<close> (sorted_list_of_fset (nondeterministic_pairs new)))
              in (
         if length newScores < (length ss) + 1 then
           case resolve_nondeterminism newScores oldEFSM new m check of
             Some new' \<Rightarrow> Some new' |
             None \<Rightarrow> resolve_nondeterminism ss oldEFSM newEFSM m check
         else 
           let t = timestamp;
               p = writeiDot new (STR ''dotfiles/log/''+t+STR ''-new.dot'') ;
               p' = print (STR ''Failed to reduce nondeterminism '' + (show_nat (length newScores)) + STR '' > '' + (show_nat ((length ss) + 1))) ;
               p'' = writeiDot newEFSM (STR ''dotfiles/log/''+t+STR ''.dot'') in
           None
       )
   )"

lemma resolve_and_print: "Inference.resolve_nondeterminism = Code_Generation.resolve_nondeterminism"
  sorry

declare resolve_and_print [code]
declare Inference.resolve_nondeterminism.simps [code del]

export_code try_heuristics learn same_register insert_increment nondeterministic finfun_apply infer_types heuristic_1 iefsm2dot efsm2dot naive_score null_modifier in Scala
  (* module_name "Inference" *)
  file "../../inference-tool/src/main/scala/inference/Inference.scala"

lemma "iterative_learn [] naive_score (iterative_try_heuristics [(\<lambda>x. insert_increment), (\<lambda>x. heuristic_1 x)]) = {||}"
  by (simp add: iterative_learn_def tm_def)

end