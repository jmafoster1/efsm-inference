theory Distinguishing_Guards
imports "../Inference"
begin

hide_const uids

definition put_updates :: "tids \<Rightarrow> update_function list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "put_updates uids updates iefsm = fimage (\<lambda>(uid, fromTo, tran).
      case uid of [u] \<Rightarrow>
      if u \<in> set uids then
        (uid, fromTo, \<lparr>Label = Label tran, Arity = Arity tran, Guard = Guard tran, Outputs = Outputs tran, Updates = (Updates tran)@updates\<rparr>)
      else
        (uid, fromTo, tran)
      ) iefsm"

definition transfer_updates :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "transfer_updates e pta = fold (\<lambda>(tids, (from, to), tran) acc. put_updates tids (Updates tran) acc) (sorted_list_of_fset e) pta"

fun trace_collect_training_sets :: "execution \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> tids \<Rightarrow> tids \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> ((inputs \<times> registers) list \<times> (inputs \<times> registers) list)" where
  "trace_collect_training_sets [] uPTA s registers T1 T2 G1 G2 = (G1, G2)" |
  "trace_collect_training_sets ((label, inputs, outputs)#t) uPTA s registers T1 T2 G1 G2 = (
    let
      (uids, s', tran) = fthe_elem (ffilter (\<lambda>(uids, s', tran). apply_outputs (Outputs tran) (join_ir inputs registers) = map Some outputs) (i_possible_steps uPTA s registers label inputs));
      updated = (apply_updates (Updates tran) (join_ir inputs registers) registers)
    in
    if hd uids \<in> set T1 then
      trace_collect_training_sets t uPTA s' updated T1 T2 ((inputs, registers)#G1) G2
    else if hd uids \<in> set T2 then
      trace_collect_training_sets t uPTA s' updated T1 T2 G1 ((inputs, registers)#G2)
    else
      trace_collect_training_sets t uPTA s' updated T1 T2 G1 G2
  )"

primrec collect_training_sets :: "log \<Rightarrow> iEFSM \<Rightarrow> tids \<Rightarrow> tids \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> ((inputs \<times> registers) list \<times> (inputs \<times> registers) list)" where
  "collect_training_sets [] uPTA T1 T2 G1 G2 = (G1, G2)" |
  "collect_training_sets (h#t) uPTA T1 T2 G1 G2 = (
    let (G1a, G2a) = trace_collect_training_sets h uPTA 0 <> T1 T2 [] [] in
    collect_training_sets t uPTA T1 T2 (List.union G1 G1a) (List.union G2 G2a)
  )"

definition find_distinguishing_guards :: "(inputs \<times> registers) list \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> (vname gexp \<times> vname gexp) option" where
  "find_distinguishing_guards G1 G2 = (
    let gs = {(g1, g2).
      (\<forall>(i, r) \<in> set G1. gval g1 (join_ir i r) = true) \<and>
      (\<forall>(i, r) \<in> set G2. gval g2 (join_ir i r) = true) \<and>
      (\<forall>i r. \<not> (gval g1 (join_ir i r) = true \<and> gval g2 (join_ir i r) = true))
    } in
    if gs = {} then None else Some (Eps (\<lambda>g. g \<in> gs))
  )"
declare find_distinguishing_guards_def [code del]
code_printing constant find_distinguishing_guards \<rightharpoonup> (Scala) "Dirties.findDistinguishingGuard"

definition add_guard :: "transition \<Rightarrow> vname gexp \<Rightarrow> transition" where
  "add_guard t g = \<lparr>Label = Label t, Arity = Arity t, Guard = g#(Guard t), Outputs = Outputs t, Updates = Updates t\<rparr>"

definition distinguish :: "log \<Rightarrow> update_modifier" where
  "distinguish log t1ID t2ID s destMerge preDestMerge old np = (
    let
      t1 = get_by_ids destMerge t1ID;
      t2 = get_by_ids destMerge t2ID;
      uPTA = transfer_updates destMerge (make_pta log);
      (G1, G2) = collect_training_sets log uPTA t1ID t2ID [] []
    in
      case find_distinguishing_guards G1 G2 of
        None \<Rightarrow> None |
        Some (g1, g2) \<Rightarrow> (
          let newEFSM = replace_transitions preDestMerge [(t1ID, add_guard t1 g1), (t2ID, add_guard t2 g2)]
          in
          resolve_nondeterminism [] (sorted_list_of_fset (np newEFSM)) old newEFSM null_modifier (\<lambda>a. True) np
        )
  )"

definition can_still_take_ctx :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "can_still_take_ctx e1 e2 s1 s2 t1 t2 = (
    \<forall>t. accepts_trace e1 t \<and> gets_us_to s1 e1 0 <> t \<and>  accepts_trace e2 t \<and> gets_us_to s2 e2 0 <> t \<longrightarrow>
    (\<exists>a. anterior_context e2 t = Some a \<and> (\<forall>i. can_take_transition t2 i a \<longrightarrow> can_take_transition t1 i a))
  )"

lemma distinguishing_guard_subsumption:
"Label t1 = Label t2 \<Longrightarrow>
 Arity t1 = Arity t2 \<Longrightarrow>
 Outputs t1 = Outputs t2 \<Longrightarrow>
 Updates t1 = Updates t2 \<Longrightarrow>
 can_still_take_ctx (tm e1) (tm e2) s1 s2 t1 t2 \<Longrightarrow>
 accepts_and_gets_us_to_both e1 e2 s1 s2 \<Longrightarrow>
 accepts_trace (tm e1) p \<Longrightarrow>
 gets_us_to s1 (tm e1) 0 <> p \<Longrightarrow>
 accepts_trace (tm e2) p \<Longrightarrow>
 gets_us_to s2 (tm e2) 0 <> p \<Longrightarrow>
 anterior_context (tm e2) p = Some c \<Longrightarrow>
 subsumes t1 c t2"
  using subsumes_def can_still_take_ctx_def by auto

definition "can_still_take e1 e2 s1 s2 t1 t2 = (
  Label t1 = Label t2 \<and>
  Arity t1 = Arity t2 \<and>
  Outputs t1 = Outputs t2 \<and>
  Updates t1 = Updates t2 \<and>
  can_still_take_ctx (tm e1) (tm e2) s1 s2 t1 t2 \<and>
  accepts_and_gets_us_to_both e1 e2 s1 s2)"

lemma can_still_take_direct_subsumption:
 "can_still_take e1 e2 s1 s2 t1 t2 \<Longrightarrow>
  directly_subsumes e1 e2 s1 s2 t1 t2"
  apply (simp add: directly_subsumes_def can_still_take_def)
  using accepts_and_gets_us_to_both_def accepts_trace_gives_context distinguishing_guard_subsumption by blast

end