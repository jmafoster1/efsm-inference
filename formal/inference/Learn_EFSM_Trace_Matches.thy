theory Learn_EFSM_Trace_Matches
imports Learn_EFSM
begin

lemma new_reg_pta: "new_reg pta = 1"
  apply (simp add: new_reg_def)
  by (simp add: pta_def get_biggest_t_reg_def transitions)

lemma generalise_selectCoke: "remove_guard_add_update selectCoke 1 1 = selectGeneral"
  apply (simp add: selectCoke_def remove_guard_add_update_def)
  by (simp add: selectGeneral_def)

lemma generalise_selectPepsi: "remove_guard_add_update selectPepsi 1 1 = selectGeneral"
  apply (simp add: selectPepsi_def remove_guard_add_update_def)
  by (simp add: selectGeneral_def)

lemma generalise_vend_coke: "generalise_output vend_coke 1 0 = vend_general"
  apply (simp add: generalise_output_def)
  apply (simp add: vend_coke_def)
  by (simp add: vend_general_def)

lemma generalise_vend_pepsi: "generalise_output vend_pepsi 1 0 = vend_general"
  apply (simp add: generalise_output_def)
  apply (simp add: vend_pepsi_def)
  by (simp add: vend_general_def)

definition relevant :: "match list" where
  "relevant = [
(((selectCoke, 0), In, 0),
   (vend_coke, 5), Out, 0),
  (((selectPepsi, 1), In, 0),
   (vend_pepsi, 9), Out, 0)
]"

definition replacements :: "(((transition \<times> nat) \<times> ioTag \<times> nat) \<times>
    (transition \<times> nat) \<times> ioTag \<times> nat) list" where
  "replacements = [(((selectGeneral, 0), In, 0), (vend_general, 5), Out, 0), (((selectGeneral, 1), In, 0), (vend_general, 9), Out, 0)]"


lemma relevant:  "filter
            (\<lambda>(((uu, u1'), io, uu), (uu, u2'), ab).
                io = In \<and> (case ab of (io', uu) \<Rightarrow> io' = Out \<and> (u1' = 5 \<or> u1' = 9 \<or> u2' = 5 \<or> u2' = 9)))
            (find_intratrace_matches traces pta) = relevant"
  by eval

lemma replacements: "map (\<lambda>(((t1, u1), io1, inx1), (t2, u2), io2, inx2).
                   (((remove_guard_add_update t1 (inx1 + 1) 1, u1), io1, inx1), (generalise_output t2 1 inx2, u2), io2, inx2))
            relevant = replacements"
  apply (simp add: relevant_def)
  by (simp add: generalise_selectCoke generalise_vend_coke generalise_selectPepsi generalise_vend_pepsi replacements_def)

lemma zip_relevant_replacements: "zip relevant replacements = [
((((selectCoke, 0), In, 0),
    (vend_coke, 5), Out, 0),
   ((selectGeneral, 0), In, 0),
   (vend_general, 5), Out, 0),
  ((((selectPepsi, 1), In, 0),
    (vend_pepsi, 9), Out, 0),
   ((selectGeneral, 1), In, 0),
   (vend_general, 9), Out, 0)
]"
  by eval

value "iefsm2dot_str (replace (replace pta 0 selectGeneral) 5 vend_general)"

lemma to_replace: "filter
            (\<lambda>(uu, s).
                1 < count (strip_uids s)
                     (map (strip_uids \<circ>
                           (\<lambda>(((t1, u1), io1, inx1), (t2, u2), io2, inx2).
                               (((remove_guard_add_update t1 (inx1 + 1) 1, u1), io1, inx1), (generalise_output t2 1 inx2, u2), io2, inx2)))
                       relevant))
            [((((selectCoke, 0), In, 0), (vend_coke, 5), Out, 0), ((selectGeneral, 0), In, 0), (vend_general, 5), Out, 0),
             ((((selectPepsi, 1), In, 0), (vend_pepsi, 9), Out, 0), ((selectGeneral, 1), In, 0), (vend_general, 9), Out, 0)] = 
[((((selectCoke, 0), In, 0), (vend_coke, 5), Out, 0), ((selectGeneral, 0), In, 0), (vend_general, 5), Out, 0),
 ((((selectPepsi, 1), In, 0), (vend_pepsi, 9), Out, 0), ((selectGeneral, 1), In, 0), (vend_general, 9), Out, 0)]"
  apply (simp add: strip_uids_def relevant_def)
  by (simp add: generalise_selectPepsi generalise_vend_pepsi generalise_selectCoke generalise_vend_coke)

definition nondeterministic_merged_vends :: iEFSM where
"nondeterministic_merged_vends = {|(0, (0, 1), selectGeneral),  (2, (1, 2), coin50_50), (4, (2, 3), coin50_100),  (5, (3, 4), vend_general),
                                                             (3, (1, 5), coin100_100), (6, (5, 6), vend_general),
           (1, (0, 7), selectGeneral), (7, (7, 8), coin50_50), (8, (8, 9), coin50_100),  (9, (9, 10), vend_general)|}"

lemma generalise_transitions: "(\<lambda>(uid, (from, to), t). if t = vend_pepsi then (uid, (from, to), vend_general) else (uid, (from, to), t)) `
    (\<lambda>(uid, (from, to), t). if t = selectPepsi then (uid, (from, to), selectGeneral) else (uid, (from, to), t)) `
    (\<lambda>(uid, (from, to), t). if t = vend_coke then (uid, (from, to), vend_general) else (uid, (from, to), t)) `
    (\<lambda>(uid, (from, to), t). if t = selectCoke then (uid, (from, to), selectGeneral) else (uid, (from, to), t)) ` fset pta = 
fset nondeterministic_merged_vends"
  by eval

lemma "modify (find_intratrace_matches traces pta) 5 9 pta = Some nondeterministic_merged_vends"
  apply (simp add: modify_def new_reg_pta)
  apply (simp add: relevant replacements)
  apply (simp only: zip_relevant_replacements)
  apply (simp only: to_replace Let_def)
  apply (simp add: replaceAll_def fimage_def fset_both_sides Abs_fset_inverse)
  by (simp add: generalise_transitions)

lemma nondeterministic_simulates_trace_3_3: "nondeterministic_simulates_trace (tm nondeterministic_merged_vends) (tm pta) 3 3 (\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None)
     Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "possible_steps (tm nondeterministic_merged_vends) 3 (\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None) (STR ''vend'') [] = {|(4, vend_general)|}"
    by eval
  have stop: "\<forall>aa b. possible_steps (tm pta) 4 Map.empty aa b = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def pta_def Set.filter_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''vend''), [])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_vend_3)
        apply (simp add: possible_steps)
       apply simp
      apply (simp add: vend_general_def)
     apply (simp add: vend_general_def)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def stop)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    apply (simp add: nondeterministic_step_def)
    by (simp add: possible_steps_not_vend)
qed


lemma nondeterministic_simulates_trace_2_2: "nondeterministic_simulates_trace (tm nondeterministic_merged_vends) (tm pta) 2 2 (\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None)
     Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps:  "possible_steps (tm nondeterministic_merged_vends) 2 (\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None) (STR ''coin'') [Num 50] = {|(3, coin50_100)|}"
    by eval
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''coin''), [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_coin50_2)
        apply (simp add: possible_steps)
       apply simp
      apply (simp add: transitions)
     apply (simp add: transitions)
     apply (simp add: nondeterministic_simulates_trace_3_3)

    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    apply (simp add: nondeterministic_step_def)
    by (simp add: possible_steps_pta_2_not_coin50)
qed

lemma nondeterministic_simulates_trace_5_5: "nondeterministic_simulates_trace (tm nondeterministic_merged_vends) (tm pta) 5 5 (\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None)
     Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps:  "possible_steps (tm nondeterministic_merged_vends) 5 (\<lambda>a. if a = R 1 then Some (EFSM.Str ''coke'') else None) STR ''vend'' [] = {|(6, \<lparr>Label = STR ''vend'', Arity = 0, Guard = [], Outputs = [V (R 1)], Updates = []\<rparr>)|}"
    by eval
  have stop: "\<forall> aaa b. possible_steps (tm pta) 6 Map.empty aaa b = {||}"
    by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def pta_def tm_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''vend''), [])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_vend_5 Str_coke)
        apply (simp add: possible_steps)
       apply simp
      apply (simp add: vend_general_def implode_coke)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def stop)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    apply (simp add: nondeterministic_step_def)
    by (simp add: possible_steps_pta_5_not_vend)
qed

lemma nondeterministic_simulates_trace_1_1: "nondeterministic_simulates_trace (tm nondeterministic_merged_vends) (tm pta) 1 1 <R 1 := (Str ''coke'')> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "possible_steps (tm nondeterministic_merged_vends) 1 (\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None) (STR ''coin'') [Num 50] = {|(2, coin50_50)|}"
    by eval
  have possible_steps_2: "possible_steps (tm nondeterministic_merged_vends) 1 (\<lambda>a. if a = R 1 then Some ((Str ''coke'')) else None) (STR ''coin'') [Num 100] = {|(5, coin100_100)|}"
    by eval
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''coin''), [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_coin50_1)
        apply (simp add: possible_steps)
       apply auto[1]
      apply eval
     apply (simp add: coin50_50_def)
     apply (simp add: nondeterministic_simulates_trace_2_2)
    apply (case_tac "a = ((STR ''coin''), [Num 100])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_coin100_1)
        apply (simp add: possible_steps_2)
       apply simp
      apply (simp add: transitions)
     apply (simp add: transitions)
     apply (simp add: nondeterministic_simulates_trace_5_5)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_1_not_coin)
qed

lemma nondeterministic_simulates_trace_3_9: "nondeterministic_simulates_trace (tm nondeterministic_merged_vends) (tm pta) 3 9
     (\<lambda>a. if a = R 1 then Some (EFSM.Str ''pepsi'') else None) Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "possible_steps (tm nondeterministic_merged_vends) 3 (\<lambda>a. if a = R 1 then Some (EFSM.Str ''pepsi'') else None) STR ''vend'' [] = {|(4, \<lparr>Label = STR ''vend'', Arity = 0, Guard = [], Outputs = [V (R 1)], Updates = []\<rparr>)|}"
    by eval
  have stop: "\<forall>aaa b. possible_steps (tm pta) 10 Map.empty aaa b = {||}"
    by (simp add: possible_steps_def ffilter_def fset_both_sides tm_def pta_def Abs_fset_inverse Set.filter_def)
  case (Cons a t)
  then show ?case
 apply (case_tac "a = ((STR ''vend''), [])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_vend_9 Str_coke)
        apply (simp add: possible_steps)
       apply simp
      apply (simp add: vend_general_def implode_coke)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def stop)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    apply (simp add: nondeterministic_step_def)
    by (simp add: possible_steps_pta_9_not_vend)
qed

lemma nondeterministic_simulates_trace_2_8: "nondeterministic_simulates_trace (tm nondeterministic_merged_vends) (tm pta) 2 8
     (\<lambda>a. if a = R 1 then Some (EFSM.Str ''pepsi'') else None) Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "possible_steps (tm nondeterministic_merged_vends) 2 (\<lambda>a. if a = R 1 then Some (EFSM.Str ''pepsi'') else None) STR ''coin'' [Num 50] = {|(3, coin50_100)|}"
    by eval
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''coin''), [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_coin50_8)
        apply (simp add: possible_steps)
       apply simp
      apply (simp add: transitions)
     apply (simp add: transitions)
     apply (simp add: nondeterministic_simulates_trace_3_9)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    apply (simp add: nondeterministic_step_def)
    by (simp add: possible_steps_pta_8_not_coin)
qed

lemma nondeterministic_simulates_trace_1_7: "nondeterministic_simulates_trace (tm nondeterministic_merged_vends) (tm pta) 1 7 <R 1 := EFSM.Str ''pepsi''> Map.empty t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "possible_steps (tm nondeterministic_merged_vends) 1 (\<lambda>a. if a = R 1 then Some (EFSM.Str ''pepsi'') else None) STR ''coin'' [Num 50] = {|(2, coin50_50)|}"
    by eval
  case (Cons a t)
  then show ?case
    apply (case_tac "a = ((STR ''coin''), [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_coin50_7)
        apply (simp add: possible_steps)
       apply simp
      apply (simp add: transitions)
     apply (simp add: transitions)
     apply (simp add: nondeterministic_simulates_trace_2_8)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    apply (simp add: nondeterministic_step_def)
    by (simp add: possible_steps_pt_7_not_coin)
qed

lemma nondeterministic_simulates_trace_0_0: "nondeterministic_simulates_trace (tm nondeterministic_merged_vends) (tm pta) 0 0 Map.empty Map.empty t"
proof(induct t)
case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
 have possible_steps: "\<forall>d. possible_steps (tm nondeterministic_merged_vends) 0 Map.empty (STR ''select'') [d] = {|(1, selectGeneral), (7, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def nondeterministic_merged_vends_def Set.filter_def)
    apply safe
                       apply (simp_all add: transitions selectGeneral_def)
    apply force
    by force
  have selectGeneral_updates: "\<forall>d. EFSM.apply_updates (Updates selectGeneral) (join_ir [d] Map.empty) Map.empty = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by (simp add: selectGeneral_def)
  case (Cons a t)
  then show ?case
     apply (case_tac "a=((STR ''select''), [(Str ''coke'')])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_selectCoke)
        apply (simp add: possible_steps)
        apply auto[1]
       apply (simp only: selectGeneral_updates)
      apply (simp add: selectGeneral_def)
     apply (simp add: nondeterministic_simulates_trace_1_1)
    apply (case_tac "a=((STR ''select''), [Str ''pepsi''])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: step_nondet_step_equiv step_pta_selectPepsi)
        apply (simp add: possible_steps)
        apply auto[1]
       apply (simp only: selectGeneral_updates)
      apply (simp add: selectGeneral_def)
     apply (simp add: nondeterministic_simulates_trace_1_7)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_0_not_select)
qed

lemma "nondeterministic_simulates (tm nondeterministic_merged_vends) (tm pta)"
  by (simp add: nondeterministic_simulates_def nondeterministic_simulates_trace_0_0)


end