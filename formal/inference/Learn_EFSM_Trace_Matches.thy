theory Learn_EFSM_Trace_Matches
imports Learn_EFSM
begin

lemma Suc_0_simp: "Suc 0 = 1"
  by simp

lemma Suc_1_simp: "Suc 1 = 2"
  by simp

lemma Suc_2_simp: "Suc 2 = 3"
  by simp

lemma io_index_singleton: "io_index n [a] [] = {|(n, In, 0)|}"
  by (simp add: io_index_def)

lemma ffilter_pairs: "(ffilter (\<lambda>(a, b). eventNum a \<le> eventNum b \<and> a \<noteq> b)
       ({|(3, Out, 0), (2, Out, 0), (2, In, 0), (1, Out, 0), (1, In, 0), (0, In, 0)|} |\<times>|
        {|(3, Out, 0), (2, Out, 0), (2, In, 0), (1, Out, 0), (1, In, 0), (0, In, 0)|})) = {|((2, Out, 0), 3, Out, 0), ((2, Out, 0), 2, In, 0), ((2, In, 0), 3, Out, 0), ((2, In, 0), 2, Out, 0), ((1, Out, 0), 3, Out, 0),
   ((1, Out, 0), 2, Out, 0), ((1, Out, 0), 2, In, 0), ((1, Out, 0), 1, In, 0), ((1, In, 0), 3, Out, 0), ((1, In, 0), 2, Out, 0),
   ((1, In, 0), 2, In, 0), ((1, In, 0), 1, Out, 0), ((0, In, 0), 3, Out, 0), ((0, In, 0), 2, Out, 0), ((0, In, 0), 2, In, 0),
   ((0, In, 0), 1, Out, 0), ((0, In, 0), 1, In, 0)|}"
  apply (simp add: fprod_def)
  apply (simp add: ffilter_def)
  apply (simp add: fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def)
  apply standard
   apply clarify
   apply (case_tac "ac = Out")
    apply simp
    apply (case_tac "aa = Out")
     apply auto[1]
    apply (case_tac "aa = In")
     apply auto[1]
    apply simp
   apply (case_tac "ac = In")
    apply simp
    apply (case_tac "aa = Out")
     apply auto[1]
    apply (case_tac "aa = In")
     apply auto[1]
    apply simp
   apply simp

  apply clarify
  apply simp
  apply (case_tac "aa = In \<and> ac = In")
   apply simp
   apply (case_tac "b=0 \<and> ba = 0")
    apply simp
    apply (case_tac "a = 1")
     apply simp
    apply simp
    apply (case_tac "a = 0")
     apply auto[1]
    apply simp
   apply simp
   apply (case_tac "b=0 \<and> ba = 0")
    apply simp
   apply auto[1]
  apply simp
  apply (case_tac "b=0 \<and> ba = 0")
   apply simp
   apply (case_tac "a=2")
    apply simp
   apply (case_tac "ab=2")
     apply auto[1]
    apply (case_tac "ab=3")
     apply simp
    apply simp
   apply simp
  apply (case_tac "a=1")
    apply simp
  apply (case_tac "ab=2")
     apply auto[1]
    apply (case_tac "ab=3")
     apply simp
    apply (case_tac "ab=1")
     apply auto[1]
    apply simp
   apply (case_tac "a=0")
    apply simp
    apply (case_tac "ab=3")
     apply simp
    apply (case_tac "ab=2")
     apply simp
    apply simp
    apply presburger
   apply simp
  apply simp
  apply (case_tac "a=1")
   apply simp
  apply (case_tac "b=0 \<and> ba = 0")
    apply simp
   apply auto[1]
  apply simp
  apply (case_tac "a=2")
   apply simp
   apply (case_tac "b=0 \<and> ba = 0")
    apply simp
   apply auto[1]
  apply simp
   apply (case_tac "b=0 \<and> ba = 0")
   apply simp
  by auto

lemma get_intra_1: "get_intratrace_matches_alt
      [(''select'', [Str ''coke''], []), (''coin'', [Num 50], [Num 50]), (''coin'', [Num 50], [Num 100]), (''vend'', [], [Str ''coke''])] =
{|((0, In, 0), 3, Out, 0), ((1, In, 0), 2, In, 0), ((1, In, 0), 1, Out, 0), ((1, Out, 0), 2, In, 0), ((1, Out, 0), 1, In, 0)|}"
  apply (simp add: get_intratrace_matches_preproces)
  apply (simp add: indices_def)
  apply (simp only: Suc_0_simp Suc_1_simp Suc_2_simp)
  apply (simp add: io_index_def)
  apply (simp add: ffilter_pairs)
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def)
  apply standard
   apply clarify
   apply simp
   apply (case_tac "ac = Out")
    apply simp
    apply (case_tac "aa = In")
     apply auto[1]
    apply auto[1]
   apply auto[1]
  by simp

lemma get_intra_2: "get_intratrace_matches_alt [(''select'', [Str ''coke''], []), (''coin'', [Num 100], [Num 100]), (''vend'', [], [Str ''coke''])] =
    {|((1, Out, 0), 1, In, 0), ((1, In, 0), 1, Out, 0), ((0, In, 0), 2, Out, 0)|}"
  apply (simp add: get_intratrace_matches_alt_def)
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  apply (simp add: fprod_def Abs_fset_inverse)
  apply (simp add: indices_def io_index_def)
  apply (simp add: Set.filter_def)
  apply standard
   apply clarify
   apply simp
   apply (case_tac "ac = In")
    apply auto[1]
   apply auto[1]
  by simp

lemma get_intra_3: "get_intratrace_matches_alt
     [(''select'', [Str ''pepsi''], []), (''coin'', [Num 50], [Num 50]), (''coin'', [Num 50], [Num 100]), (''vend'', [], [Str ''pepsi''])] =
    {|((0, In, 0), 3, Out, 0), ((1, In, 0), 2, In, 0), ((1, In, 0), 1, Out, 0), ((1, Out, 0), 2, In, 0), ((1, Out, 0), 1, In, 0)|}"
  apply (simp add: get_intratrace_matches_alt_def)
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  apply (simp add: fprod_def Abs_fset_inverse)
  apply (simp add: indices_def io_index_def)
  apply (simp add: Set.filter_def)
  apply standard
   apply clarify
   apply simp
   apply (case_tac "ac = In")
    apply simp
  apply (case_tac "ab = 2")
     apply simp
     apply auto[1]
    apply simp
    apply (case_tac "aa=Out")
     apply simp
     apply auto[1]
    apply simp
    apply auto[1]
   apply simp
   apply (case_tac "ac = Out")
    apply simp
    apply (case_tac "aa = In")
     apply simp
     apply auto[1]
    apply simp
    apply (case_tac "aa=Out")
  apply simp
     apply auto[1]
  apply simp
  apply simp
  by simp

lemma get_intratrace_matches: "get_all_intratrace_matches_alt traces = [{|((0, In, 0), 3, Out, 0), ((1, In, 0), 2, In, 0), ((1, In, 0), 1, Out, 0), ((1, Out, 0), 2, In, 0), ((1, Out, 0), 1, In, 0)|},
                                                {|((1, Out, 0), 1, In, 0), ((1, In, 0), 1, Out, 0), ((0, In, 0), 2, Out, 0)|},
                                                {|((0, In, 0), 3, Out, 0), ((1, In, 0), 2, In, 0), ((1, In, 0), 1, Out, 0), ((1, Out, 0), 2, In, 0), ((1, Out, 0), 1, In, 0)|}]"
  apply (simp add: traces_def)
  by (simp add: get_intra_1 get_intra_2 get_intra_3)

lemma i_possible_steps_selectCoke: "i_possible_steps merged_4_10 0 r ''select'' [Str ''coke''] = {|(0, 1, selectCoke)|}"
  apply (simp add: merged_4_10_def i_possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def)
  apply safe
  apply (simp_all add: transitions)
  by force

lemma i_possible_steps_selectPepsi: "i_possible_steps merged_4_10 0 r ''select'' [Str ''pepsi''] = {|(1, 1, selectPepsi)|}"
  apply (simp add: merged_4_10_def i_possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def)
  apply safe
  apply (simp_all add: transitions)
  by force

lemma i_possible_steps_coin50_1: "i_possible_steps merged_4_10 1 r ''coin'' [Num 50] = {|(2, 2, coin50_50)|}"
  apply (simp add: merged_4_10_def i_possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def)
  apply safe
  apply (simp_all add: transitions)
  by force

lemma i_possible_steps_coin100: "i_possible_steps merged_4_10 1 r ''coin'' [Num 100] = {|(3, 5, coin100_100)|}"
  apply (simp add: merged_4_10_def i_possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def)
  apply safe
  apply (simp_all add: transitions)
  by force

lemma i_possible_steps_coin50_2: "i_possible_steps merged_4_10 2 r ''coin'' [Num 50] = {|(4, 3, coin50_100)|}"
  apply (simp add: merged_4_10_def i_possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
  apply (simp add: Set.filter_def)
  apply safe
  apply (simp_all add: transitions)
  by force

(*definition pta :: iEFSM where
  "pta = {|(0, (0, 1), selectCoke),  (2, (1, 2), coin50_50), (4, (2, 3), coin50_100),  (5, (3, 4), vend_coke),
                                                             (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
           (1, (0, 7), selectPepsi), (7, (7, 8), coin50_50), (8, (8, 9), coin50_100),  (9, (9, 10), vend_pepsi)|}"*)

fun get_aexp_biggest_reg :: "aexp \<Rightarrow> nat" where
  "get_aexp_biggest_reg (L _) = 0" |
  "get_aexp_biggest_reg (V (R n)) = n" |
  "get_aexp_biggest_reg (V (I _)) = 0" |
  "get_aexp_biggest_reg (Plus a1 a2) = max (get_aexp_biggest_reg a1) (get_aexp_biggest_reg a2)" |
  "get_aexp_biggest_reg (Minus a1 a2) = max (get_aexp_biggest_reg a1) (get_aexp_biggest_reg a2)"

fun get_gexp_biggest_reg :: "gexp \<Rightarrow> nat" where
  "get_gexp_biggest_reg (gexp.Bc _) = 0" |
  "get_gexp_biggest_reg (gexp.Eq a1 a2) = max (get_aexp_biggest_reg a1) (get_aexp_biggest_reg a2)" |
  "get_gexp_biggest_reg (gexp.Gt a1 a2) = max (get_aexp_biggest_reg a1) (get_aexp_biggest_reg a2)" |
  "get_gexp_biggest_reg (gexp.Nor g1 g2) = max (get_gexp_biggest_reg g1) (get_gexp_biggest_reg g2)" |
  "get_gexp_biggest_reg (gexp.Null (R n)) = n" |
  "get_gexp_biggest_reg (gexp.Null (I n)) = 0"

definition get_biggest_t_reg :: "transition \<Rightarrow> nat" where
  "get_biggest_t_reg t = (let s = (fset_of_list ((map get_gexp_biggest_reg (Guard t))@ (map (\<lambda>(_, a). get_aexp_biggest_reg a) (Updates t)))) in 
                          if s = {||} then 0 else fMax s)"

definition new_reg :: "iEFSM \<Rightarrow> nat" where
  "new_reg e = (fMax (fimage (\<lambda>(_, (_, _), t). get_biggest_t_reg t) e)) + 1"

lemma new_reg_pta: "new_reg pta = 1"
  apply (simp add: new_reg_def)
  by (simp add: pta_def get_biggest_t_reg_def transitions)

definition remove_guard_add_update :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "remove_guard_add_update t inputX outputX = \<lparr>Label = (Label t), Arity = (Arity t), Guard = (filter (\<lambda>g. \<nexists>a. g = gexp.Eq (V (I inputX)) a \<or> g = gexp.Eq a (V (I inputX))) (Guard t)), Outputs = (Outputs t), Updates = (R outputX, (V (I inputX)))#(Updates t)\<rparr>"

definition generalise_output :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "generalise_output t regX outputX = \<lparr>Label = (Label t), Arity = (Arity t), Guard = (Guard t), Outputs = list_update (Outputs t) outputX (V (R regX)), Updates = (Updates t)\<rparr>"

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

primrec count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count _ [] = 0" |
  "count a (h#t) = (if a = h then 1+(count a t) else count a t)"

definition replace :: "iEFSM \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace e uid t = (let (u, (origin, dest), t') = fthe_elem (ffilter (\<lambda>(u, _). u = uid) e) in (e |-| {|(u, (origin, dest), t')|}) |\<union>| {|(u, (origin, dest), t)|}) "

primrec generalise_transitions :: "((((transition \<times> nat) \<times> ioTag \<times> nat) \<times>
     (transition \<times> nat) \<times> ioTag \<times> nat) \<times>
    ((transition \<times> nat) \<times> ioTag \<times> nat) \<times>
    (transition \<times> nat) \<times> ioTag \<times> nat) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "generalise_transitions [] e = e" |
  "generalise_transitions (h#t) e = (let ((((orig1, u1), _), (orig2, u2), _), (((gen1, u1'), _), (gen2, u2), _)) = h in
                                         replace (replace e u1 gen1) u2 gen2)"

definition modify :: "match list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "modify matches u1 u2 old = (let relevant = filter (\<lambda>(((_, u1'), io, _), (_, u2'), io', _). io = In \<and> io' = Out \<and> (u1 = u1' \<or> u2 = u1' \<or> u1 = u2' \<or> u2 = u2')) matches;
                                   newReg = new_reg old;
                                   replacements = map (\<lambda>(((t1, u1), io1, inx1), (t2, u2), io2, inx2). (((remove_guard_add_update t1 (inx1+1) newReg, u1), io1, inx1), (generalise_output t2 newReg inx2, u2), io2, inx2)) relevant;
                                   comparisons = zip relevant replacements;
                                   to_replace = filter (\<lambda>(_, s). count s replacements > 1) comparisons in
                                if to_replace = [] then None else Some (generalise_transitions to_replace old)
                              )"

lemma intertrace_matches: "find_intratrace_matches traces pta = [
(((coin50_50, 2), In, 0),
   (coin50_100, 4), In, 0),
  (((coin50_50, 2), Out, 0),
   (coin50_100, 4), In, 0),
  (((selectCoke, 0), In, 0),
   (vend_coke, 5), Out, 0),
  (((selectCoke, 0), In, 0),
   (vend_coke, 6), Out, 0),
  (((coin50_50, 7), In, 0),
   (coin50_100, 8), In, 0),
  (((coin50_50, 7), Out, 0),
   (coin50_100, 8), In, 0),
  (((selectPepsi, 1), In, 0),
   (vend_pepsi, 9), Out, 0)
]"
  by eval

definition relevant :: "match list" where
  "relevant = [
(((selectCoke, 0), In, 0),
   (vend_coke, 5), Out, 0),
  (((selectPepsi, 1), In, 0),
   (vend_pepsi, 9), Out, 0)
]"

lemma relevant:  "filter
            (\<lambda>(((uu, u1'), io, uu), (uu, u2'), ab).
                io = In \<and> (case ab of (io', uu) \<Rightarrow> io' = Out \<and> (u1' = 5 \<or> u1' = 9 \<or> u2' = 5 \<or> u2' = 9)))
            (find_intratrace_matches traces pta) = relevant"
  by eval

definition replacements :: "(((transition \<times> nat) \<times> ioTag \<times> nat) \<times>
    (transition \<times> nat) \<times> ioTag \<times> nat) list" where
  "replacements = [(((selectGeneral, 0), In, 0), (vend_general, 5), Out, 0), (((selectGeneral, 1), In, 0), (vend_general, 9), Out, 0)]"

lemma replacements: "map (\<lambda>(((t1, u1), io1, inx1), (t2, u2), io2, inx2).
                   (((remove_guard_add_update t1 (inx1 + 1) 1, u1), io1, inx1), (generalise_output t2 1 inx2, u2), io2, inx2))
            relevant = replacements"
  apply (simp add: relevant_def)
  by (simp add: generalise_selectCoke generalise_vend_coke generalise_selectPepsi generalise_vend_pepsi replacements_def)

lemma "modify (find_intratrace_matches traces pta) 5 9 pta = Some merged_vends"
  apply (simp add: modify_def new_reg_pta)
  apply (simp add: relevant replacements)

end