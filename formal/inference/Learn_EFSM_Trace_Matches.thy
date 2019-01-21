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

value "find_intratrace_matches traces pta"


end