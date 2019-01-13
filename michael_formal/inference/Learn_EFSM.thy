theory Learn_EFSM
  imports Inference SelectionStrategies EFSM_Dot
begin

declare One_nat_def [simp del]

definition selectCoke :: transition where
  "selectCoke = \<lparr>Label = ''select'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>"

definition coin50_50 :: transition where
  "coin50_50 = \<lparr>Label = ''coin'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>"

definition coin50_100 :: transition where
  "coin50_100 = \<lparr>Label = ''coin'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>"

definition vend_coke :: transition where
  "vend_coke = \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>"

definition coin100_100 :: transition where
  "coin100_100 = \<lparr>Label = ''coin'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>"

definition selectPepsi :: transition where
  "selectPepsi = \<lparr>Label = ''select'', Arity = 1, Guard = [gexp.Eq (V (I 1)) (L (Str ''pepsi''))], Outputs = [], Updates = []\<rparr>"

definition vend_pepsi :: transition where
  "vend_pepsi = \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''pepsi'')], Updates = []\<rparr>"

lemmas transitions = selectCoke_def coin50_50_def coin50_100_def vend_coke_def selectPepsi_def coin100_100_def vend_pepsi_def

definition pta :: iEFSM where
  "pta = {|(0, (0, 1), selectCoke),  (2, (1, 2), coin50_50), (4, (2, 3), coin50_100),  (5, (3, 4), vend_coke),
                                                             (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
           (1, (0, 7), selectPepsi), (7, (7, 8), coin50_50), (8, (8, 9), coin50_100),  (9, (9, 10), vend_pepsi)|}"

lemma step_pta_selectPepsi: "step (tm pta) 0 Map.empty ''select'' [Str ''pepsi''] = Some (selectPepsi, 7, [], <>)"
proof-
  have possible_steps: "possible_steps (tm pta) 0 Map.empty ''select'' [Str ''pepsi''] = {|(7, selectPepsi)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def pta_def Set.filter_def)
    apply safe
                      apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: selectPepsi_def)
qed

definition traces :: log where
  "traces = [[(''select'', [Str ''coke''], []), (''coin'', [Num 50], [Num 50]), (''coin'', [Num 50], [Num 100]), (''vend'', [], [Str ''coke''])],
             [(''select'', [Str ''coke''], []), (''coin'', [Num 100], [Num 100]), (''vend'', [], [Str ''coke''])],
             [(''select'', [Str ''pepsi''], []), (''coin'', [Num 50], [Num 50]), (''coin'', [Num 50], [Num 100]), (''vend'', [], [Str ''pepsi''])]]"


lemma build_pta: "toiEFSM (make_pta traces {||}) = pta"
proof-
 have step_coin50: "step {|((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|} 1 Map.empty
           ''coin'' [Num 50] = None"
    proof-
      have set_filter: "(Set.filter
         (\<lambda>((origin, dest), t).
             origin = 1 \<and>
             Label t = ''coin'' \<and>
             Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n)) Map.empty))
         {((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)}) = {}"
        by (simp add: Set.filter_def)
      show ?thesis
        by (simp add: step_def possible_steps_def ffilter_def set_filter)
    qed
    have step_coin50_2: "step
           {|((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
             ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
           2 Map.empty ''coin'' [Num 50] = None"
    proof-
      have set_filter: "Set.filter
         (\<lambda>((origin, dest), t).
             origin = (2::nat) \<and>
             Label t = ''coin'' \<and>
             Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n)) Map.empty))
         {((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
          ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {}"
        by (simp add: Set.filter_def)
      show ?thesis
        by (simp add: step_def possible_steps_def ffilter_def set_filter)
    qed
    have step_vend_coke: "step
           {|((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
             ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
           3 Map.empty ''vend'' [] = None"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = (3::nat) \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname Map.empty Map.empty))
         {((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
          ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {}"
        by (simp add: Set.filter_def)
      show ?thesis
        by (simp add: step_def possible_steps_def ffilter_def set_filter)
    qed
    have step_selectCoke_2: "step
                  {|((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
                    ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
                    ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
                    ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
                  0 Map.empty ''select'' [Str ''coke''] = Some (selectCoke, 1, [], <>)"
    proof-
      have set_filter: "Set.filter
          (\<lambda>((origin, dest), t).
              origin = 0 \<and>
              Label t = ''select'' \<and>
              Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. if n = 1 then Some (Str ''coke'') else input2state [] (1 + 1) (I n)) Map.empty))
          {((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
           ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
           ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
           ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {((0, 1), selectCoke)}"
        apply (simp add: Set.filter_def)
        apply safe
        by (simp_all add: selectCoke_def)
      show ?thesis
        apply (simp add: step_def possible_steps_def ffilter_def set_filter)
        by (simp add: set_filter selectCoke_def)
    qed
    have step_coin100: "step
                  {|((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
                    ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
                    ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
                    ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
                  1 Map.empty ''coin'' [Num 100] = None"
    proof-
      have applyGuards: "\<not> apply_guards [gexp.Eq (V (I 1)) (L (Num 50))] (case_vname (\<lambda>n. if n = 1 then Some (Num 100) else input2state [] (1 + 1) (I n)) Map.empty)"
        by simp
      have set_filter: "Set.filter
         (\<lambda>((origin::nat, dest), t).
             origin = 1 \<and>
             Label t = ''coin'' \<and>
             Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. if n = 1 then Some (Num 100) else input2state [] (1 + 1) (I n)) Map.empty))
         {((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
          ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
          ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {}"
        apply (simp add: Set.filter_def)
        apply clarify
        using applyGuards
        by (metis (no_types, lifting) select_convs(3))
      show ?thesis
        by (simp add: step_def possible_steps_def ffilter_def set_filter)
    qed
    have step_vend_coke_2: "step
                  {|((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
                    ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
                    ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
                    ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
                    ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
                  5 Map.empty ''vend'' [] = None"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin::nat, dest), t). origin = 5 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname Map.empty Map.empty))
         {((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
          ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
          ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {}"
        by (simp add: Set.filter_def)
      show ?thesis
        by (simp add: step_def possible_steps_def ffilter_def set_filter)
    qed
    have step_select_pepsi: "step
           {|((5, 6), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
             ((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
             ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
             ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
           0 Map.empty ''select'' [Str ''pepsi''] = None"
    proof-
      have applyGuards: "\<not>apply_guards [gexp.Eq (V (I 1)) (L (Str ''coke''))] (case_vname (\<lambda>n. if n = 1 then Some (Str ''pepsi'') else input2state [] (1 + 1) (I n)) Map.empty)"
        by simp
      have set_filter: "Set.filter
         (\<lambda>((origin::nat, dest::nat), t).
             origin = 0 \<and>
             Label t = ''select'' \<and>
             Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. if n = 1 then Some (Str ''pepsi'') else input2state [] (1 + 1) (I n)) Map.empty))
         {((5, 6), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
          ((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
          ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
          ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {}"
        apply (simp add: Set.filter_def)
        apply clarify
        apply simp
        by (metis (no_types, lifting) applyGuards select_convs(3))
      show ?thesis
        by (simp add: step_def possible_steps_def ffilter_def set_filter)
    qed
    have step_coin50_3:  "step
           {|((0, 7), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''pepsi''))], Outputs = [], Updates = []\<rparr>),
             ((5, 6), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
             ((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
             ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
             ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
           7 Map.empty ''coin'' [Num 50] = None"
    proof-
      have set_filter: "Set.filter
         (\<lambda>((origin::nat, dest::nat), t).
             origin = 7 \<and>
             Label t = ''coin'' \<and>
             Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n)) Map.empty))
         {((0, 7), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''pepsi''))], Outputs = [], Updates = []\<rparr>),
          ((5, 6), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
          ((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
          ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
          ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {}"
        by (simp add: Set.filter_def)
    show ?thesis
      by (simp add: step_def possible_steps_def ffilter_def set_filter)
  qed
  have step_coin50_4: "step
           {|((7, 8), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
             ((0, 7), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''pepsi''))], Outputs = [], Updates = []\<rparr>),
             ((5, 6), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
             ((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
             ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
             ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
           8 Map.empty ''coin'' [Num 50] = None"
  proof-
    have set_filter: "Set.filter
         (\<lambda>((origin::nat, dest::nat), t).
             origin = 8 \<and>
             Label t = ''coin'' \<and>
             Suc 0 = Arity t \<and> apply_guards (Guard t) (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n)) Map.empty))
         {((7, 8), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
          ((0, 7), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''pepsi''))], Outputs = [], Updates = []\<rparr>),
          ((5, 6), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
          ((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
          ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
          ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
          ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {}"
      by (simp add: Set.filter_def)
    show ?thesis
      by (simp add: step_def possible_steps_def ffilter_def set_filter)
  qed
  have step_vend_pepsi: "step
           {|((8, 9), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((7, 8), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
             ((0, 7), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''pepsi''))], Outputs = [], Updates = []\<rparr>),
             ((5, 6), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
             ((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
             ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
             ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
             ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)|}
           9 Map.empty ''vend'' [] = None"
  proof-
    have set_filter: "Set.filter (\<lambda>((origin::nat, dest::nat), t). origin = 9 \<and> Label t = ''vend'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (case_vname Map.empty Map.empty))
         {((8, 9), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
         ((7, 8), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
         ((0, 7), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''pepsi''))], Outputs = [], Updates = []\<rparr>),
         ((5, 6), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
         ((1, 5), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr>),
         ((3, 4), \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr>),
         ((2, 3), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr>),
         ((1, 2), \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr>),
         ((0, 1), \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr>)} = {}"
      by (simp add: Set.filter_def)
    show ?thesis
      by (simp add: step_def possible_steps_def ffilter_def set_filter)
  qed
  have select_coke: " \<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''coke''))], Outputs = [], Updates = []\<rparr> = selectCoke"
    by (simp add: selectCoke_def)
  have coin50_50: "\<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 50)], Updates = []\<rparr> = coin50_50"
    by (simp add: coin50_50_def)
  have coin100_100: " \<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 100))], Outputs = [L (Num 100)], Updates = []\<rparr> = coin100_100"
    by (simp add: coin100_100_def)
  have coin50_100: "\<lparr>Label = ''coin'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Num 50))], Outputs = [L (Num 100)], Updates = []\<rparr> = coin50_100"
    by (simp add: coin50_100_def)
  have selectPepsi: "\<lparr>Label = ''select'', Arity = Suc 0, Guard = [gexp.Eq (V (I 1)) (L (Str ''pepsi''))], Outputs = [], Updates = []\<rparr> = selectPepsi"
    by (simp add: selectPepsi_def)
  have vendCoke: "\<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''coke'')], Updates = []\<rparr> = vend_coke"
    by (simp add: vend_coke_def)
  have vendPepsi: "\<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [L (Str ''pepsi'')], Updates = []\<rparr> = vend_pepsi"
    by (simp add: vend_pepsi_def)
  have sorted_list_of_fset: "sorted_list_of_fset
         {|((9::nat, 10::nat), vend_pepsi), ((8, 9), coin50_100), ((7, 8), coin50_50), ((0, 7), selectPepsi), ((5, 6), vend_coke),
           ((1, 5), coin100_100), ((3, 4), vend_coke), ((2, 3), coin50_100), ((1, 2), coin50_50), ((0, 1), selectCoke)|} = [((0, 1), selectCoke), ((0, 7), selectPepsi), ((1, 2), coin50_50), ((1, 5), coin100_100), ((2, 3), coin50_100), ((3, 4), vend_coke),
     ((5, 6), vend_coke), ((7, 8), coin50_50), ((8, 9), coin50_100), ((9, 10), vend_pepsi)]"
    by (simp add: sorted_list_of_fset_def )
  show ?thesis
    apply (simp add: make_pta_def traces_def)
    apply (simp add: step_coin50 step_coin50_2 step_vend_coke
                      step_selectCoke_2 step_coin100 step_vend_coke_2
                      step_select_pepsi step_coin50_3 step_coin50_4 step_vend_pepsi)
    apply (simp add: select_coke coin50_50 coin100_100 coin50_100 selectPepsi vendCoke vendPepsi)
    apply (simp add: toiEFSM_def toiEFSM_aux_def)
    apply (simp add: sorted_list_of_fset pta_def)
    by auto
qed

definition filtered_pairs :: "(nat \<times> nat) set" where
  "filtered_pairs = {(9, 10), (8, 10), (8, 9), (7, 10), (7, 9), (7, 8), (6, 10), (6, 9), (6, 8), (6, 7), (5, 10), (5, 9), (5, 8), (5, 7), (5, 6), (4, 10),
  (4, 9), (4, 8), (4, 7), (4, 6), (4, 5), (3, 10), (3, 9), (3, 8), (3, 7), (3, 6), (3, 5), (3, 4), (2, 10), (2, 9), (2, 8), (2, 7), (2, 6),
  (2, 5), (2, 4), (2, 3), (1, 10), (1, 9), (1, 8), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (1, 2), (0, 10), (0, 9), (0, 8), (0, 7), (0, 6),
  (0, 5), (0, 4), (0, 3), (0, 2), (0, 1)}"

lemma scoring_1: "sorted_list_of_fset (score pta naive_score) = [(0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 0, 6), (0, 0, 7), (0, 0, 8), (0, 0, 9), (0, 0, 10), (0, 1, 3), (0, 1, 4),
     (0, 1, 5), (0, 1, 6), (0, 1, 9), (0, 1, 10), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 2, 6), (0, 2, 9), (0, 2, 10), (0, 3, 4), (0, 3, 6),
     (0, 3, 7), (0, 3, 8), (0, 3, 10), (0, 4, 5), (0, 4, 6), (0, 4, 7), (0, 4, 8), (0, 4, 9), (0, 4, 10), (0, 5, 6), (0, 5, 7), (0, 5, 8),
     (0, 5, 10), (0, 6, 7), (0, 6, 8), (0, 6, 9), (0, 6, 10), (0, 7, 9), (0, 7, 10), (0, 8, 9), (0, 8, 10), (0, 9, 10), (1, 2, 7), (1, 2, 8),
     (1, 3, 5), (1, 3, 9), (1, 5, 9), (1, 7, 8), (2, 1, 2), (2, 1, 7), (2, 1, 8)]"
proof-
  have S_pta: "S pta = {|0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10|}"
    apply (simp add: S_def pta_def)
    by auto
  have fset_S: "fset {|0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10|} = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}"
    by (metis bot_fset.rep_eq finsert.rep_eq)
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S pta |\<times>| Inference.S pta) = Abs_fset filtered_pairs"
    apply (simp add: filtered_pairs_def ffilter_def fset_both_sides Abs_fset_inverse fprod_def)
    apply (simp only: S_pta fprod_equiv fset_S Set.filter_def)
    apply standard
     apply clarify
     apply (case_tac "a=10")
      apply auto[1]
      apply simp
      apply (case_tac "a=9")
       apply auto[1]
      apply simp
      apply (case_tac "a=8")
       apply auto[1]
      apply simp
      apply (case_tac "a=7")
       apply auto[1]
      apply simp
      apply (case_tac "a=6")
       apply auto[1]
      apply simp
      apply (case_tac "a=5")
       apply auto[1]
      apply simp
      apply (case_tac "a=4")
       apply auto[1]
      apply simp
      apply (case_tac "a=3")
       apply auto[1]
      apply simp
      apply (case_tac "a=2")
        apply auto[1]
      apply simp
      apply (case_tac "a=1")
      apply auto[1]
     apply simp
    apply clarify
    apply safe
    by auto
  have Two_nat_def: "2 = Suc (Suc 0)"
    by simp
  have scores: "score pta naive_score = {|(0, 9, 10), (0, 8, 10), (0, 8, 9), (0, 7, 10), (0, 7, 9), (1, 7, 8), (0, 6, 10), (0, 6, 9), (0, 6, 8), (0, 6, 7), (0, 5, 10),
     (1, 5, 9), (0, 5, 8), (0, 5, 7), (0, 5, 6), (0, 4, 10), (0, 4, 9), (0, 4, 8), (0, 4, 7), (0, 4, 6), (0, 4, 5), (0, 3, 10),
     (1, 3, 9), (0, 3, 8), (0, 3, 7), (0, 3, 6), (1, 3, 5), (0, 3, 4), (0, 2, 10), (0, 2, 9), (1, 2, 8), (1, 2, 7),
     (0, 2, 6), (0, 2, 5), (0, 2, 4), (0, 2, 3), (0, 1, 10), (0, 1, 9), (2, 1, 8), (2, 1, 7), (0, 1, 6), (0, 1, 5),
     (0, 1, 4), (0, 1, 3), (2, 1, 2), (0, 0, 10), (0, 0, 9), (0, 0, 8), (0, 0, 7), (0, 0, 6), (0, 0, 5), (0, 0, 4), (0, 0, 3),
     (0, 0, 2), (0, 0, 1)|}"
    apply (simp add: score_def ffilter filtered_pairs_def)
    apply (simp add: outgoing_transitions_def pta_def fimage_def)
    apply (simp add: naive_score_empty set_equiv)
    apply (simp add: naive_score_def fprod_def)
    apply (simp add: transitions Abs_fset_inverse)
    by (simp add: One_nat_def Two_nat_def)
  show ?thesis
    by (simp add: scores sorted_list_of_fset_def)
qed

lemmas possible_steps_fst = possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse

lemma step_pta_coin50_7: "step (tm pta) 7 r ''coin'' [Num 50] = Some (coin50_50, 8, [Some (Num 50)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 7 r ''coin'' [Num 50] = {|(8, coin50_50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: coin50_50_def)
qed

lemma step_pta_coin50_1: "step (tm pta) 1 r ''coin'' [Num 50] = Some (coin50_50, 2, [Some (Num 50)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 1 r ''coin'' [Num 50] = {|(2, coin50_50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: coin50_50_def)
qed

lemma step_pta_vend_5: "step (tm pta) 5 r ''vend'' [] = Some (vend_coke, 6, [Some (Str ''coke'')], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 5 r ''vend'' [] = {|(6, vend_coke)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: transitions)
qed

lemma step_pta_coin100_1: "step (tm pta) 1 r ''coin'' [Num 100] = Some (coin100_100, 5, [Some (Num 100)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 1 r ''coin'' [Num 100] = {|(5, coin100_100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: coin100_100_def)
qed

lemma step_pta_coin50_2: "step (tm pta) 2 r ''coin'' [Num 50] = Some (coin50_100, 3, [Some (Num 100)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 2 r ''coin'' [Num 50] = {|(3, coin50_100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: coin50_100_def)
qed

lemma step_pta_coin50_8: "step (tm pta) 8 r ''coin'' [Num 50] = Some (coin50_100, 9, [Some (Num 100)], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 8 r ''coin'' [Num 50] = {|(9, coin50_100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: coin50_100_def)
qed

lemma step_pta_vend_3: "step (tm pta) 3 r ''vend'' [] = Some (vend_coke, 4, [Some (Str ''coke'')], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 3 r ''vend'' [] = {|(4, vend_coke)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: vend_coke_def)
qed

lemma step_pta_vend_9: "step (tm pta) 9 r ''vend'' [] = Some (vend_pepsi, 10, [Some (Str ''pepsi'')], r)"
proof-
  have possible_steps: "possible_steps (tm pta) 9 r ''vend'' [] = {|(10, vend_pepsi)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: Set.filter_def tm_def pta_def)
    apply safe
                     apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: vend_pepsi_def)
qed

definition merged_1_8 :: iEFSM where
  "merged_1_8 = {|
(0, (0, 1), selectCoke),
(1, (0, 7), selectPepsi),
(2, (1, 2), coin50_50),
(3, (1, 5), coin100_100),
(4, (2, 3), coin50_100),
(5, (3, 4), vend_coke),
(6, (5, 6), vend_coke),
(7, (7, 1), coin50_50),
(8, (1, 9), coin50_100),
(9, (9, 10), vend_pepsi)
|}"

definition merged_2_9 :: iEFSM where
  "merged_2_9 = {|(0, (0, 1), selectCoke), (1, (0, 7), selectPepsi), (2, (1, 2), coin50_50), (3, (1, 5), coin100_100), (4, (2, 3), coin50_100),
      (5, (3, 4), vend_coke), (6, (5, 6), vend_coke), (7, (7, 1), coin50_50), (8, (1, 2), coin50_100), (9, (2, 10), vend_pepsi)|}"

lemma merge_states_2_9: "merge_states 2 9 merged_1_8 = merged_2_9"
  by (simp add: merge_states_def merge_states_aux_def merged_1_8_def merged_2_9_def)

lemma step_merged_2_9_selectPepsi: "step (tm merged_2_9) 0 Map.empty ''select'' [Str ''pepsi''] = Some (selectPepsi, 7, [], <>)"
proof-
  have possible_steps: "possible_steps (tm merged_2_9) 0 Map.empty ''select'' [Str ''pepsi''] = {|(7, selectPepsi)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_2_9_def Set.filter_def)
    apply safe
                      apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: selectPepsi_def)
qed

lemma step_merged_2_9_coin50_7: "step (tm merged_2_9) 7 r ''coin'' [Num 50] = Some (coin50_50, 1, [Some (Num 50)], r)"
proof-
  have possible_steps: "possible_steps (tm merged_2_9) 7 r ''coin'' [Num 50] = {|(1, coin50_50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_2_9_def Set.filter_def)
    apply safe
                      apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: coin50_50_def)
qed

lemma posterior_selectPepsi: "posterior \<lbrakk>\<rbrakk> selectPepsi = \<lbrakk>\<rbrakk>"
proof-
  have consistent_medial: "consistent (medial \<lbrakk>\<rbrakk> (Guard selectPepsi))"
    apply (simp add: selectPepsi_def consistent_def)
    apply (rule_tac x="<I 1 := Str ''pepsi''>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial)
    by (simp add: selectPepsi_def)
qed

lemma posterior_selectCoke: "posterior \<lbrakk>\<rbrakk> selectCoke = \<lbrakk>\<rbrakk>"
proof-
  have consistent_medial: "consistent (medial \<lbrakk>\<rbrakk> (Guard selectCoke))"
    apply (simp add: selectCoke_def consistent_def)
    apply (rule_tac x="<I 1 := Str ''coke''>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial)
    by (simp add: selectCoke_def)
qed

lemma posterior_coin50_50: "posterior \<lbrakk>\<rbrakk> coin50_50 = \<lbrakk>\<rbrakk>"
proof-
  have consistent_medial: "consistent (medial \<lbrakk>\<rbrakk> (Guard coin50_50))"
    apply (simp add: coin50_50_def consistent_def)
    apply (rule_tac x="<I 1 := Num 50>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial)
    by (simp add: coin50_50_def)
qed

lemma posterior_coin50_100: "posterior \<lbrakk>\<rbrakk> coin50_100 = \<lbrakk>\<rbrakk>"
proof-
  have consistent_medial: "consistent (medial \<lbrakk>\<rbrakk> (Guard coin50_100))"
    apply (simp add: coin50_100_def consistent_def)
    apply (rule_tac x="<I 1 := Num 50>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial)
    by (simp add: coin50_100_def)
qed

lemma posterior_coin100_100: "posterior \<lbrakk>\<rbrakk> coin100_100 = \<lbrakk>\<rbrakk>"
proof-
  have consistent_medial: "consistent (medial \<lbrakk>\<rbrakk> (Guard coin100_100))"
    apply (simp add: coin100_100_def consistent_def)
    apply (rule_tac x="<I 1 := Num 100>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial)
    by (simp add: coin100_100_def)
qed

lemma posterior_vend_coke: "posterior \<lbrakk>\<rbrakk> vend_coke = \<lbrakk>\<rbrakk>"
proof-
  have consistent_medial: "consistent (medial \<lbrakk>\<rbrakk> (Guard vend_coke))"
    apply (simp add: vend_coke_def consistent_def)
    apply (rule_tac x="<>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial)
    by (simp add: vend_coke_def)
qed

lemma posterior_vend_pepsi: "posterior \<lbrakk>\<rbrakk> vend_pepsi = \<lbrakk>\<rbrakk>"
proof-
  have consistent_medial: "consistent (medial \<lbrakk>\<rbrakk> (Guard vend_pepsi))"
    apply (simp add: vend_pepsi_def consistent_def)
    apply (rule_tac x="<>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial)
    by (simp add: vend_pepsi_def)
qed

lemma no_subsumption_coin50_50_coin50_100:  "\<not> subsumes \<lbrakk>\<rbrakk> coin50_50 coin50_100"
proof-
  have subsumption_violation: "(\<exists>i r. satisfies_context r \<lbrakk>\<rbrakk> \<and>
           apply_guards (Guard coin50_100) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin50_100) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin50_50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
    apply (simp add: coin50_50_def coin50_100_def)
    apply standard
     apply (rule_tac x="<>" in exI)
     apply (simp add: satisfies_context_def datastate2context_def consistent_def)
     apply (rule_tac x="<>" in exI)
     apply clarify
     defer
    apply (rule_tac x="[Num 50]" in exI)
    apply simp
     apply (case_tac r)
        apply simp
       apply (case_tac x2)
    by auto
  show ?thesis
    by (simp add: subsumes_def subsumption_violation)
qed

lemma no_subsumption_coin50_100_coin50_50: " \<not> subsumes \<lbrakk>\<rbrakk> coin50_100 coin50_50"
proof-
  have subsumption_violation: "(\<exists>i r. satisfies_context r \<lbrakk>\<rbrakk> \<and>
           apply_guards (Guard coin50_50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin50_50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin50_100) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
        apply (simp add: coin50_50_def coin50_100_def)
    apply standard
     apply (rule_tac x="<>" in exI)
     apply (simp add: satisfies_context_def datastate2context_def consistent_def)
     apply (rule_tac x="<>" in exI)
     apply clarify
     defer
    apply (rule_tac x="[Num 50]" in exI)
    apply simp
     apply (case_tac r)
        apply simp
       apply (case_tac x2)
    by auto
  show ?thesis
    by (simp add: subsumes_def subsumption_violation)
qed

lemma no_subsumption_vend_coke_vend_pepsi: "\<not> subsumes \<lbrakk>\<rbrakk> vend_coke vend_pepsi"
proof-
  have subsumption_violation: "(\<exists>i r. satisfies_context r \<lbrakk>\<rbrakk> \<and>
           apply_guards (Guard vend_pepsi) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs vend_pepsi) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs vend_coke) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
    apply (simp add: transitions)
        apply (rule_tac x="<>" in exI)
     apply (simp add: satisfies_context_def datastate2context_def consistent_def)
     apply (rule_tac x="<>" in exI)
     apply clarify
     apply (case_tac r)
        apply simp
       apply (case_tac x2)
    by auto
  show ?thesis
    by (simp add: subsumes_def subsumption_violation)
qed

lemma no_subsumption_vend_pepsi_vend_coke: "\<not> subsumes \<lbrakk>\<rbrakk> vend_pepsi vend_coke"
proof-
  have subsumption_violation: "(\<exists>i r. satisfies_context r \<lbrakk>\<rbrakk> \<and>
           apply_guards (Guard vend_coke) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs vend_coke) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs vend_pepsi) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
    apply (simp add: transitions)
        apply (rule_tac x="<>" in exI)
     apply (simp add: satisfies_context_def datastate2context_def consistent_def)
     apply (rule_tac x="<>" in exI)
     apply clarify
     apply (case_tac r)
        apply simp
       apply (case_tac x2)
    by auto
  show ?thesis
    by (simp add: subsumes_def subsumption_violation)
qed

lemma step_pta_selectCoke: "step (tm pta) 0 Map.empty ''select'' [Str ''coke''] = Some (selectCoke, 1, [], <>)"
proof-
  have possible_steps: "possible_steps (tm pta) 0 Map.empty ''select'' [Str ''coke''] = {|(1, selectCoke)|}"
    apply (simp add: possible_steps_def ffilter_def fimage_def fset_both_sides Abs_fset_inverse)
    apply (simp add: tm_def pta_def Set.filter_def)
    apply safe
                      apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: selectCoke_def)
qed

lemma step_merged_2_9_selectCoke: "step (tm merged_2_9) 0 Map.empty ''select'' [Str ''coke''] = Some (selectCoke, 1, [], <>)"
proof-
  have possible_steps: "possible_steps (tm merged_2_9) 0 Map.empty ''select'' [Str ''coke''] = {|(1, selectCoke)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_2_9_def Set.filter_def)
    apply safe
      apply (simp_all add: transitions)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    by (simp add: selectCoke_def)
qed

definition merged_1_7 :: iEFSM where
  "merged_1_7 = {|(0, (0, 1), selectCoke), (2, (1, 2), coin50_50), (4, (2, 3), coin50_100),  (5, (3, 4), vend_coke), 
                                                                   (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
                 (1, (0, 1), selectPepsi), (7, (1, 8), coin50_50), (8, (8, 9), coin50_100),  (9, (9, 10), vend_pepsi)|}"

lemma merge_states_1_7: "merge_states 1 7 pta = merged_1_7"
  by (simp add: merge_states_def pta_def merge_states_aux_def merged_1_7_def)

definition merged_2_8 :: iEFSM where
  "merged_2_8 = {|(0, (0, 1), selectCoke),  (2, (1, 2), coin50_50),  (4, (2, 3), coin50_100),  (5, (3, 4), vend_coke),
                                                                      (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
                   (1, (0, 1), selectPepsi), (7, (1, 2), coin50_50),  (8, (2, 9), coin50_100),  (9, (9, 10), vend_pepsi)|}"

lemma merge_states_2_8: "merge_states 2 8 merged_1_7 = merged_2_8"
  by (simp add: merge_states_def merge_states_aux_def merged_1_7_def merged_2_8_def)

lemma no_choice_coin50_50_coin100_100: "\<not>choice coin50_50 coin100_100"
  by (simp add: choice_def transitions)

definition merge_2_8_no_nondet :: iEFSM where
  "merge_2_8_no_nondet = {|(0, (0, 1), selectCoke), (2, (1, 2), coin50_50), (4, (2, 3), coin50_100), (5, (3, 4), vend_coke), (3, (1, 5), coin100_100),
      (6, (5, 6), vend_coke), (1, (0, 1), selectPepsi), (7, (1, 2), coin50_50), (8, (2, 9), coin50_100), (9, (9, 10), vend_pepsi)|}"

definition selectGeneral :: transition where
  "selectGeneral = \<lparr>Label = ''select'', Arity = 1, Guard = [], Outputs = [], Updates = [(R 1, V (I 1))]\<rparr>"

definition vend_general :: transition where
  "vend_general = \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [V (R 1)], Updates = []\<rparr>"

definition merged_4_10 :: iEFSM where
  "merged_4_10 = {|(0, (0, 1), selectCoke), (2, (1, 2), coin50_50), (4, (2, 3), coin50_100), (5, (3, 4), vend_coke) ,
                   (1, (0, 1), selectPepsi),                                                 (9, (3, 4), vend_pepsi), 
                                            (3, (1, 5), coin100_100), (6, (5, 6), vend_coke)|}"

definition merged_vends :: iEFSM where
  "merged_vends = {|(0, (0, 1), selectGeneral), (2, (1, 2), coin50_50), (4, (2, 3), coin50_100), (5, (3, 4), vend_general) ,
                                            (3, (1, 5), coin100_100), (6, (5, 6), vend_general)|}"

definition coinGeneral :: transition where
  "coinGeneral = \<lparr>Label = ''coin'', Arity = 1, Guard = [], Outputs = [Plus (V (I 1)) (V (R 2))], Updates = [(R 2, Plus (V (I 1)) (V (R 2)))]\<rparr>"

lemma no_choice_coin100_100_coin50_50: "\<not>choice coin100_100 coin50_50"
  by (simp add: choice_def transitions)

lemma no_choice_coin100_100_coin50_100: "\<not>choice coin100_100 coin50_100"
  by (simp add: choice_def transitions)

lemma no_choice_selectCoke_selectPepsi: "\<not>choice selectCoke selectPepsi"
  by (simp add: choice_def transitions)

lemma choice_coin50_100_coin50_50: "choice coin50_100 coin50_50"
  apply (simp add: choice_def transitions)
  by auto

lemma choice_coin50_50_coin50_50: "choice coin50_50 coin50_50"
  apply (simp add: choice_def transitions)
  by auto

lemma choice_coin50_100_coin50_100: "choice coin50_100 coin50_100"
  apply (simp add: choice_def transitions)
  by auto

lemma choice_vend_coke_vend_pepsi: "choice vend_coke vend_pepsi"
  by (simp add: choice_def transitions)

lemma no_coice_vend_general_coin100_100:  "\<not>choice vend_general coin100_100"
  by (simp add: choice_def transitions vend_general_def)

lemma no_choice_coinGeneral_vend_general: "\<not>choice coinGeneral vend_general"
  by (simp add: choice_def coinGeneral_def vend_general_def)

lemma choice_coinGeneral_coin100_100: "choice coinGeneral coin100_100"
  apply (simp add: transitions coinGeneral_def choice_def)
  by auto

lemma no_coice_coin100_100_vend_general: "\<not>choice coin100_100 vend_general"
  by (simp add: choice_def transitions vend_general_def)

lemma choice_coin100_100_coinGeneral: "choice coin100_100 coinGeneral"
  apply (simp add: transitions coinGeneral_def choice_def)
  by auto

lemma choice_vend_general_vend_general: "choice vend_general vend_general"
  by (simp add: choice_def vend_general_def)

lemmas choices = choice_vend_general_vend_general choice_coin100_100_coinGeneral  no_coice_coin100_100_vend_general choice_coinGeneral_coin100_100 no_choice_coinGeneral_vend_general no_coice_vend_general_coin100_100 choice_vend_coke_vend_pepsi choice_coin50_100_coin50_100 choice_coin50_50_coin50_50 choice_coin50_100_coin50_50 no_choice_selectCoke_selectPepsi no_choice_coin100_100_coin50_100 no_choice_coin100_100_coin50_50 no_choice_coin50_50_coin100_100 choice_symmetry

lemma coin50_50_lt_coin50_100: "coin50_50 < coin50_100"
  by (simp add: transitions less_transition_ext_def less_aexp_def)

lemma vend_coke_lt_vend_pepsi: "vend_coke < vend_pepsi"
  by (simp add: transitions less_transition_ext_def less_aexp_def)

lemmas orders = vend_coke_lt_vend_pepsi coin50_50_lt_coin50_100

lemma merge_states_1_8: "merge_states 1 8 pta = merged_1_8"
  apply (simp add: merge_states_def merge_states_aux_def pta_def merged_1_8_def)
  by auto

lemma nondeterministic_pairs_merged_1_8: "nondeterministic_pairs merged_1_8 = {|(1, (2, 9), (coin50_50, 2), coin50_100, 8)|}"
proof-
  have minus_1: "{|(1, selectCoke, 0), (7, selectPepsi, 1)|} |-| {|(7, selectPepsi, 1)|} = {|(1, selectCoke, 0)
|}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{|(2, coin50_50, 2), (5, coin100_100, 3), (9, coin50_100, 8)|} |-| {|(5, coin100_100, 3)|} = {|(2, coin50_50, 2), (9, coin50_100, 8)|}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{|(2, coin50_50, 2), (5, coin100_100, 3), (9, coin50_100, 8)|} |-| {|(9, coin50_100, 8)|} = {|(2, coin50_50, 2), (5, coin100_100, 3)|}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminsm_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (7, selectPepsi, 1)|} = {|(0, (1, 7), (selectCoke, 0), selectPepsi, 1)|}"
    by (simp add: state_nondeterminism_def minus_1)
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50, 2), (5, coin100_100, 3), (9, coin50_100, 8)|} = {|
      (1, (2, 5), (coin50_50, 2), coin100_100, 3),
      (1, (5, 9), (coin100_100, 3), coin50_100, 8),
      (1, (2, 9), (coin50_50, 2), coin50_100, 8)
    |}"
    apply (simp add: state_nondeterminism_def minus_2 minus_3)
    by auto
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_8_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminsm_0 state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices orders)
qed

lemma nondeterministic_pairs_merged_1_7: "nondeterministic_pairs merged_1_7 = {|
(1, (2, 8), (coin50_50, 2), coin50_50, 7)
|}"
proof-
  have minus_1: "{(2, coin50_50, 2), (5, coin100_100, 3), (8, coin50_50, 7)} - {(5, coin100_100, 3)} = {(2, coin50_50, 2), (8, coin50_50, 7)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{(2, coin50_50, 2::nat), (5, coin100_100, 3), (8, coin50_50, 7)} - {(8, coin50_50, 7)} = {(2, coin50_50, 2), (5, coin100_100, 3)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50, 2), (5, coin100_100, 3), (8, coin50_50, 7)|} = {|
      (1, (5, 8), (coin100_100, 3), coin50_50, 7),
      (1, (2, 5), (coin50_50, 2), coin100_100, 3),
      (1, (2, 8), (coin50_50, 2), coin50_50, 7)
    |}"
    apply (simp add: state_nondeterminism_def fimage_def minus_1 minus_2)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    by auto
  have minus_3: "{(1, selectCoke, 0), (1, selectPepsi, 1)} - {(1, selectPepsi, 1)} = {(1, selectCoke, 0)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (1, selectPepsi, 1)|} = {|(0, (1, 1), (selectPepsi, 1), selectCoke, 0), (0, (1, 1), (selectCoke, 0), selectPepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_7_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1 state_nondeterminism_0)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

definition generator :: generator_function where
  "generator oldEFSM t1FromOld t1 t2FromOld t2 = (if (oldEFSM, t1FromOld, t1, t2FromOld, t2) = (pta, 1, coin50_50, 8, coin50_100) then None
                                                  else None)"

definition H_pta :: "nat \<Rightarrow> nat" where
  "H_pta n = (if n = 7 then 1 else if n = 8 then 2 else if n = 9 then 3 else if n = 10 then 4 else n)"

definition H_merged_4_10 :: "nat \<Rightarrow> nat" where
  "H_merged_4_10 n = n"

definition H_merged_1_2 :: "nat \<Rightarrow> nat" where
  "H_merged_1_2 n = (if n = 2 then 1 else if n = 3 then 1 else n)"

definition merged_1_3 :: iEFSM where
  "merged_1_3 = {|(0, (0, 1), selectGeneral), (2, (1, 1), coin50_50), (4, (1, 1), coin50_100), (5, (1, 4), vend_general),
                                              (3, (1, 5), coin100_100), (6, (5, 6), vend_general)|}"

definition selectGeneral_2 :: transition where
  "selectGeneral_2 = \<lparr>Label = ''select'', Arity = 1, Guard = [], Outputs = [], Updates = [(R 1, V (I 1)), (R 2, (L (Num 0)))]\<rparr>"

definition merged_1_3_coin :: iEFSM where
  "merged_1_3_coin = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general),
                                              (3, (1, 5), coin100_100), (6, (5, 6), vend_general)|}"

definition merged_1_5 :: iEFSM where
  "merged_1_5 = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general), (3, (1, 1), coin100_100),
      (6, (1, 6), vend_general)|}"

definition merged_1_5_coin :: iEFSM where
  "merged_1_5_coin = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general),
      (6, (1, 6), vend_general)|}"

definition H_merged_1_5 :: "nat \<Rightarrow> nat" where
  "H_merged_1_5 n = (if n = 2 then 1 else if n = 3 then 1 else if n = 5 then 1 else n)"

definition modifier :: update_modifier where
  "modifier t1 t2 newFrom newEFSM oldEFSM = (if (t1, t2, newFrom, newEFSM, oldEFSM) = (coin50_50, coin50_100, 1, merged_1_8, pta) then None
                                        else if (t1, t2, newFrom, newEFSM, oldEFSM) = (vend_coke, vend_pepsi, 3, merged_4_10, pta) then Some (merged_vends, H_merged_4_10, H_pta)
                                        else if (t1, t2, newFrom, newEFSM, oldEFSM) = (coin50_50, coin50_100, 1, merged_1_3, merged_vends) then Some (merged_1_3_coin, H_merged_1_2, H_merged_1_2)
                                        else if (t1, t2, newFrom, newEFSM, oldEFSM) = (coinGeneral, coin100_100, 1, merged_1_5, merged_vends) then Some (merged_1_5_coin, H_merged_1_5, H_merged_1_5)
                                        else None)"

lemma set_nequiv_def: "(s \<noteq> s') = (\<exists>e. (e \<in> s \<and> e \<notin> s') \<or> (e \<in> s' \<and> e \<notin> s))"
  apply safe
   apply simp
  by simp

lemma merge_1_8: "merge pta 1 8 generator modifier = None"
proof-
  have leaves_2_pta: "leaves 2 pta = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) (fset pta) = {(2, (1, 2), coin50_50)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_1_8_pta: "leaves 8 pta = 8"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) (fset pta) = {(8, (8, 9), coin50_100)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have no_direct_subsumption_coin_50_50_coin50_100: "\<not> directly_subsumes (tm pta) (tm merged_2_9) 8 coin50_50 coin50_100"
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''pepsi'']), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_pta_selectPepsi)
     apply (rule accepts.step)
      apply (simp add: step_pta_coin50_7)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_pta_selectPepsi)
     apply (rule gets_us_to.step_some)
      apply (simp add: step_pta_coin50_7)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)
    apply (simp add: step_merged_2_9_selectPepsi step_merged_2_9_coin50_7)
    by (simp add: posterior_selectPepsi posterior_coin50_50 no_subsumption_coin50_50_coin50_100)
  have no_direct_subsumption_coin50_100_coin_50_50: "\<not> directly_subsumes (tm pta) (tm merged_2_9) 1 coin50_100 coin50_50"
    apply (simp add: directly_subsumes_def)
    apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_pta_selectCoke)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_pta_selectCoke)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def)
    apply (simp add: step_merged_2_9_selectCoke)
    by (simp add: posterior_selectCoke no_subsumption_coin50_100_coin50_50)
  have merged_2_9_neq_merged_1_3: "merged_2_9 \<noteq> merged_1_3"
    apply (simp add: merged_2_9_def merged_1_3_def set_equiv)
    apply (simp only: set_nequiv_def)
    apply (rule_tac x="(0, (0, 1), selectCoke)" in exI)
    by (simp add: transitions selectGeneral_def)
  have coin50_50_neq_coinGeneral:  "coin50_50 \<noteq> coinGeneral"
    by (simp add: coin50_50_def coinGeneral_def)
  have merge_transitions: "merge_transitions pta merged_2_9 1 8 1 2 2 coin50_50 2 coin50_100 8 generator modifier True = None"
    apply (simp add: merge_transitions_def easy_merge_def)
    by (simp add: generator_def modifier_def no_direct_subsumption_coin_50_50_coin50_100 coin50_50_neq_coinGeneral
                     no_direct_subsumption_coin50_100_coin_50_50 merged_2_9_neq_merged_1_3)
  have arrives_2_merged_1_8: "arrives 2 merged_1_8 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_8 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_8_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_8_merged_1_8: "arrives 8 merged_1_8 = 9"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_1_8 = {|(8, (1, 9), coin50_100)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_8_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have leaves_2_merged_2_9: "leaves 2 merged_2_9 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_9 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have arrives_2_merged_2_9: "arrives 2 merged_2_9 = 2"
      proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_9 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_8_merged_2_9: "arrives 8 merged_2_9 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_2_9 = {|(8, (1, 2), coin50_100)|}"
      apply (simp add: ffilter_def merged_2_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions) 
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  show ?thesis
    apply (simp add: merge_def merge_states_1_8 nondeterminism_def nondeterministic_pairs_merged_1_8)
    apply (simp add: leaves_2_pta leaves_1_8_pta merge_transitions arrives_8_merged_1_8 arrives_2_merged_1_8)
    apply (simp add: merge_states_2_9 leaves_2_merged_2_9 arrives_2_merged_2_9 arrives_8_merged_2_9)
    by (simp add: merge_transitions nondeterminism_def nondeterministic_pairs_merged_1_8)
qed

lemma singleton_equiv: "is_singleton s \<Longrightarrow> (the_elem s = i) = (s = {i})"
  by (meson is_singleton_the_elem the_elem_eq)

lemma singleton_dest: "fis_singleton (possible_steps e s r aa b) \<Longrightarrow>
       fthe_elem (possible_steps e s r aa b) = (baa, aba) \<Longrightarrow>
       ((s, baa), aba) |\<in>| e"
  apply (simp add: fis_singleton_def fthe_elem_def singleton_equiv)
  apply (simp add: possible_steps_def fmember_def)
  by auto

lemma anterior_context_merged_2_8: "anterior_context (tm merged_2_8) p = \<lbrakk>\<rbrakk>"
proof-
  have every_transition_gives_empty: "\<forall>s r aa b baa aba. fis_singleton (possible_steps (tm merged_2_8) s r aa b) \<longrightarrow>
       fthe_elem (possible_steps (tm merged_2_8) s r aa b) = (baa, aba) \<longrightarrow>
       posterior \<lbrakk>\<rbrakk> aba = \<lbrakk>\<rbrakk>"
  proof-
    have possible_transitions: "\<forall>aba. aba \<noteq> selectCoke \<longrightarrow>
      aba \<noteq> selectPepsi \<longrightarrow>
      aba \<noteq> coin50_50 \<longrightarrow>
      aba \<noteq> coin50_100 \<longrightarrow>
      aba \<noteq> coin100_100 \<longrightarrow>
      aba \<noteq> vend_coke \<longrightarrow>
      aba \<noteq> vend_pepsi \<longrightarrow> ( \<nexists>fst. (fst, aba) |\<in>| (tm merged_2_8))"
      by (simp add: merged_2_8_def tm_def)
    show ?thesis
      apply clarify
      apply (case_tac "aba = selectCoke")
       apply (simp add: posterior_selectCoke)
      apply (case_tac "aba = selectPepsi")
       apply (simp add: posterior_selectPepsi)
      apply (case_tac "aba = coin50_50")
       apply (simp add: posterior_coin50_50)
      apply (case_tac "aba = coin50_100")
       apply (simp add: posterior_coin50_100)
      apply (case_tac "aba = coin100_100")
       apply (simp add: posterior_coin100_100)
      apply (case_tac "aba = vend_coke")
       apply (simp add: posterior_vend_coke)
      apply (case_tac "aba = vend_pepsi")
       apply (simp add: posterior_vend_pepsi)
      using singleton_dest possible_transitions
      by blast
  qed
  have step_empty:  "\<forall>s r aa b aba baa c d. step (tm merged_2_8) s r aa b = Some (aba, baa, c, d) \<longrightarrow> (posterior \<lbrakk>\<rbrakk> aba) = \<lbrakk>\<rbrakk>"
    apply clarify
    apply (simp add: step_def)
    apply (case_tac "fis_singleton (possible_steps (tm merged_2_8) s r aa b)")
     defer
     apply simp
    apply (case_tac "fthe_elem (possible_steps (tm merged_2_8) s r aa b)")
    apply simp
    apply clarify
    by (simp add: every_transition_gives_empty)
  have posterior_sequence_empty: "\<forall>s r. posterior_sequence \<lbrakk>\<rbrakk> (tm merged_2_8) s r p = \<lbrakk>\<rbrakk>"
  proof(induct p)
    case Nil
    then show ?case by simp
  next
    case (Cons a p)
    then show ?case
      apply clarify
      apply simp
      apply (case_tac "step (tm merged_2_8) s r (fst a) (snd a)")
       apply simp
      apply (simp add: step_empty)
      apply (case_tac aa)
      apply clarify
      by (simp add: step_empty)
  qed
  show ?thesis
    by (simp add: anterior_context_def posterior_sequence_empty)
qed

definition merged_3_9 :: iEFSM where
  "merged_3_9 = {|(0, (0, 1), selectCoke),  (2, (1, 2), coin50_50),   (8, (2, 3), coin50_100), (5, (3, 4), vend_coke),
                         (1, (0, 1), selectPepsi), (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
                                                   (4, (2, 3), coin50_100),  (9, (3, 10), vend_pepsi)|}"

definition merged_3_9_coin100 :: iEFSM where
  "merged_3_9_coin100 = {|(0, (0, 1), selectCoke),  (2, (1, 2), coin50_50),  (5, (3, 4), vend_coke),
                         (1, (0, 1), selectPepsi), (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
                                                   (4, (2, 3), coin50_100),  (9, (3, 10), vend_pepsi)|}"

lemma anterior_context_merged_3_9: "anterior_context (tm merged_3_9) p = \<lbrakk>\<rbrakk>"
proof-
have every_transition_gives_empty: "\<forall>s r aa b baa aba. fis_singleton (possible_steps (tm merged_3_9) s r aa b) \<longrightarrow>
       fthe_elem (possible_steps (tm merged_3_9) s r aa b) = (baa, aba) \<longrightarrow>
       posterior \<lbrakk>\<rbrakk> aba = \<lbrakk>\<rbrakk>"
  proof-
    have possible_transitions: "\<forall>aba. aba \<noteq> selectCoke \<longrightarrow>
      aba \<noteq> selectPepsi \<longrightarrow>
      aba \<noteq> coin50_50 \<longrightarrow>
      aba \<noteq> coin50_100 \<longrightarrow>
      aba \<noteq> coin100_100 \<longrightarrow>
      aba \<noteq> vend_coke \<longrightarrow>
      aba \<noteq> vend_pepsi \<longrightarrow> ( \<nexists>fst. (fst, aba) |\<in>| (tm merged_3_9))"
      by (simp add: merged_3_9_def tm_def)
    show ?thesis
      apply clarify
      apply (case_tac "aba = selectCoke")
       apply (simp add: posterior_selectCoke)
      apply (case_tac "aba = selectPepsi")
       apply (simp add: posterior_selectPepsi)
      apply (case_tac "aba = coin50_50")
       apply (simp add: posterior_coin50_50)
      apply (case_tac "aba = coin50_100")
       apply (simp add: posterior_coin50_100)
      apply (case_tac "aba = coin100_100")
       apply (simp add: posterior_coin100_100)
      apply (case_tac "aba = vend_coke")
       apply (simp add: posterior_vend_coke)
      apply (case_tac "aba = vend_pepsi")
       apply (simp add: posterior_vend_pepsi)
      using singleton_dest possible_transitions
      by blast
  qed
  have step_empty:  "\<forall>s r aa b aba baa c d. step (tm merged_3_9) s r aa b = Some (aba, baa, c, d) \<longrightarrow> (posterior \<lbrakk>\<rbrakk> aba) = \<lbrakk>\<rbrakk>"
    apply clarify
    apply (simp add: step_def)
    apply (case_tac "fis_singleton (possible_steps (tm merged_3_9) s r aa b)")
     defer
     apply simp
    apply (case_tac "fthe_elem (possible_steps (tm merged_3_9) s r aa b)")
    apply simp
    apply clarify
    by (simp add: every_transition_gives_empty)
  have posterior_sequence_empty: "\<forall>s r. posterior_sequence \<lbrakk>\<rbrakk> (tm merged_3_9) s r p = \<lbrakk>\<rbrakk>"
  proof(induct p)
    case Nil
    then show ?case by simp
  next
    case (Cons a p)
    then show ?case
      apply clarify
      apply simp
      apply (case_tac "step (tm merged_3_9) s r (fst a) (snd a)")
       apply simp
      apply (simp add: step_empty)
      apply (case_tac aa)
      apply clarify
      by (simp add: step_empty)
  qed
  show ?thesis
    by (simp add: anterior_context_def posterior_sequence_empty)
qed

lemma anterior_context_merged_4_10: "anterior_context (tm merged_4_10) p = \<lbrakk>\<rbrakk>"
proof-
have every_transition_gives_empty: "\<forall>s r aa b baa aba. fis_singleton (possible_steps (tm merged_4_10) s r aa b) \<longrightarrow>
       fthe_elem (possible_steps (tm merged_4_10) s r aa b) = (baa, aba) \<longrightarrow>
       posterior \<lbrakk>\<rbrakk> aba = \<lbrakk>\<rbrakk>"
  proof-
    have possible_transitions: "\<forall>aba. aba \<noteq> selectCoke \<longrightarrow>
      aba \<noteq> selectPepsi \<longrightarrow>
      aba \<noteq> coin50_50 \<longrightarrow>
      aba \<noteq> coin50_100 \<longrightarrow>
      aba \<noteq> coin100_100 \<longrightarrow>
      aba \<noteq> vend_coke \<longrightarrow>
      aba \<noteq> vend_pepsi \<longrightarrow> ( \<nexists>fst. (fst, aba) |\<in>| (tm merged_4_10))"
      by (simp add: merged_4_10_def tm_def)
    show ?thesis
      apply clarify
      apply (case_tac "aba = selectCoke")
       apply (simp add: posterior_selectCoke)
      apply (case_tac "aba = selectPepsi")
       apply (simp add: posterior_selectPepsi)
      apply (case_tac "aba = coin50_50")
       apply (simp add: posterior_coin50_50)
      apply (case_tac "aba = coin50_100")
       apply (simp add: posterior_coin50_100)
      apply (case_tac "aba = coin100_100")
       apply (simp add: posterior_coin100_100)
      apply (case_tac "aba = vend_coke")
       apply (simp add: posterior_vend_coke)
      apply (case_tac "aba = vend_pepsi")
       apply (simp add: posterior_vend_pepsi)
      using singleton_dest possible_transitions
      by blast
  qed
  have step_empty:  "\<forall>s r aa b aba baa c d. step (tm merged_4_10) s r aa b = Some (aba, baa, c, d) \<longrightarrow> (posterior \<lbrakk>\<rbrakk> aba) = \<lbrakk>\<rbrakk>"
    apply clarify
    apply (simp add: step_def)
    apply (case_tac "fis_singleton (possible_steps (tm merged_4_10) s r aa b)")
     defer
     apply simp
    apply (case_tac "fthe_elem (possible_steps (tm merged_4_10) s r aa b)")
    apply simp
    apply clarify
    by (simp add: every_transition_gives_empty)
  have posterior_sequence_empty: "\<forall>s r. posterior_sequence \<lbrakk>\<rbrakk> (tm merged_4_10) s r p = \<lbrakk>\<rbrakk>"
  proof(induct p)
    case Nil
    then show ?case by simp
  next
    case (Cons a p)
    then show ?case
      apply clarify
      apply simp
      apply (case_tac "step (tm merged_4_10) s r (fst a) (snd a)")
       apply simp
      apply (simp add: step_empty)
      apply (case_tac aa)
      apply clarify
      by (simp add: step_empty)
  qed
  show ?thesis
    by (simp add: anterior_context_def posterior_sequence_empty)
qed

lemma subsumes_coin50_50_coin50_50: "subsumes \<lbrakk>\<rbrakk> coin50_50 coin50_50"
  apply (simp add: subsumes_def posterior_coin50_50)
  apply (simp add: posterior_def Let_def)
  apply (simp add: coin50_50_def remove_input_constraints_def)
  apply clarify
  using consistent_empty_1 by force

lemma subsumes_coin50_100_coin50_100: "subsumes \<lbrakk>\<rbrakk> coin50_100 coin50_100"
  apply (simp add: subsumes_def posterior_coin50_100)
  apply (simp add: posterior_def Let_def)
  apply (simp add: coin50_100_def remove_input_constraints_def)
  apply clarify
  using consistent_empty_1 by force

definition merged_2_8_coin50 :: iEFSM where
  "merged_2_8_coin50 = {|
   (9, (9, 10), vend_pepsi),
   (8, (2, 9), coin50_100),
   (1, (0, 1), selectPepsi),
   (6, (5, 6), vend_coke),
   (3, (1, 5), coin100_100),
   (5, (3, 4), vend_coke),
   (4, (2, 3), coin50_100),
   (0, (0, 1), selectCoke),
   (2, (1, 2), coin50_50)
|}"

lemma replace_coin50: "replace_transition merged_2_8 2 1 2 coin50_50 coin50_50 = merged_2_8_coin50"
proof-
  have filter: "{a \<in> fset merged_2_8. snd a \<noteq> ((1, 2), coin50_50)} = {
   (9, (9, 10), vend_pepsi),
   (8, (2, 9), coin50_100),
   (1, (0, 1), selectPepsi),
   (6, (5, 6), vend_coke),
   (3, (1, 5), coin100_100),
   (5, (3, 4), vend_coke),
   (4, (2, 3), coin50_100),
   (0, (0, 1), selectCoke)}"
    apply (simp add: merged_2_8_def)
    apply standard
     apply clarify
     apply simp
     apply auto[1]
    apply clarify
    apply simp
    apply (case_tac "a=0")
     apply simp
    apply (case_tac "a=1")
     apply simp
    apply (case_tac "a=3")
     apply simp
    apply (case_tac "a=9")
     apply simp
    apply (case_tac "a=8")
     apply simp
    apply simp
    by auto
  show ?thesis
  apply (simp add: replace_transition_def ffilter_def)
  apply (simp add: Set.filter_def finsert_equiv Abs_fset_inverse)
    apply (simp add: merged_2_8_coin50_def filter)
    by auto
qed

lemma nondeterministic_pairs_merged_2_8_coin50: "nondeterministic_pairs merged_2_8_coin50 = {|(2, (3, 9), (coin50_100, 4), coin50_100, 8)|}"
proof-
  have minus_1: "{|(5, coin100_100, 3), (2, coin50_50, 2)|} |-| {|(2, coin50_50, 2)|} = {|(5, coin100_100, 3)|}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{(1, selectCoke, 0), (1, selectPepsi, 1)} - {(1, selectPepsi, 1)} = {(1, selectCoke, 0)}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{|(9, coin50_100, 8::nat), (3, coin50_100, 4)|} |-| {|(3, coin50_100, 4)|} = {|(9, coin50_100, 8)|}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (1, selectPepsi, 1)|} = {|(0, (1, 1), (selectPepsi, 1), selectCoke, 0), (0, (1, 1), (selectCoke, 0), selectPepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  have outgoing_0_equiv: "{|(1, selectPepsi, 1), (1, selectCoke, 0)|} = {|(1, selectCoke, 0), (1, selectPepsi, 1)|}"
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(5, coin100_100, 3), (2, coin50_50, 2)|} = {|(1, (2, 5), (coin50_50, 2), coin100_100, 3)|}"
    by (simp add: state_nondeterminism_def minus_1)
  have state_nondeterminism_2: "state_nondeterminism 2 {|(9, coin50_100, 8), (3, coin50_100, 4)|} = {|(2, (3, 9), (coin50_100, 4), coin50_100, 8)|}"
    by (simp add: state_nondeterminism_def minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_2_8_coin50_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: outgoing_0_equiv state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_2)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

lemma nondeterministic_pairs_merged_3_9_coin100: "nondeterministic_pairs merged_3_9_coin100 = {|(3, (4, 10), (vend_coke, 5), vend_pepsi, 9)|}"
proof-
  have minus_1: "{|(2, coin50_50, 2), (5, coin100_100, 3)|} |-| {|(5, coin100_100, 3)|} = {|(2, coin50_50, 2)|}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{|(4, vend_coke, 5), (10, vend_pepsi, 9)|} |-| {|(10, vend_pepsi, 9)|} = {|(4, vend_coke, 5)|}"
    apply (simp add: transitions)
    by auto
  have minus_3: "{(1, selectCoke, 0), (1, selectPepsi, 1)} - {(1, selectPepsi, 1)} = {(1, selectCoke, 0)}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke, 0), (1, selectPepsi, 1)|} = {|(0, (1, 1), (selectPepsi, 1), selectCoke, 0), (0, (1, 1), (selectCoke, 0), selectPepsi, 1)|}"
    by (simp add: state_nondeterminism_def fimage_def minus_3)
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50, 2), (5, coin100_100, 3)|} = {|(1, (2, 5), (coin50_50, 2), coin100_100, 3)|}"
    by (simp add: state_nondeterminism_def minus_1)
  have state_nondeterminism_3: "state_nondeterminism 3 {|(4, vend_coke, 5), (10, vend_pepsi, 9)|} = {|(3, (4, 10), (vend_coke, 5), vend_pepsi, 9)|}"
    by (simp add: state_nondeterminism_def minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_3_9_coin100_def)
    apply (simp add: outgoing_transitions_def fimage_def)
    apply (simp add: state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_3)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: orders choices)
qed

lemma nondeterministic_simulates_trace_merged_vends_pta_4_4: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 4 4 <R 1 := Str ''coke''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "\<forall>aa b. possible_steps (tm pta) 4 Map.empty aa b = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def pta_def Set.filter_def)
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma possible_steps_not_vend: "aa = ''vend'' \<longrightarrow> b \<noteq> [] \<Longrightarrow> possible_steps (tm pta) 3 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply (simp add: vend_coke_def)
  by auto

lemma nondetermnistic_step_not_vend: "aa = ''vend'' \<longrightarrow> b \<noteq> [] \<Longrightarrow> nondeterministic_step (tm pta) 3 Map.empty aa b = None"
  by (simp add: nondeterministic_step_def possible_steps_not_vend)

lemma possible_steps_vend: "possible_steps (tm merged_vends) 3 r ''vend'' [] = {|(4, vend_general)|}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def merged_vends_def Set.filter_def)
  apply safe
           apply (simp_all add: transitions selectGeneral_def vend_general_def)
  by force

lemma nondeterministic_simulates_trace_merged_vends_pta_3_3: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 3 3 <R 1 := Str ''coke''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have regsimp: "(\<lambda>a. if a = R 1 then Some (Str ''coke'') else None) = <R 1 := Str ''coke''>"
    apply (rule ext)
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a=(''vend'', [])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_vend_3)
       apply (simp add: possible_steps_vend)
      apply (simp add: vend_general_def regsimp)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_4_4)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondetermnistic_step_not_vend)
qed

lemma possible_steps_pta_2_not_coin50: "aa = ''coin'' \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow> possible_steps (tm pta) 2 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: Set.filter_def tm_def pta_def)
  apply (simp add: coin50_100_def hd_input2state)
  by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))

lemma possible_steps_merged_vends_coin50_2: "\<forall>r. possible_steps (tm merged_vends) 2 r ''coin'' [Num 50] = {|(3, coin50_100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions selectGeneral_def)
    by force

lemma nondeterministic_simulates_trace_merged_vends_pta_2_2: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 2 2 <R 1 := Str ''coke''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have coin50_updates: "\<forall>r. EFSM.apply_updates (Updates coin50_100) (join_ir [Num 50] r) r = r"
    apply clarify
    apply (rule ext)
    by (simp add: transitions)
  have regsimp: "(\<lambda>a. if a = R 1 then Some (Str ''coke'') else None) = <R 1 := Str ''coke''>"
    apply (rule ext)
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a=(''coin'', [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_coin50_2)
       apply (simp add: possible_steps_merged_vends_coin50_2)
      apply (simp only: coin50_updates regsimp)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_3_3)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_2_not_coin50)
qed

lemma nondeterministic_simulates_trace_merged_vends_pta_6_6: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 6 6 <R 1 := Str ''coke''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "\<forall>aa b. possible_steps (tm pta) 6 Map.empty aa b = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def pta_def Set.filter_def)
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps)
qed

lemma possible_steps_pta_5_not_vend: "a = ''vend'' \<longrightarrow> b \<noteq> [] \<Longrightarrow> possible_steps (tm pta) 5 Map.empty a b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def vend_coke_def)
  by force

lemma nondeterministic_simulates_trace_merged_vends_pta_5_5: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 5 5 <R 1 := Str ''coke''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have regsimp: "(\<lambda>a. if a = R 1 then Some (Str ''coke'') else None) = <R 1 := Str ''coke''>"
    apply (rule ext)
    by simp
  have possible_steps_vend: "possible_steps (tm merged_vends) 5 <R 1 := Str ''coke''> ''vend'' [] = {|(6, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: transitions vend_general_def)
    by force
  case (Cons a t)
  case (Cons a t)
  then show ?case
    apply (case_tac "a = (''vend'', [])")
     apply (simp add: regsimp)
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_vend_5)
       apply (simp add: possible_steps_vend)
      apply (simp add: vend_general_def regsimp)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_6_6)
    apply (case_tac a)
    apply (simp add: regsimp)
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_5_not_vend)
qed

lemma possible_steps_pta_1_not_coin: "aa = ''coin'' \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       aa = ''coin'' \<longrightarrow> b \<noteq> [Num 100] \<Longrightarrow>
       possible_steps (tm pta) 1 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply clarify
  apply (case_tac "Label baa = ''coin''")
   apply simp
   apply (case_tac "ba = 2")
    apply (simp add: transitions hd_input2state)
    apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
   apply (simp add: transitions hd_input2state)
   apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  apply (simp add: transitions)
  by auto

lemma possible_steps_merged_vends_coin50_1: "possible_steps (tm merged_vends) 1 r ''coin'' [Num 50] = {|(2, coin50_50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions selectGeneral_def)
  by force

lemma possible_steps_merged_vends_coin100: "possible_steps (tm merged_vends) 1 r ''coin'' [Num 100] = {|(5, coin100_100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions selectGeneral_def vend_general_def)
    by force

lemma nondeterministic_simulates_trace_merged_vends_pta_1_1: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 1 1 <R 1 := Str ''coke''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have coin50_updates: "\<forall>r. EFSM.apply_updates (Updates coin50_50) (join_ir [Num 50] r) r = r"
    apply clarify
    apply (rule ext)
    by (simp add: transitions)
  have regsimp: "(\<lambda>a. if a = R 1 then Some (Str ''coke'') else None) = <R 1 := Str ''coke''>"
    apply (rule ext)
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a=(''coin'', [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_coin50_1)
       apply (simp add: possible_steps_merged_vends_coin50_1)
      apply (simp only: coin50_updates regsimp)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_2_2)
    apply (case_tac "a=(''coin'', [Num 100])")
     apply (simp add: regsimp)
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_coin100_1)
       apply (simp add: possible_steps_merged_vends_coin100)
      apply (simp add: coin100_100_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_5_5)
    apply (case_tac a)
    apply (simp add: regsimp)
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_1_not_coin)
qed

lemma possible_steps_pta_9_not_vend: "aa = ''vend'' \<longrightarrow> b \<noteq> [] \<Longrightarrow>
       possible_steps (tm pta) 9 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply (simp add: vend_pepsi_def)
  by auto

lemma nondeterministic_simulates_trace_merged_vends_pta_3_9: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 3 9 <R 1 := Str ''pepsi''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "\<forall>r. possible_steps (tm merged_vends) 3 r ''vend'' [] = {|(4, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
    apply (simp_all add: transitions vend_general_def)
    by force
  have possible_steps_10: "\<forall>aaa b. possible_steps (tm pta) 10 Map.empty aaa b = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def pta_def Set.filter_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a=(''vend'', [])")
    apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_vend_9)
       apply (simp add: possible_steps)
      apply (simp add: vend_general_def)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def possible_steps_10)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_9_not_vend)
qed

lemma possible_steps_pta_8_not_coin: "aa = ''coin'' \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm pta) 8 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply (simp add: coin50_100_def hd_input2state)
  by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))

lemma nondeterministic_simulates_trace_merged_vends_pta_2_8: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 2 8 <R 1 := Str ''pepsi''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "possible_steps (tm merged_vends) 2 <R 1 := Str ''pepsi''> ''coin'' [Num 50] = {|(3, coin50_100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions selectGeneral_def vend_general_def)
    by force
  case (Cons a t)
  have regsimp: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  then show ?case
    apply (case_tac "a=(''coin'', [Num 50])")
     apply (simp add: regsimp)
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_coin50_8)
       apply (simp add: possible_steps)
      apply (simp add: coin50_100_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_3_9)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_8_not_coin)
qed

lemma possible_steps_pt_7_not_coin: "aa = ''coin'' \<longrightarrow> b \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm pta) 7 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def coin50_50_def hd_input2state)
  by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))

lemma nondeterministic_simulates_trace_merged_vends_pta_1_7: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 1 7 <R 1 := Str ''pepsi''> Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_coin50: "\<forall>r. possible_steps (tm merged_vends) 1 r ''coin'' [Num 50] = {|(2, coin50_50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions selectGeneral_def)
    by force
  have regsimp: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a=(''coin'', [Num 50])")
     apply (simp add: regsimp)
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_coin50_7)
       apply (simp add: possible_steps_coin50)
      apply (simp add: coin50_50_def)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_2_8)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pt_7_not_coin)
qed

lemma possible_steps_pta_0_not_select: " aa = ''select'' \<longrightarrow> b \<noteq> [Str ''coke''] \<Longrightarrow>
       aa = ''select'' \<longrightarrow> b \<noteq> [Str ''pepsi''] \<Longrightarrow>
       possible_steps (tm pta) 0 Map.empty aa b = {||}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def pta_def Set.filter_def)
  apply clarify
  apply simp
  apply (case_tac "ba = 1")
   apply (simp add: transitions hd_input2state)
   apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  apply (simp add: transitions hd_input2state)
  by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))

lemma nondeterministic_simulates_trace_merged_vends_pta_0_0: "nondeterministic_simulates_trace (tm merged_vends) (tm pta) 0 0 Map.empty Map.empty t H_pta"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps: "\<forall>d. possible_steps (tm merged_vends) 0 Map.empty ''select'' [d] = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions selectGeneral_def)
    by force
  have selectGeneral_updates: "\<forall>d. EFSM.apply_updates (Updates selectGeneral) (join_ir [d] Map.empty) Map.empty = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by (simp add: selectGeneral_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a=(''select'', [Str ''coke''])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_selectCoke)
       apply (simp add: possible_steps)
      apply (simp only: selectGeneral_updates)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_1_1)
    apply (case_tac "a=(''select'', [Str ''pepsi''])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_pta_def)
        apply (simp add: step_nondet_step_equiv step_pta_selectPepsi)
       apply (simp add: possible_steps)
      apply (simp only: selectGeneral_updates)
     apply (simp add: nondeterministic_simulates_trace_merged_vends_pta_1_7)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_pta_0_not_select)
qed

lemma nondeterministic_pairs_merged_vends: "nondeterministic_pairs merged_vends = {||}"
proof-
  have minus_1: "{|(2, coin50_50, 2), (5, coin100_100, 3)|} |-| {|(5, coin100_100, 3)|} = {|(2, coin50_50, 2)|}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50, 2), (5, coin100_100, 3)|} = {|(1, (2, 5), (coin50_50, 2), coin100_100, 3)|}"
    by (simp add: state_nondeterminism_def minus_1)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_vends_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    by (simp add: choices)
qed

lemma merge_1_7: "merge pta 1 7 generator modifier = Some merged_vends"
proof-
  have leaves_2_pta: "leaves 2 pta = 1"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) (fset pta) = {(2, (1, 2), coin50_50)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have leaves_7_pta: "leaves 7 pta = 7"
  proof-
    have set_filter: "Set.filter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) (fset pta) = {(7, (7, 8), coin50_50)}"
      apply (simp add: Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter_def fthe_elem_def Abs_fset_inverse set_filter)
  qed
  have arrives_2_merged_1_7: "arrives 2 merged_1_7 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_7 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_1_7_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_7_merged_1_7: "arrives 7 merged_1_7 = 8"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) merged_1_7 = {|(7, (1, 8), coin50_50)|}"
      apply (simp add: ffilter_def merged_1_7_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have directly_subsumes_coin50_coin50: "\<forall>s. directly_subsumes (tm pta) (tm merged_2_8) s coin50_50 coin50_50"
    by (simp add: directly_subsumes_def anterior_context_merged_2_8 subsumes_coin50_50_coin50_50)
                 (* easy_merge oldEFSM newEFSM     t1FromOld t2FromOld newFrom t1NewTo t2NewTo t1        u1 t2        u2 maker *)
                 (* replace_transition newEFSM u1 newFrom t2NewTo t1 t2 *)
  have easy_merge: "easy_merge pta merged_2_8 1 7 1 2 2 coin50_50 2 coin50_50 7 generator = Some merged_2_8_coin50"
    (* apply (simp add: easy_merge_def) *)
    unfolding easy_merge_def
    apply (simp add: directly_subsumes_coin50_coin50)
    by (simp add: replace_coin50)
  have merge_transitions: "merge_transitions pta merged_2_8 1 7 1 2 2 coin50_50 2 coin50_50 7 generator modifier True = Some merged_2_8_coin50"
    apply (simp add: merge_transitions_def)
    by (simp add: easy_merge)
  have leaves_2_merged_2_8: "leaves 2 merged_2_8 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_8 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have arrives_2_merged_2_8: "arrives 2 merged_2_8 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_2_8 = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_7_merged_2_8: "arrives 7 merged_2_8 = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (7, (a, b), ba)) merged_2_8= {|(7, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def merged_2_8_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions) 
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_4_merged_2_8_coin50: "arrives 4 merged_2_8_coin50 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_2_8_coin50 = {|(4, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def merged_2_8_coin50_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_8_merged_2_8_coin50: "arrives 8 merged_2_8_coin50 = 9"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_2_8_coin50 = {|(8, (2, 9), coin50_100)|}"
      apply (simp add: ffilter_def merged_2_8_coin50_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_3_9_merged_2_8_coin50: "merge_states 3 9 merged_2_8_coin50 = merged_3_9"
    apply (simp add: merge_states_def merge_states_aux_def merged_2_8_coin50_def merged_3_9_def)
    by auto
  have leaves_4_pta: "leaves 4 pta = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) pta = {|(4, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def pta_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_8_pta: "leaves 8 pta = 8"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) pta = {|(8, (8, 9), coin50_100)|}"
      apply (simp add: ffilter_def pta_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_4_merged_3_9: "leaves 4 merged_3_9 = 2 \<and>arrives 4 merged_3_9 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_3_9 = {|(4, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def merged_3_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def leaves_def ffilter)
  qed
  have arrives_8_merged_3_9: "arrives 8 merged_3_9 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (8, (a, b), ba)) merged_3_9 = {|(8, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def merged_3_9_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_transitions_2: "merge_transitions pta merged_3_9 2 8 2 3 3 coin50_100 4 coin50_100 8 generator modifier True = Some merged_3_9_coin100"
  proof-
    have ffilter: "ffilter (\<lambda>x. snd x \<noteq> ((2, 3), coin50_100)) merged_3_9 = {|
                         (0, (0, 1), selectCoke),  (2, (1, 2), coin50_50),          (5, (3, 4), vend_coke),
                         (1, (0, 1), selectPepsi), (3, (1, 5), coin100_100), (6, (5, 6), vend_coke),
                                                   (9, (3, 10), vend_pepsi)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_3_9_def)
      apply standard
       apply clarify
      by auto
    have easy_merge: "easy_merge pta merged_3_9 2 8 2 3 3 coin50_100 4 coin50_100 8 generator = Some merged_3_9_coin100"
      apply (simp add: easy_merge_def directly_subsumes_def anterior_context_merged_3_9 subsumes_coin50_100_coin50_100)
      apply (simp add: replace_transition_def ffilter)
      apply (simp add: merged_3_9_coin100_def)
      by auto
    show ?thesis
      by (simp add: merge_transitions_def easy_merge)
  qed
  have arrives_5_merged_3_9_coin100: "arrives 5 merged_3_9_coin100 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_3_9_coin100 = {|(5, (3, 4), vend_coke)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_3_9_coin100_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_9_merged_3_9_coin100: "arrives 9 merged_3_9_coin100 = 10"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) merged_3_9_coin100 = {|(9, (3, 10), vend_pepsi)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_3_9_coin100_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_4_10: "merge_states 4 10 merged_3_9_coin100 = merged_4_10"
    apply (simp add: merge_states_def merge_states_aux_def merged_3_9_coin100_def merged_4_10_def)
    by auto
  have leaves_5_pta: "leaves 5 pta = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) pta = {|(5, (3, 4), vend_coke)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_9_pta: "leaves 9 pta = 9"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) pta = {|(9, (9, 10), vend_pepsi)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def pta_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_5_merged_4_10: "leaves 5 merged_4_10 = 3 \<and> arrives 5 merged_4_10 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_4_10 = {|(5, (3, 4), vend_coke)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_4_10_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_9_merged_4_10: "arrives 9 merged_4_10 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (9, (a, b), ba)) merged_4_10 = {|(9, (3, 4), vend_pepsi)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_4_10_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have no_direct_subsumption_vend_coke_vend_pepsi: "\<not> directly_subsumes (tm pta) (tm merged_4_10) 9 vend_coke vend_pepsi"
       apply (simp add: directly_subsumes_def anterior_context_merged_4_10)
       apply (rule_tac x="[(''select'', [Str ''pepsi'']), (''coin'', [Num 50]), (''coin'', [Num 50])]" in exI)
       apply standard
        apply (simp add: accepts_trace_def)
        apply (rule accepts.step)
         apply (simp add: step_pta_selectPepsi)
        apply (rule accepts.step)
         apply (simp add: step_pta_coin50_7)
        apply (rule accepts.step)
         apply (simp add: step_pta_coin50_8)
        apply (rule accepts.base)
       apply standard
              apply (rule gets_us_to.step_some)
         apply (simp add: step_pta_selectPepsi)
              apply (rule gets_us_to.step_some)
         apply (simp add: step_pta_coin50_7)
              apply (rule gets_us_to.step_some)
         apply (simp add: step_pta_coin50_8)
      apply (simp add: gets_us_to.base)
    by (simp add: no_subsumption_vend_coke_vend_pepsi)
  have no_direct_subsumption_vend_pepsi_vend_coke: "\<not> directly_subsumes (tm pta) (tm merged_4_10) 3 vend_pepsi vend_coke"
    apply (simp add: directly_subsumes_def anterior_context_merged_4_10 no_subsumption_vend_pepsi_vend_coke)
    apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (simp add: accepts_trace_def)
     apply (rule accepts.step)
      apply (simp add: step_pta_selectCoke)
     apply (rule accepts.step)
      apply (simp add: step_pta_coin50_1)
     apply (rule accepts.step)
      apply (simp add: step_pta_coin50_2)
     apply (rule accepts.base)
    apply (rule gets_us_to.step_some)
         apply (simp add: step_pta_selectCoke)
    apply (rule gets_us_to.step_some)
     apply (simp add: step_pta_coin50_1)
    apply (rule gets_us_to.step_some)
     apply (simp add: step_pta_coin50_2)
    by (simp add: gets_us_to.base)
  have merge_vend_coke_vend_pepsi: "merge_transitions pta merged_4_10 3 9 3 4 4 vend_coke 5 vend_pepsi 9 generator modifier True = Some merged_vends"
  proof-
    have easy_merge: "easy_merge pta merged_4_10 3 9 3 4 4 vend_coke 5 vend_pepsi 9 generator = None"
      apply (simp add: easy_merge_def generator_def)
      by (simp add: no_direct_subsumption_vend_coke_vend_pepsi no_direct_subsumption_vend_pepsi_vend_coke)
    show ?thesis
      apply (simp add: merge_transitions_def easy_merge modifier_def)
      by (simp add: nondeterministic_simulates_def nondeterministic_simulates_trace_merged_vends_pta_0_0)
  qed
  show ?thesis
    apply (simp add: merge_def merge_states_1_7 nondeterminism_def nondeterministic_pairs_merged_1_7)
    apply (simp add: leaves_2_pta leaves_7_pta arrives_2_merged_1_7 arrives_7_merged_1_7)
    apply (simp add: leaves_2_merged_2_8 merge_states_2_8 arrives_2_merged_2_8 arrives_7_merged_2_8)
    apply (simp add: merge_transitions nondeterminism_def nondeterministic_pairs_merged_2_8_coin50)
    apply (simp add: arrives_4_merged_2_8_coin50 arrives_8_merged_2_8_coin50 merge_states_3_9_merged_2_8_coin50)
    apply (simp add: leaves_4_pta leaves_8_pta leaves_4_merged_3_9 arrives_8_merged_3_9)
    apply (simp add: merge_transitions_2 nondeterminism_def nondeterministic_pairs_merged_3_9_coin100)
    apply (simp add: arrives_5_merged_3_9_coin100 arrives_9_merged_3_9_coin100 merge_states_4_10)
    apply (simp add: leaves_5_pta leaves_9_pta leaves_5_merged_4_10 arrives_9_merged_4_10)
    by (simp add: merge_vend_coke_vend_pepsi nondeterministic_pairs_merged_vends nondeterminism_def)
qed

lemma scoring_2: "sorted_list_of_fset (score merged_vends naive_score) = [(0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 0, 6), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 1, 6), (0, 2, 3), (0, 2, 4),
     (0, 2, 5), (0, 2, 6), (0, 3, 4), (0, 3, 6), (0, 4, 5), (0, 4, 6), (0, 5, 6), (1, 3, 5), (2, 1, 2)]"
proof-
  have S_merged_vends: "S merged_vends = {|0, 1, 2, 3, 4, 5, 6|}"
    apply (simp add: S_def merged_vends_def)
    by auto
  have fset_S: "fset {|0, 1, 2, 3, 4, 5, 6|} = {0, 1, 2, 3, 4, 5, 6}"
    by simp
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S merged_vends |\<times>| Inference.S merged_vends) = {|
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 4), (3, 5), (3, 6),
    (4, 5), (4, 6),
    (5, 6)
  |}"
    apply (simp add: filtered_pairs_def ffilter_def fset_both_sides Abs_fset_inverse fprod_def)
    apply (simp only: S_merged_vends fprod_equiv fset_S Set.filter_def)
    apply standard
     apply clarify
     apply simp
      apply (case_tac "a=6")
       apply auto[1]
      apply simp
      apply (case_tac "a=5")
       apply auto[1]
      apply simp
      apply (case_tac "a=4")
       apply auto[1]
      apply simp
      apply (case_tac "a=3")
       apply auto[1]
      apply simp
      apply (case_tac "a=2")
        apply auto[1]
      apply simp
      apply (case_tac "a=1")
        apply auto[1]
     apply simp
    apply clarify
    apply safe
    by auto
  have Two_nat_def: "2 = Suc (Suc 0)"
    by simp
  have scores: "score merged_vends naive_score = {|(0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 0, 6), (2, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 1, 6),
     (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 2, 6), (0, 3, 4), (1, 3, 5), (0, 3, 6), (0, 4, 5), (0, 4, 6), (0, 5, 6)|}"
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def merged_vends_def fimage_def)
    apply (simp add: naive_score_empty set_equiv)
    apply (simp add: naive_score_def fprod_def)
    apply (simp add: transitions selectGeneral_def vend_general_def Abs_fset_inverse)
    by (simp add: One_nat_def Two_nat_def)
  show ?thesis
    by (simp add: scores sorted_list_of_fset_def)
qed

definition merged_1_2 :: iEFSM where
  "merged_1_2 = {|(0, (0, 1), selectGeneral), (2, (1, 1), coin50_50),  (4, (1, 3), coin50_100), (5, (3, 4), vend_general),
                                              (3, (1, 5), coin100_100), (6, (5, 6), vend_general)|}"

lemma merge_states_1_2: "merge_states 1 2 merged_vends = merged_1_2"
  by (simp add: merge_states_def merge_states_aux_def merged_vends_def merged_1_2_def)

lemma nondeterministic_pairs_merged_1_2: "nondeterministic_pairs merged_1_2 = {|(1, (1, 3), (coin50_50, 2), coin50_100, 4)|}"
proof-
  have minus_1: "{|(1, coin50_50, 2), (3, coin50_100, 4), (5, coin100_100, 3)|} |-| {|(3, coin50_100, 4)|} = {|(1, coin50_50, 2), (5, coin100_100, 3)|}"
    apply (simp add: transitions)
    by auto
  have minus_2: "{|(1, coin50_50, 2), (3, coin50_100, 4), (5, coin100_100, 3)|} |-| {|(5, coin100_100, 3)|} = {|(1, coin50_50, 2), (3, coin50_100, 4)|}"
    apply (simp add: transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, coin50_50, 2), (3, coin50_100, 4), (5, coin100_100, 3)|} = {|(1, (1, 5), (coin50_50, 2), coin100_100, 3), (1, (3, 5), (coin50_100, 4), coin100_100, 3), (1, (1, 3), (coin50_50, 2), coin50_100, 4),
      (1, (3, 5), (coin50_100, 4), coin100_100, 3), (1, (1, 3), (coin50_50, 2), coin50_100, 4),
      (1, (1, 5), (coin50_50, 2), coin100_100, 3)|}"
    by (simp add: state_nondeterminism_def minus_1 minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_2_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
                       apply (simp_all add: choices)
    by (simp add: transitions less_transition_ext_def less_aexp_def)
qed

lemma merge_states_1_3: "merge_states 1 3 merged_1_2 = merged_1_3"
  by (simp add: merge_states_def merge_states_aux_def merged_1_2_def merged_1_3_def)

lemma step_merged_1_3_select: "length b = 1 \<Longrightarrow> step (tm merged_1_3) 0 Map.empty ''select'' b = Some (selectGeneral, 1, [], <R 1 := hd b>)"
proof-
  assume premise: "length b = 1"
  have possible_steps: "possible_steps (tm merged_1_3) 0 Map.empty ''select'' b = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_def Set.filter_def)
    apply safe
            apply (simp_all add: selectGeneral_def transitions vend_general_def premise)
    by force
  show ?thesis
    apply (simp add: step_def possible_steps)
    apply (simp add: selectGeneral_def)
    apply (rule ext)
    by (simp add: hd_input2state premise)
qed

definition r1_true :: "context" where
  "r1_true = \<lbrakk>V (R 1) \<mapsto> Bc True\<rbrakk>"

lemma posterior_selectGeneral: "posterior \<lbrakk>\<rbrakk> selectGeneral = r1_true"
  apply (simp add: posterior_def selectGeneral_def remove_input_constraints_def r1_true_def)
  apply (rule ext)
  by simp

lemma posterior_selectGeneral2: "posterior r1_true selectGeneral = r1_true"
proof-
  have consistent_medial:  "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True\<rbrakk>"
    by (simp add: consistent_def consistent_empty_4)
  show ?thesis
  apply (simp add: posterior_def selectGeneral_def remove_input_constraints_def r1_true_def Let_def consistent_medial)
  apply (rule ext)
    by simp
qed

lemma posterior_r1_true_coin50_50: "posterior r1_true coin50_50 = r1_true"
proof-
  have consistent_medial: "consistent (medial r1_true (Guard coin50_50))"
    apply (simp add: consistent_def coin50_50_def r1_true_def)
    apply (rule_tac x="<R 1 := d, I 1 := Num 50>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial remove_input_constraints_def)
    apply (rule ext)
    by (simp add: coin50_50_def r1_true_def)
qed

lemma posterior_r1_true_coin50_100: "posterior r1_true coin50_100 = r1_true"
proof-
  have consistent_medial: "consistent (medial r1_true (Guard coin50_100))"
    apply (simp add: consistent_def coin50_100_def r1_true_def)
    apply (rule_tac x="<R 1 := d, I 1 := Num 50>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial remove_input_constraints_def)
    apply (rule ext)
    by (simp add: coin50_100_def r1_true_def)
qed

lemma posterior_r1_true_coin100_100: "posterior r1_true coin100_100 = r1_true"
proof-
  have consistent_medial: "consistent (medial r1_true (Guard coin100_100))"
    apply (simp add: consistent_def coin100_100_def r1_true_def)
    apply (rule_tac x="<R 1 := d, I 1 := Num 100>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial remove_input_constraints_def)
    apply (rule ext)
    by (simp add: coin100_100_def r1_true_def)
qed

lemma posterior_r1_true_vend_general: "posterior r1_true vend_general = r1_true"
proof-
  have consistent_medial: "consistent (medial r1_true (Guard vend_general))"
    apply (simp add: consistent_def vend_general_def r1_true_def)
    apply (rule_tac x="<R 1 := d, I 1 := Num 100>" in exI)
    by (simp add: consistent_empty_4)
  show ?thesis
    apply (simp add: posterior_def Let_def consistent_medial remove_input_constraints_def)
    apply (rule ext)
    by (simp add: vend_general_def r1_true_def)
qed

lemma posterior_sequence_merged_1_3: "\<forall>r s. posterior_sequence r1_true (tm merged_1_3) s r p = r1_true"
proof(induct p)
  case Nil
  then show ?case
    by simp
next
  have regsimp: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_transitions: "\<forall>aba. aba \<noteq> selectGeneral \<longrightarrow>
       aba \<noteq> coin50_50 \<longrightarrow>
       aba \<noteq> coin50_100 \<longrightarrow>
       aba \<noteq> coin100_100 \<longrightarrow>
       aba \<noteq> vend_general \<longrightarrow>
       (\<nexists>fst. (fst, aba) |\<in>| (tm merged_1_3))"
  by (simp add: tm_def merged_1_3_def)
  case (Cons a as)
  then show ?case
    apply clarify
    apply (case_tac a)
    apply (simp add: regsimp)
    apply (case_tac "step (tm merged_1_3) s r aa b")
     apply simp
    apply simp
    apply (case_tac aaa)
    apply simp
    apply (case_tac "ab = selectGeneral")
     apply (simp add: posterior_selectGeneral2)
    apply (case_tac "ab = coin50_50")
    apply (simp add: posterior_r1_true_coin50_50)
    apply (case_tac "ab = coin50_100")
     apply (simp add: posterior_r1_true_coin50_100)
    apply (case_tac "ab = coin100_100")
     apply (simp add: posterior_r1_true_coin100_100)
    apply (case_tac "ab = vend_general")
     apply (simp add: posterior_r1_true_vend_general)
    apply (simp add: step_def)
    apply (case_tac "fis_singleton (possible_steps (tm merged_1_3) s r aa b)")
     defer
     apply simp
    apply (case_tac "fthe_elem (possible_steps (tm merged_1_3) s r aa b)")
    apply simp
    apply clarify
    apply simp
    using possible_transitions singleton_dest by blast
qed

lemma merged_1_3_anterior_context: "accepts_trace (tm merged_vends) p \<and>
       gets_us_to 2 (tm merged_vends) 0 Map.empty p \<longrightarrow>
       anterior_context (tm merged_1_3) p = r1_true"
proof(induct p)
  case Nil
  then show ?case
    by (simp add: no_further_steps)
next
  have must_do_select: "\<forall>aa b p. \<not> (aa = ''select'' \<and> length b = 1) \<longrightarrow>
       \<not>accepts_trace (tm merged_vends) ((aa, b) # p)"
  proof-
    have possible_steps: "\<And>a ba.
       a = ''select'' \<longrightarrow> length ba \<noteq> 1 \<Longrightarrow>
       possible_steps (tm merged_vends) 0 Map.empty a ba = {||}"
      apply (simp add: possible_steps_fst)
      apply (simp add: tm_def merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: selectGeneral_def)
    show ?thesis
      apply (simp add: accepts_trace_def)
      apply clarify
      apply (rule accepts.cases)
        apply simp
       apply simp
      apply clarify
      by (simp add: step_def possible_steps)
  qed
  case (Cons a p)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (case_tac "aa = ''select'' \<and> length b = 1")
     apply (simp add: anterior_context_def step_merged_1_3_select posterior_selectGeneral)
     apply (simp add: posterior_sequence_merged_1_3)
    by (simp add: must_do_select)
qed

lemma merged_1_3_anterior_context_1: "accepts_trace (tm merged_vends) p \<and>
       gets_us_to 1 (tm merged_vends) 0 Map.empty p \<longrightarrow>
       anterior_context (tm merged_1_3) p = r1_true"
proof(induct p)
  case Nil
  then show ?case
    by (simp add: no_further_steps)
next
  have must_do_select: "\<forall>aa b p. \<not> (aa = ''select'' \<and> length b = 1) \<longrightarrow>
       \<not>accepts_trace (tm merged_vends) ((aa, b) # p)"
  proof-
    have possible_steps: "\<And>a ba.
       a = ''select'' \<longrightarrow> length ba \<noteq> 1 \<Longrightarrow>
       possible_steps (tm merged_vends) 0 Map.empty a ba = {||}"
      apply (simp add: possible_steps_fst)
      apply (simp add: tm_def merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: selectGeneral_def)
    show ?thesis
      apply (simp add: accepts_trace_def)
      apply clarify
      apply (rule accepts.cases)
        apply simp
       apply simp
      apply clarify
      by (simp add: step_def possible_steps)
  qed
  case (Cons a p)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (case_tac "aa = ''select'' \<and> length b = 1")
     apply (simp add: anterior_context_def step_merged_1_3_select posterior_selectGeneral)
     apply (simp add: posterior_sequence_merged_1_3)
    by (simp add: must_do_select)
qed

lemma no_direct_subsumption_coin50_50_coin_50_100: "\<not> directly_subsumes (tm merged_vends) (tm merged_1_3) 2 coin50_50 coin50_100"
proof-
  have possible_steps_select: "possible_steps (tm merged_vends) 0 Map.empty ''select'' [d] = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force
  have possible_steps_coin: "\<forall>r. possible_steps (tm merged_vends) 1 r ''coin'' [Num 50] = {|(2, coin50_50)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions)
    by force
  have subsumption_violation: "(\<exists>i r. satisfies_context r r1_true \<and>
           apply_guards (Guard coin50_100) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin50_100) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin50_50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))))"
    apply (simp add: transitions satisfies_context_def consistent_def datastate2context_def r1_true_def)
    apply standard
     apply (rule_tac x="<R 1 := d>" in exI)
     apply (rule_tac x="<R 1 := d>" in exI)
     apply clarify
     defer
     apply (meson input2state.simps(2))
    apply (case_tac r)
       apply simp
      apply (case_tac x2)
    by auto
    show ?thesis
    apply (simp add: directly_subsumes_def merged_1_3_anterior_context accepts_trace_def)
    apply (rule_tac x="[(''select'', [d]), (''coin'', [Num 50])]" in exI)
    apply standard
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select)
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_coin)
     apply (simp add: accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_select)
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_coin)
     apply (simp add: gets_us_to.base)
      by (simp add: subsumes_def subsumption_violation)
  qed

lemma no_direct_subsumption_coin50_100_coin_50_50: "\<not> directly_subsumes (tm merged_vends) (tm merged_1_3) 1 coin50_100 coin50_50"
proof-
  have possible_steps_select: "possible_steps (tm merged_vends) 0 Map.empty ''select'' [d] = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force
  have subsumption_violation: "\<exists>i r. satisfies_context r r1_true \<and>
           apply_guards (Guard coin50_50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs coin50_50) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n))) \<noteq>
           apply_outputs (Outputs coin50_100) (case_vname (\<lambda>n. input2state i 1 (I n)) (\<lambda>n. r (R n)))"
    apply (simp add: transitions satisfies_context_def consistent_def datastate2context_def r1_true_def)
    apply standard
     apply (rule_tac x="<R 1 := d>" in exI)
     apply (rule_tac x="<R 1 := d>" in exI)
     apply clarify
     defer
     apply (meson input2state.simps(2))
    apply (case_tac r)
       apply simp
      apply (case_tac x2)
    by auto
  show ?thesis
    apply (simp add: directly_subsumes_def merged_1_3_anterior_context_1 accepts_trace_def)
    apply (rule_tac x="[(''select'', [d])]" in exI)
    apply standard
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps_select)
     apply (simp add: accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps_select)
     apply (simp add: gets_us_to.base)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_3: "nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 1 3 <R 1 := hd b, R 2 := Num 100> <R 1 := hd b> t H_merged_1_2"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have regsimp_1: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  have regsimp_2: "\<forall>d. (\<lambda>a. if a = R 2 then Some (Num 100) else if a = R 1 then Some d else None) = <R 1 := d, R 2 := Num 100>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_steps_merged_vends_vend: "\<forall>r. possible_steps (tm merged_vends) 3 r ''vend'' [] = {|(4, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: merged_vends_def Set.filter_def tm_def)
    apply safe
             apply (simp_all add: transitions vend_general_def)
    by force
  have possible_steps_merged_1_3_coin_vend: "\<forall>r. possible_steps (tm merged_1_3_coin) 1 r ''vend'' [] = {|(4, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
           apply (simp_all add: transitions coinGeneral_def vend_general_def)
    by force
  have possible_steps_merged_vends_4: "\<forall>r l i. possible_steps (tm merged_vends) 4 r l i = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: merged_vends_def Set.filter_def tm_def)
  have possible_steps_not_vend: "\<And>aa ba.
       aa = ''vend'' \<longrightarrow> ba \<noteq> [] \<Longrightarrow>
       possible_steps (tm merged_vends) 3 (\<lambda>a. if a = R 1 then Some (hd b) else None) aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: merged_vends_def Set.filter_def tm_def)
    apply safe
    by (simp_all add: transitions vend_general_def)
  case (Cons a t)
  then show ?case
    apply (case_tac "a= (''vend'', [])")
    apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_2_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_vend)
       apply (simp add: possible_steps_merged_1_3_coin_vend)
      apply (simp add: vend_general_def)
     apply (simp add: regsimp_1 vend_general_def regsimp_2)
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
    apply (simp add: nondeterministic_step_def possible_steps_merged_vends_4)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_not_vend)
qed


lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_2: "nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 1 2 <R 1 := hd b, R 2 := Num 50> <R 1 := hd b> t H_merged_1_2"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_1_3_coin_1_coin: "\<forall>r. possible_steps (tm merged_1_3_coin) 1 r ''coin'' [Num 50] = {|(1, coinGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
           apply (simp_all add: coinGeneral_def transitions selectGeneral_2_def vend_general_def)
    by force
  have regsimp_1: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  have regsimp_2: "\<forall>d. (\<lambda>x. if x = R 2
          then aval (snd (R 2, Plus (V (I 1)) (V (R 2))))
                (case_vname (\<lambda>n. input2state [Num 50] 1 (I n))
                  (\<lambda>n. if R n = R 2 then Some (Num 50) else if R n = R 1 then Some d else None))
          else EFSM.apply_updates []
                (case_vname (\<lambda>n. input2state [Num 50] 1 (I n))
                  (\<lambda>n. if R n = R 2 then Some (Num 50) else if R n = R 1 then Some d else None))
                (\<lambda>a. if a = R 2 then Some (Num 50) else if a = R 1 then Some d else None) x) = <R 1 := d, R 2 := Num 100>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_steps_not_coin: "\<And>aa ba r.
       aa = ''coin'' \<longrightarrow> ba \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm merged_vends) 2 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: coin50_100_def hd_input2state)
    by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  case (Cons a t)
  then show ?case
    apply (case_tac "a = (''coin'', [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_2_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin50_2)
       apply (simp add: possible_steps_merged_1_3_coin_1_coin)
      apply simp
     apply (simp add: coinGeneral_def coin50_100_def regsimp_1 regsimp_2)
     apply (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_3)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_not_coin)
qed

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_5_5: "nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 5 5 <R 1 := hd b, R 2 := Num 0> <R 1 := hd b> t H_merged_1_2"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_vends_vend: "\<forall>r. possible_steps (tm merged_vends) 5 r ''vend'' [] = {|(6, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
             apply (simp_all add: vend_general_def)
    by force
  have possible_steps_other_vend: "\<forall>r. possible_steps (tm merged_1_3_coin) 5 r ''vend'' [] = {|(6, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
             apply (simp_all add: vend_general_def)
    by force
  have stop: "\<forall>r aaa ba. possible_steps (tm merged_vends) 6 r aaa ba = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def merged_vends_def Set.filter_def)
  have stop_2: "\<And>aa ba.
       aa = ''vend'' \<longrightarrow> ba \<noteq> [] \<Longrightarrow>
       possible_steps (tm merged_vends) 5 (\<lambda>a. if a = R 1 then Some (hd b) else None) aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def vend_general_def)
    by auto
  case (Cons a t)
  then show ?case
    apply (case_tac "a=(''vend'', [])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_2_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_vend)
       apply (simp add: possible_steps_other_vend)
      apply simp
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
    by (simp add: nondeterministic_step_def stop_2)
qed

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_1: "nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 1 1 <R 1 := hd b, R 2 := Num 0> <R 1 := hd b> t H_merged_1_2"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have regsimp_1: "\<forall>d. (\<lambda>a. if a = R 1 then Some d else None) = <R 1 := d>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_steps_merged_1_3_coin_coin: "\<forall>r. possible_steps (tm merged_1_3_coin) 1 r ''coin'' [Num 50] = {|(1, coinGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
           apply (simp_all add: coinGeneral_def vend_general_def transitions)
    by force
  have regsimp_2: "\<forall>d. (\<lambda>x. if x = R 2
          then aval (snd (R 2, Plus (V (I 1)) (V (R 2))))
                (case_vname (\<lambda>n. input2state [Num 50] 1 (I n))
                  (\<lambda>n. if R n = R 2 then Some (Num 0) else if R n = R 1 then Some d else None))
          else EFSM.apply_updates []
                (case_vname (\<lambda>n. input2state [Num 50] 1 (I n))
                  (\<lambda>n. if R n = R 2 then Some (Num 0) else if R n = R 1 then Some d else None))
                (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some d else None) x) = <R 1 := d, R 2 := Num 50>"
    apply clarify
    apply (rule ext)
    by simp
  have possible_steps_coin_100: "\<forall>r. possible_steps (tm merged_vends) 1 r ''coin'' [Num 100] = {|(5, coin100_100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions)
    by force
  have possible_steps_merged_1_3_coin_coin100: "\<forall>r. possible_steps (tm merged_1_3_coin) 1 r ''coin'' [Num 100] = {|(1, coinGeneral), (5, coin100_100)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
               apply (simp_all add: transitions coinGeneral_def vend_general_def)
    apply force
    by force
  have go_to_5: "\<forall>r. (5, coin100_100) |\<in>|
    possible_steps (tm merged_1_3_coin) 1 r ''coin'' [Num 100]"
    by (simp add: possible_steps_merged_1_3_coin_coin100)
  have regsimp_3: "\<forall>d. (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some d else None) = <R 1 := d, R 2 := Num 0>"
    apply clarify
    apply (rule ext)
    by simp
  have stop: "\<And>aa ba.
       aa = ''coin'' \<longrightarrow> ba \<noteq> [Num 50] \<Longrightarrow>
       aa = ''coin'' \<longrightarrow> ba \<noteq> [Num 100] \<Longrightarrow>
       possible_steps (tm merged_vends) 1 (\<lambda>a. if a = R 1 then Some (hd b) else None) aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: coin50_50_def coin100_100_def)
    apply clarify
    apply simp
    apply (case_tac "bb=2")
     apply (simp add: hd_input2state)
     apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    apply (case_tac "bb=5")
     apply (simp add: hd_input2state)
     apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    by simp
  case (Cons a t)
  then show ?case
    apply (case_tac "a = (''coin'', [Num 50])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_2_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin50_1)
       apply (simp add: possible_steps_merged_1_3_coin_coin)
      apply (simp add: coinGeneral_def regsimp_2)
     apply (simp add: transitions regsimp_1)
     apply (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_2)
    apply (case_tac "a = (''coin'', [Num 100])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_2_def)
        apply (simp add: nondeterministic_step_def possible_steps_coin_100)
    using go_to_5 apply auto[1]
      apply simp
     apply (simp add: regsimp_1 regsimp_3 coin100_100_def)
     apply (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_5_5)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop)
qed

lemma nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_0_0:"nondeterministic_simulates_trace (tm merged_1_3_coin) (tm merged_vends) 0 0 Map.empty Map.empty t H_merged_1_2"
proof(induct t)
  case Nil
  then show ?case
  by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_vends_select: "\<forall>b. length b = 1 \<longrightarrow> possible_steps (tm merged_vends) 0 Map.empty ''select'' b = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force
  have possible_steps_merged_1_3_coin_select: "\<forall>b. length b = 1 \<longrightarrow> possible_steps (tm merged_1_3_coin) 0 Map.empty ''select'' b = {|(1, selectGeneral_2)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_3_coin_def Set.filter_def)
    apply safe
            apply (simp_all add: selectGeneral_2_def)
    by force
  have regsimp_1: "\<forall>b. length b = 1 \<longrightarrow>(\<lambda>a. if a = R 1 then aval (snd (R 1, V (I 1))) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty)
             else EFSM.apply_updates [(R 2, L (Num 0))] (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty a) = <R 1 := hd b, R 2 := Num 0>"
    apply clarify
    apply (rule ext)
    by (simp add: hd_input2state)
  have regsimp_2: "\<forall>b. length b = 1 \<longrightarrow> (\<lambda>a. if a = R 1 then aval (snd (R 1, V (I 1))) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty)
             else EFSM.apply_updates [] (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty a) = <R 1 := hd b>"
    apply clarify
    apply (rule ext)
    by (simp add: hd_input2state)
  have stop: "\<And>aa b.
       aa = ''select'' \<longrightarrow> length b \<noteq> 1 \<Longrightarrow>
       possible_steps (tm merged_vends) 0 Map.empty aa b = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
    by (simp_all add: transitions selectGeneral_def)
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (case_tac "aa = ''select'' \<and> length b = 1")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_2_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_select)
       apply (simp add: possible_steps_merged_1_3_coin_select)
      apply simp
     apply (simp add: selectGeneral_2_def selectGeneral_def)
     apply (simp add: regsimp_1 regsimp_2)
     apply (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_1_1)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop)
qed

lemma nondeterministic_simulates_merged_1_3_coin_merged_vends: "nondeterministic_simulates (tm merged_1_3_coin) (tm merged_vends) H_merged_1_2"
  apply (simp add: nondeterministic_simulates_def)
  by (simp add: nondeterministic_simulates_trace_merged_1_3_coin_merged_vends_0_0)

lemma nondeterministic_pairs_merged_1_3_coin: "nondeterministic_pairs merged_1_3_coin = {|(1, (1, 5), (coinGeneral, 2), coin100_100, 3)|}"
proof-
  have minus_1: "{|(1, coinGeneral, 2), (4, vend_general, 5), (5, coin100_100, 3)|} |-| {|(4, vend_general, 5)|} = {|(1, coinGeneral, 2), (5, coin100_100, 3)|}"
    apply (simp add: transitions coinGeneral_def vend_general_def)
    by auto
  have minus_2: "{|(1, coinGeneral, 2), (4, vend_general, 5), (5, coin100_100, 3)|} |-| {|(5, coin100_100, 3)|} = {|(1, coinGeneral, 2), (4, vend_general, 5)|}"
    apply (simp add: transitions coinGeneral_def vend_general_def)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, coinGeneral, 2), (4, vend_general, 5), (5, coin100_100, 3)|} = {|(1, (1, 5), (coinGeneral, 2), coin100_100, 3), (1, (4, 5), (vend_general, 5), coin100_100, 3),
      (1, (1, 4), (coinGeneral, 2), vend_general, 5), (1, (4, 5), (vend_general, 5), coin100_100, 3),
      (1, (1, 4), (coinGeneral, 2), vend_general, 5), (1, (1, 5), (coinGeneral, 2), coin100_100, 3)|}"
    by (simp add: state_nondeterminism_def minus_1 minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_3_coin_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def Set.filter_def fset_both_sides Abs_fset_inverse)
    apply safe
                 apply (simp_all add: choices)
    by (simp add: coinGeneral_def transitions less_transition_ext_def)
qed

definition merged_4_6 :: iEFSM where
  "merged_4_6 = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general), (6, (1, 4), vend_general)|}"

definition final :: iEFSM where
  "final = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral), (5, (1, 4), vend_general)|}"

lemma directly_subsumes_vend_general_self: "directly_subsumes (tm merged_vends) (tm merged_4_6) 5 vend_general vend_general"
proof-
  have self_subsumpion: "\<forall>c. subsumes c vend_general vend_general"
    by (simp add: subsumes_def vend_general_def)
  show ?thesis
    by (simp add: directly_subsumes_def self_subsumpion)
qed

lemma nondeterministic_pairs_merged_1_5_coin: "nondeterministic_pairs merged_1_5_coin = {|(1, (4, 6), (vend_general, 5), vend_general, 6)|}"
proof-
  have minus_1: "{|(1, coinGeneral, 2::nat), (4, vend_general, 5), (6, vend_general, 6)|} |-| {|(4, vend_general, 5)|} = {|(1, coinGeneral, 2), (6, vend_general, 6)|}"
    apply (simp add: vend_general_def coinGeneral_def)
    by auto
  have minus_2: "{|(1, coinGeneral, 2::nat), (4, vend_general, 5), (6, vend_general, 6)|} |-| {|(6, vend_general, 6)|} = {|(1, coinGeneral, 2), (4, vend_general, 5)|}"
    apply (simp add: vend_general_def coinGeneral_def)
    by auto
  have state_nondeterminim_1: "state_nondeterminism 1 {|(1, coinGeneral, 2), (4, vend_general, 5), (6, vend_general, 6)|} = {|(1, (1, 6), (coinGeneral, 2), vend_general, 6), (1, (4, 6), (vend_general, 5), vend_general, 6),
      (1, (1, 4), (coinGeneral, 2), vend_general, 5), (1, (4, 6), (vend_general, 5), vend_general, 6),
      (1, (1, 4), (coinGeneral, 2), vend_general, 5), (1, (1, 6), (coinGeneral, 2), vend_general, 6)|}"
    by (simp add: state_nondeterminism_def minus_1 minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def merged_1_5_coin_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminim_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: choices)
qed

lemma no_direct_subsumption_coinGeneral_coin100_100:  "\<not>directly_subsumes (tm merged_vends) (tm merged_1_5) 1 coinGeneral coin100_100"
proof-
  have possible_steps: "\<forall>d. possible_steps (tm merged_vends) 0 Map.empty ''select'' [d] = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions selectGeneral_def)
    by force
  have possible_steps_merged_1_5: "\<forall>b. length b = 1 \<longrightarrow> possible_steps (tm merged_1_5) 0 Map.empty ''select'' b = {|(1, selectGeneral_2)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_5_def Set.filter_def)
    apply safe
          apply (simp_all add: selectGeneral_2_def)
    by force
  have posterior_empty_selectGeneral_2: "posterior \<lbrakk>\<rbrakk> selectGeneral_2 = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
    apply (rule ext)
    by (simp add: posterior_def selectGeneral_2_def remove_input_constraints_def)
  have medial_coin100_100: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin100_100) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> Eq (Num 100)\<rbrakk>"
    apply (rule ext)
    by (simp add: coin100_100_def)
  have consistent_medial: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> cexp.Eq (Num 100)\<rbrakk>"
    apply (simp add: consistent_def)
    apply (rule_tac x="<R 1 := d, R 2 := Num 0, I 1 := Num 100>" in exI)
    by (simp add: consistent_empty_4)
  have medial_coinGeneral: "\<forall>c. medial c (Guard coinGeneral) = c"
    apply clarify
    apply (rule ext)
    by (simp add: coinGeneral_def)
  have subsumption_violation: " (\<exists>r i. cval (posterior (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin100_100)) coinGeneral r) i = Some True \<and>
           cval (posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin100_100 r) i \<noteq> Some True \<and>
           posterior \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin100_100 r \<noteq> Undef)"
    apply (rule_tac x="V (R 2)" in exI)
    apply (rule_tac x="Num 100" in exI)
    apply (simp add: medial_coin100_100 posterior_def medial_coinGeneral Let_def consistent_medial)
    by (simp add: remove_input_constraints_def coinGeneral_def valid_def satisfiable_def coin100_100_def)
  show ?thesis
    apply (simp add: directly_subsumes_def accepts_trace_def)
    apply (rule_tac x="[(''select'', [d])]" in exI)
    apply standard
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def step_def possible_steps_merged_1_5 posterior_empty_selectGeneral_2)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma no_direct_subsumption_coin100_100_coinGeneral: "\<not> directly_subsumes (tm merged_vends) (tm merged_1_5) 1 coin100_100 coinGeneral"
proof-
have possible_steps: "\<forall>d. possible_steps (tm merged_vends) 0 Map.empty ''select'' [d] = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply safe
              apply (simp_all add: transitions selectGeneral_def)
    by force
  have possible_steps_merged_1_5: "\<forall>b. length b = 1 \<longrightarrow> possible_steps (tm merged_1_5) 0 Map.empty ''select'' b = {|(1, selectGeneral_2)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_1_5_def Set.filter_def)
    apply safe
          apply (simp_all add: selectGeneral_2_def)
    by force
  have posterior_empty_selectGeneral_2: "posterior \<lbrakk>\<rbrakk> selectGeneral_2 = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
    apply (rule ext)
    by (simp add: posterior_def selectGeneral_2_def remove_input_constraints_def)
  have medial_coin100_100: "medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin100_100) = \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0), V (I 1) \<mapsto> Eq (Num 100)\<rbrakk>"
    apply (rule ext)
    by (simp add: coin100_100_def)
  have medial_coinGeneral: "\<forall>c. medial c (Guard coinGeneral) = c"
    apply clarify
    apply (rule ext)
    by (simp add: coinGeneral_def)
  have subsumption_violation: "\<exists>r i. cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coinGeneral) r) i = Some True \<and>
           cval (medial \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> (Guard coin100_100) r) i \<noteq> Some True"
    apply (simp add: medial_coinGeneral medial_coin100_100)
    by auto
  show ?thesis
 apply (simp add: directly_subsumes_def accepts_trace_def)
    apply (rule_tac x="[(''select'', [d])]" in exI)
    apply standard
     apply (rule accepts.step)
      apply (simp add: step_def possible_steps)
     apply (rule accepts.base)
    apply standard
     apply (rule gets_us_to.step_some)
      apply (simp add: step_def possible_steps)
     apply (simp add: gets_us_to.base)
    apply (simp add: anterior_context_def step_def possible_steps_merged_1_5 posterior_empty_selectGeneral_2)
    by (simp add: subsumes_def subsumption_violation)
qed

lemma nondeterministic_pairs_final: "nondeterministic_pairs final = {||}"
proof-
  have minus_1: "{|(1, coinGeneral, 2), (4, vend_general, 5)|} |-| {|(4, vend_general, 5)|} = {|(1, coinGeneral, 2)|}"
    apply (simp add: coinGeneral_def vend_general_def)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(1, coinGeneral, 2), (4, vend_general, 5)|} = {|(1, (1, 4), (coinGeneral, 2), vend_general, 5)|}"
    by (simp add: state_nondeterminism_def minus_1)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def S_def final_def)
    apply (simp add: outgoing_transitions_def fimage_def state_nondeterminism_1)
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    by (simp add: choice_def coinGeneral_def vend_general_def)
qed

lemma possible_steps_merged_1_5_coin_coin: "\<forall>r. possible_steps (tm merged_1_5_coin) 1 r ''coin'' [Num n] = {|(1, coinGeneral)|}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def merged_1_5_coin_def Set.filter_def)
  apply safe
       apply (simp_all add: coinGeneral_def vend_general_def selectGeneral_2_def)
  by force

lemma possible_steps_merged_1_5_coin_vend: "possible_steps (tm merged_1_5_coin) 1 r ''vend'' [] = {|(4, vend_general), (6, vend_general)|}"
  apply (simp add: possible_steps_fst)
  apply (simp add: tm_def merged_1_5_coin_def Set.filter_def)
  apply safe
           apply (simp_all add: vend_general_def coinGeneral_def)
   apply force
  by force

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_3: "\<forall>r r'. nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 1 3 r r' t H_merged_1_5"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_vends_4: "\<forall>r l i. possible_steps (tm merged_vends) 4 r l i = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: merged_vends_def Set.filter_def tm_def)
  have possible_steps_not_vend: "\<And>aa ba r.
       aa = ''vend'' \<longrightarrow> ba \<noteq> [] \<Longrightarrow>
       possible_steps (tm merged_vends) 3 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: vend_general_def)
    by auto
  case (Cons a t)
  then show ?case
    apply clarify
    apply (case_tac "a = (''vend'', [])")
    apply simp
    apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_5_def)
        apply (simp add: nondeterministic_step_def possible_steps_vend)
       apply (simp add: possible_steps_merged_1_5_coin_vend)
       apply auto[1]
      apply simp
     apply (case_tac t)
      apply (simp add: nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def possible_steps_merged_vends_4)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_not_vend)
qed


lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_2: "\<forall>r r'. nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 1 2 r r' t H_merged_1_5"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_not_coin: "\<And>aa ba r.
       aa = ''coin'' \<longrightarrow> ba \<noteq> [Num 50] \<Longrightarrow>
       possible_steps (tm merged_vends) 2 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: coin50_100_def hd_input2state)
    by (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
  case (Cons a t)
  then show ?case
    apply clarify
    apply (case_tac "a = (''coin'', [Num 50])")
    apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_5_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin50_2)
       apply (simp add: possible_steps_merged_1_5_coin_coin)
      apply simp
     apply (simp add: nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_3)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def possible_steps_not_coin)
qed

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_5: "\<forall>r r'. nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 1 5 r r' t H_merged_1_5"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_vend: "\<forall>r. possible_steps (tm merged_vends) 5 r ''vend'' [] = {|(6, vend_general)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: transitions vend_general_def)
    by force
  have stop: "\<forall>r aaa ba. possible_steps (tm merged_vends) 6 r aaa ba = {||}"
    apply (simp add: possible_steps_fst)
    by (simp add: tm_def merged_vends_def Set.filter_def)
  have stop_2: "\<And>aa ba r.
       aa = ''vend'' \<longrightarrow> ba \<noteq> [] \<Longrightarrow>
       possible_steps (tm merged_vends) 5 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def vend_general_def)
    by auto
  case (Cons a t)
  then show ?case
    apply clarify
    apply (case_tac "a = (''vend'', [])")
    apply simp
    apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_5_def)
        apply (simp add: nondeterministic_step_def possible_steps_vend)
       apply (simp add: possible_steps_merged_1_5_coin_vend)
       apply auto[1]
      apply simp
     apply (case_tac t)
      apply simp
      apply (rule nondeterministic_simulates_trace.base)
     apply (case_tac aa)
     apply simp
     apply (rule nondeterministic_simulates_trace.step_none)
     apply (simp add: nondeterministic_step_def stop)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop_2)
qed

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_1: "\<forall>r r'. nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 1 1 r r' t H_merged_1_5"
proof (induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have stop: "\<And>aa ba r.
       aa = ''coin'' \<longrightarrow> ba \<noteq> [Num 50] \<Longrightarrow>
       aa = ''coin'' \<longrightarrow> ba \<noteq> [Num 100] \<Longrightarrow>
       possible_steps (tm merged_vends) 1 r aa ba = {||}"
    apply (simp add: possible_steps_fst)
    apply (simp add: tm_def merged_vends_def Set.filter_def)
    apply (simp add: coin50_50_def coin100_100_def)
    apply clarify
    apply simp
    apply (case_tac "b=2")
     apply (simp add: hd_input2state)
     apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    apply (case_tac "b=5")
     apply (simp add: hd_input2state)
     apply (metis One_nat_def length_0_conv length_Suc_conv list.sel(1))
    by simp
  case (Cons a t)
  then show ?case
    apply clarify
    apply (case_tac "a = (''coin'', [Num 50])")
    apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_5_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin50_1)
       apply (simp add: possible_steps_merged_1_5_coin_coin)
      apply simp
     apply (simp add: nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_2)
    apply (case_tac "a = (''coin'', [Num 100])")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_5_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_coin100)
       apply (simp add: possible_steps_merged_1_5_coin_coin)
      apply simp
    apply (simp add: nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_5)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop)
qed

lemma nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_0_0: "nondeterministic_simulates_trace (tm merged_1_5_coin) (tm merged_vends) 0 0 Map.empty Map.empty t H_merged_1_5"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: nondeterministic_simulates_trace.base)
next
  have possible_steps_merged_vends_select: "\<forall>aa b. aa = ''select'' \<and> length b = 1 \<longrightarrow> possible_steps (tm merged_vends) 0 Map.empty ''select'' b = {|(1, selectGeneral)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: merged_vends_def tm_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_def)
    by force
  have possible_steps_merged_1_5_coin_select: "\<forall>aa b. aa = ''select'' \<and> length b = 1 \<longrightarrow> possible_steps (tm merged_1_5_coin) 0 Map.empty ''select'' b = {|(1, selectGeneral_2)|}"
    apply (simp add: possible_steps_fst)
    apply (simp add: merged_1_5_coin_def tm_def Set.filter_def)
    apply safe
              apply (simp_all add: selectGeneral_2_def)
    by force
    have stop: "\<And>a ba r.
       a = ''select'' \<longrightarrow> length ba \<noteq> 1 \<Longrightarrow>
       possible_steps (tm merged_vends) 0r a ba = {||}"
      apply (simp add: possible_steps_fst)
      apply (simp add: tm_def merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: selectGeneral_def)
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (case_tac "aa = ''select'' \<and> length b = 1")
     apply simp
     apply (rule nondeterministic_simulates_trace.step_some)
         apply (simp add: H_merged_1_5_def)
        apply (simp add: nondeterministic_step_def possible_steps_merged_vends_select)
       apply (simp add: possible_steps_merged_1_5_coin_select)
      apply simp
     apply (simp add: nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_1_1)
    apply (case_tac a)
    apply simp
    apply (rule nondeterministic_simulates_trace.step_none)
    by (simp add: nondeterministic_step_def stop)
qed

lemma merge_1_2: "merge merged_vends 1 2 generator modifier = Some final"
proof-
  have arrives_2_merged_1_2: "arrives 2 merged_1_2 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_2 = {|(2, (1, 1), coin50_50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_2_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_4_merged_1_2: "arrives 4 merged_1_2 = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_1_2 = {|(4, (1, 3), coin50_100)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_2_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have leaves_2_merged_vends: "leaves 2 merged_vends = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_vends = {|(2, (1, 2), coin50_50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_2_merged_1_3: "(leaves 2 merged_1_3 = 1) \<and> (arrives 2 merged_1_3 = 1)"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_3 = {|(2, (1, 1), coin50_50)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_3_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have leaves_4_merged_vends: "leaves 4 merged_vends = 2"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_vends = {|(4, (2, 3), coin50_100)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have arrives_4_merged_1_3: "arrives 4 merged_1_3 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (4, (a, b), ba)) merged_1_3 = {|(4, (1, 1), coin50_100)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_3_def Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merged_1_3_neq_merged_1_8: "merged_1_3 \<noteq> merged_1_8"
    apply (simp add: merged_1_3_def merged_1_8_def set_equiv)
    apply (simp only: set_nequiv_def)
    apply (rule_tac x="(5, (3, 4), vend_coke)" in exI)
    by simp
  have easy_merge: "easy_merge merged_vends merged_1_3 1 2 1 1 1 coin50_50 2 coin50_100 4 generator = None"
    apply (simp add: easy_merge_def generator_def no_direct_subsumption_coin50_50_coin_50_100)
    by (simp add: no_direct_subsumption_coin50_100_coin_50_50)
  have merge_vends: "merge_transitions merged_vends merged_1_3 1 2 1 1 1 coin50_50 2 coin50_100 4 generator modifier True = Some merged_1_3_coin"
    apply (simp add: merge_transitions_def easy_merge modifier_def merged_1_3_neq_merged_1_8)
    by (simp add: nondeterministic_simulates_merged_1_3_coin_merged_vends)
  have arrives_2_merged_1_3_coin: "arrives 2 merged_1_3_coin = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_3_coin =  {|(2, (1, 1), coinGeneral)|}"
      apply (simp add: ffilter_def merged_1_3_coin_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_3_merged_1_3_coin: "arrives 3 merged_1_3_coin = 5"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (3, (a, b), ba)) merged_1_3_coin = {|(3, (1, 5), coin100_100)|}"
      apply (simp add: ffilter_def merged_1_3_coin_def fset_both_sides Abs_fset_inverse Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_1_5:  "merge_states 1 5 merged_1_3_coin = merged_1_5"
    by (simp add: merge_states_def merge_states_aux_def merged_1_3_coin_def merged_1_5_def)
  have leaves_3_merged_vends: "leaves 3 merged_vends = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (3, (a, b), ba)) merged_vends = {|(3, (1, 5), coin100_100)|}"
      apply (simp add: ffilter_def merged_vends_def Abs_fset_inverse fset_both_sides Set.filter_def)
      apply safe
      by (simp_all add: transitions)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_2_merged_1_5: "leaves 2 merged_1_5= 1 \<and> arrives 2 merged_1_5 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (2, (a, b), ba)) merged_1_5 = {|(2, (1, 1), coinGeneral)|}"
      apply (simp add: ffilter_def merged_1_5_def Abs_fset_inverse fset_both_sides Set.filter_def)
      apply safe
      by (simp_all add: coinGeneral_def)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_3_merged_1_5: "arrives 3 merged_1_5 = 1"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (3, (a, b), ba)) merged_1_5 = {|(3, (1, 1), coin100_100)|}"
      apply (simp add: ffilter_def merged_1_5_def Abs_fset_inverse fset_both_sides Set.filter_def)
      apply safe
      by (simp_all add: coinGeneral_def)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have easy_merge_1_5: "easy_merge merged_vends merged_1_5 1 1 1 1 1 coinGeneral 2 coin100_100 3 generator = None"
  proof-
    have ffilter: "ffilter (\<lambda>x. snd x \<noteq> ((1, 1), coin100_100) \<and> snd x \<noteq> ((1, 1), coinGeneral)) merged_1_5 = {|(0, (0, 1), selectGeneral_2), (5, (1, 4), vend_general),
      (6, (1, 6), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_5_def Set.filter_def)
      by auto
    show ?thesis
      apply (simp add: easy_merge_def no_direct_subsumption_coinGeneral_coin100_100 no_direct_subsumption_coin100_100_coinGeneral)
      by (simp add: replace_transition_def ffilter merged_1_5_coin_def generator_def)
  qed
  have merge_coins: "merge_transitions merged_vends merged_1_5 1 1 1 1 1 coinGeneral 2 coin100_100 3 generator modifier True = Some merged_1_5_coin"
    apply (simp add: merge_transitions_def easy_merge_1_5 modifier_def)
    apply (simp add: coinGeneral_def coin50_50_def)
    by (simp add: nondeterministic_simulates_def nondeterministic_simulates_trace_merged_1_5_coin_merged_vends_0_0)
  have arrives_5_merged_1_5_coin: "arrives 5 merged_1_5_coin = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_1_5_coin = {|(5, (1, 4), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_5_coin_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have arrives_6_merged_1_5_coin: "arrives 6 merged_1_5_coin = 6"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (6, (a, b), ba)) merged_1_5_coin = {|(6, (1, 6), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_1_5_coin_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have merge_states_4_6_merged_1_5_coin: "merge_states 4 6 merged_1_5_coin = merged_4_6"
    by (simp add: merge_states_def merge_states_aux_def merged_1_5_coin_def merged_4_6_def)
  have leaves_5_merged_vends: "leaves 5 merged_vends = 3"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_vends = {|(5, (3, 4), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_6_merged_vends: "leaves 6 merged_vends = 5"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (6, (a, b), ba)) merged_vends = {|(6, (5, 6), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_vends_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: leaves_def ffilter)
  qed
  have leaves_5_merged_4_6: "leaves 5 merged_4_6 = 1 \<and> arrives 5 merged_4_6 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (5, (a, b), ba)) merged_4_6 = {|(5, (1, 4), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_4_6_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: leaves_def arrives_def ffilter)
  qed
  have arrives_6_merged_4_6: "arrives 6 merged_4_6 = 4"
  proof-
    have ffilter: "ffilter (\<lambda>x. \<exists>a b ba. x = (6, (a, b), ba)) merged_4_6 = {|(6, (1, 4), vend_general)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse merged_4_6_def Set.filter_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      by (simp add: arrives_def ffilter)
  qed
  have easy_merge_vends: "easy_merge merged_vends merged_4_6 3 5 1 4 4 vend_general 5 vend_general 6 generator = Some final"
  proof-
    have ffilter: "ffilter (\<lambda>x. snd x \<noteq> ((1, 4), vend_general)) merged_4_6 = {|(0, (0, 1), selectGeneral_2), (2, (1, 1), coinGeneral)|}"
      apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def merged_4_6_def)
      apply safe
      by (simp_all add: vend_general_def)
    show ?thesis
      apply (simp add: easy_merge_def generator_def directly_subsumes_vend_general_self)
      apply (simp add: replace_transition_def ffilter final_def)
      by auto
  qed
  have merge_vends_2: "merge_transitions merged_vends merged_4_6 3 5 1 4 4 vend_general 5 vend_general 6 generator modifier True = Some final"
    by (simp add: merge_transitions_def easy_merge_vends)
  show ?thesis
    apply (simp add: merge_def merge_states_1_2 nondeterminism_def nondeterministic_pairs_merged_1_2)
    apply (simp add: arrives_2_merged_1_2 arrives_4_merged_1_2 merge_states_1_3 leaves_2_merged_vends)
    apply (simp add: leaves_2_merged_1_3 leaves_4_merged_vends arrives_4_merged_1_3 merge_vends)
    apply (simp add: nondeterminism_def nondeterministic_pairs_merged_1_3_coin)
    apply (simp add: arrives_2_merged_1_3_coin arrives_3_merged_1_3_coin merge_states_1_5)
    apply (simp add: leaves_2_merged_vends leaves_3_merged_vends leaves_2_merged_1_5 arrives_3_merged_1_5)
    apply (simp add: merge_coins nondeterminism_def nondeterministic_pairs_merged_1_5_coin)
    apply (simp add: arrives_5_merged_1_5_coin arrives_6_merged_1_5_coin merge_states_4_6_merged_1_5_coin)
    apply (simp add: leaves_5_merged_vends leaves_6_merged_vends leaves_5_merged_4_6 arrives_6_merged_4_6)
    by (simp add: merge_vends_2 nondeterminism_def nondeterministic_pairs_final)
qed

lemma score_final: "score final naive_score = {|(0, 0, 1), (0, 0, 4), (0, 1, 4)|}"
proof-
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (Inference.S final |\<times>| Inference.S final) = {|(0, 1), (0, 4), (1, 4)|}"
    apply (simp add: S_def final_def fprod_def ffilter_def fset_both_sides Abs_fset_inverse)
    apply (simp add: Set.filter_def)
    by auto
  show ?thesis
    apply (simp add: score_def ffilter)
    apply (simp add: outgoing_transitions_def final_def fimage_def)
    apply (simp add: naive_score_empty)
    by (simp add: naive_score_def selectGeneral_2_def coinGeneral_def vend_general_def fprod_def)
qed

lemma "learn traces naive_score generator modifier = (tm final)"
  apply (simp add: learn_def build_pta scoring_1 merge_1_8 merge_1_7)
  apply (simp add: scoring_2 merge_1_2)
  by (simp add: score_final sorted_list_of_fset_def)

end