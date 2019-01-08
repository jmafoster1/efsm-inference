theory Learn_EFSM_Transitions
imports Inference SelectionStrategies
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
    apply(simp add: sorted_list_of_fset pta_def)
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

lemma no_choice_coin50_50_coin100_100: "\<not>choice coin50_50 coin100_100"
  by (simp add: choice_def transitions)

lemma no_choice_coin100_100_coin50_50: "\<not>choice coin100_100 coin50_50"
  by (simp add: choice_def transitions)

lemma no_choice_coin100_100_coin50_100: "\<not>choice coin100_100 coin50_100"
  by (simp add: choice_def transitions)

lemma no_choice_selectCoke_selectPepsi: "\<not>choice selectCoke selectPepsi"
  by (simp add: choice_def transitions)

lemma choice_coin50_100_coin50_50: "choice coin50_100 coin50_50"
  apply (simp add: choice_def transitions)
  by auto

lemmas choices = choice_coin50_100_coin50_50 no_choice_selectCoke_selectPepsi no_choice_coin100_100_coin50_100 no_choice_coin100_100_coin50_50 no_choice_coin50_50_coin100_100 choice_symmetry

lemma coin50_50_lt_coin50_100: "coin50_50 < coin50_100"
  by (simp add: transitions less_transition_ext_def less_aexp_def)

lemmas orders = coin50_50_lt_coin50_100

end