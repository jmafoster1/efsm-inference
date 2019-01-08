theory Learn_EFSM_OLD
  imports Inference SelectionStrategies "../examples/Drinks_Machine"
begin

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

definition pta :: transition_matrix where
  "pta = {|((0, 1), selectCoke), ((1, 2), coin50_50), ((2, 3), coin50_100), ((3, 4), vend_coke),
                                 ((1, 5), coin100_100), ((5, 6), vend_coke),
           ((0, 7), selectPepsi), ((7, 8), coin50_50), ((8, 9), coin50_100), ((9, 10), vend_pepsi)|}"

definition traces :: log where
  "traces = [[(''select'', [Str ''coke''], []), (''coin'', [Num 50], [Num 50]), (''coin'', [Num 50], [Num 100]), (''vend'', [], [Str ''coke''])],
             [(''select'', [Str ''coke''], []), (''coin'', [Num 100], [Num 100]), (''vend'', [], [Str ''coke''])],
             [(''select'', [Str ''pepsi''], []), (''coin'', [Num 50], [Num 50]), (''coin'', [Num 50], [Num 100]), (''vend'', [], [Str ''pepsi''])]]"

declare One_nat_def [simp del]

lemmas pta_transitions = selectCoke_def coin50_50_def coin50_100_def vend_coke_def selectPepsi_def coin100_100_def vend_pepsi_def

lemma pta_of_log: "make_pta traces {||} = pta"
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
  show ?thesis
    apply (simp add: make_pta_def pta_def traces_def)
    apply (simp add: step_coin50 step_coin50_2 step_vend_coke
                      step_selectCoke_2 step_coin100 step_vend_coke_2
                      step_select_pepsi step_coin50_3 step_coin50_4 step_vend_pepsi)
    apply (simp add: select_coke coin50_50 coin100_100 coin50_100 selectPepsi vendCoke vendPepsi)
    by auto
qed

definition filtered_pairs :: "(nat \<times> nat) fset" where
  "filtered_pairs = {|(9, 10), (8, 10), (8, 9), (7, 10), (7, 9), (7, 8), (6, 10), (6, 9), (6, 8), (6, 7), (5, 10), (5, 9), (5, 8), (5, 7), (5, 6), (4, 10),
  (4, 9), (4, 8), (4, 7), (4, 6), (4, 5), (3, 10), (3, 9), (3, 8), (3, 7), (3, 6), (3, 5), (3, 4), (2, 10), (2, 9), (2, 8), (2, 7), (2, 6),
  (2, 5), (2, 4), (2, 3), (1, 10), (1, 9), (1, 8), (1, 7), (1, 6), (1, 5), (1, 4), (1, 3), (1, 2), (0, 10), (0, 9), (0, 8), (0, 7), (0, 6),
  (0, 5), (0, 4), (0, 3), (0, 2), (0, 1)|}"

lemma scoring: "sorted_list_of_fset (score pta naive_score) = [(0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 0, 6), (0, 0, 7), (0, 0, 8), (0, 0, 9), (0, 0, 10), (0, 1, 3), (0, 1, 4),
  (0, 1, 5), (0, 1, 6), (0, 1, 9), (0, 1, 10), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 2, 6), (0, 2, 9), (0, 2, 10), (0, 3, 4), (0, 3, 6),
  (0, 3, 7), (0, 3, 8), (0, 3, 10), (0, 4, 5), (0, 4, 6), (0, 4, 7), (0, 4, 8), (0, 4, 9), (0, 4, 10), (0, 5, 6), (0, 5, 7), (0, 5, 8),
  (0, 5, 10), (0, 6, 7), (0, 6, 8), (0, 6, 9), (0, 6, 10), (0, 7, 9), (0, 7, 10), (0, 8, 9), (0, 8, 10), (0, 9, 10), (1, 2, 7), (1, 2, 8),
  (1, 3, 5), (1, 3, 9), (1, 5, 9), (1, 7, 8), (2, 1, 2), (2, 1, 7), (2, 1, 8)]"
proof-
  have filter_pairs: "(Set.filter (\<lambda>(x, y). x < y) (fset (all_pairs (S pta)))) = fset filtered_pairs"
  proof-
    have aux1: "\<forall>x. x \<in> Set.filter (\<lambda>(x, y). x < y) (fset (all_pairs (S pta))) \<longrightarrow> x \<in> fset filtered_pairs"
      apply clarify
      apply (simp add: all_pairs_def S_def pta_def filtered_pairs_def)
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
      apply (case_tac "a=0")
       apply auto[1]
      by simp
    have aux2: "\<forall>x. x \<in> fset filtered_pairs \<longrightarrow> x \<in> Set.filter (\<lambda>(x, y). x < y) (fset (all_pairs (S pta)))"
      apply clarify
      apply (simp add: all_pairs_def S_def pta_def filtered_pairs_def)
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
      apply (case_tac "a=0")
       apply auto[1]
      by simp
    show ?thesis
      using aux1 aux2
      by blast
  qed
  have ffilter: "ffilter (\<lambda>(x, y). x < y) (all_pairs (S pta)) = filtered_pairs"
    apply (simp add: ffilter_def filter_pairs)
    apply (simp add: filtered_pairs_def)
    by (metis bot_fset.rep_eq finsert.rep_eq fset_inverse)
  have scoring: "score pta naive_score = {|(0, 9, 10), (0, 8, 10), (0, 8, 9), (0, 7, 10), (0, 7, 9), (1, 7, 8), (0, 6, 10), (0, 6, 9), (0, 6, 8), (0, 6, 7), (0, 5, 10),
      (1, 5, 9), (0, 5, 8), (0, 5, 7), (0, 5, 6), (0, 4, 10), (0, 4, 9), (0, 4, 8), (0, 4, 7), (0, 4, 6), (0, 4, 5), (0, 3, 10), (1, 3, 9),
      (0, 3, 8), (0, 3, 7), (0, 3, 6), (1, 3, 5), (0, 3, 4), (0, 2, 10), (0, 2, 9), (1, 2, 8), (1, 2, 7), (0, 2, 6), (0, 2, 5), (0, 2, 4),
      (0, 2, 3), (0, 1, 10), (0, 1, 9), (2, 1, 8), (2, 1, 7), (0, 1, 6), (0, 1, 5), (0, 1, 4), (0, 1, 3), (2, 1, 2), (0, 0, 10), (0, 0, 9),
      (0, 0, 8), (0, 0, 7), (0, 0, 6), (0, 0, 5), (0, 0, 4), (0, 0, 3), (0, 0, 2), (0, 0, 1)|}"
  proof-
    have outgoing_transitions_10: "outgoing_transitions 10 pta = {||}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 10) (fset pta) = {}"
        apply (simp add: Set.filter_def pta_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_9: "outgoing_transitions 9 pta = {|(10, vend_pepsi)|}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 9) (fset pta) = {((9, 10), vend_pepsi)}"
        apply (simp add: pta_def Set.filter_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_8: "outgoing_transitions 8 pta = {|(9, coin50_100)|}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 8) (fset pta) = {((8, 9), coin50_100)}"
        apply (simp add: pta_def Set.filter_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_7: "outgoing_transitions 7 pta = {|(8, coin50_50)|}"
         proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 7) (fset pta) = {((7, 8), coin50_50)}"
        apply (simp add: pta_def Set.filter_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_6: "outgoing_transitions 6 pta = {||}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 6) (fset pta) = {}"
        apply (simp add: Set.filter_def pta_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_5: "outgoing_transitions 5 pta = {|(6, vend_coke)|}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 5) (fset pta) = {((5, 6), vend_coke)}"
        apply (simp add: Set.filter_def pta_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_4: "outgoing_transitions 4 pta = {||}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 4) (fset pta) = {}"
        apply (simp add: Set.filter_def pta_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_3: "outgoing_transitions 3 pta = {|(4, vend_coke)|}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 3) (fset pta) = {((3, 4), vend_coke)}"
        apply (simp add: Set.filter_def pta_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_2: "outgoing_transitions 2 pta = {|(3, coin50_100)|}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 2) (fset pta) = {((2, 3), coin50_100)}"
        apply (simp add: Set.filter_def pta_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed
    have outgoing_transitions_1: "outgoing_transitions 1 pta = {|(2, coin50_50), (5, coin100_100)|}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin::nat, dest::nat), t). origin = 1) (fset pta) = {((1::nat, 2::nat), coin50_50), ((1, 5), coin100_100)}"
        apply (simp add: Set.filter_def pta_def)
        apply standard
         apply clarify
         apply auto[1]
        apply clarify
        by auto
      have abs_fset: "Abs_fset {((1, 2), coin50_50), ((1, 5), coin100_100)} = {|((1, 2), coin50_50), ((1, 5), coin100_100)|}"
        by (metis fset_inverse fset_simps(1) fset_simps(2))
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter abs_fset)
    qed
    have outgoing_transitions_0: "outgoing_transitions 0 pta = {|(1, selectCoke), (7, selectPepsi)|}"
    proof-
      have set_filter: "Set.filter (\<lambda>((origin, dest), t). origin = 0) (fset pta) = {((0, 1), selectCoke), ((0, 7), selectPepsi)}"
        apply (simp add: Set.filter_def pta_def)
        apply safe
        by (simp_all add: pta_transitions)
      show ?thesis
        by (simp add: outgoing_transitions_def ffilter_def set_filter)
    qed

    have naive_score_8_9: "naive_score {|coin50_100|} {|vend_pepsi|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_7_9: "naive_score {|coin50_50|} {|vend_pepsi|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_7_8: "naive_score {|coin50_50|} {|coin50_100|} = 1"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_5_9: "naive_score {|vend_coke|} {|vend_pepsi|} = 1"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_5_8: "naive_score {|vend_coke|} {|coin50_100|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_5_7: "naive_score {|vend_coke|} {|coin50_50|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_3_5: "naive_score {|vend_coke|} {|vend_coke|} = 1"
      by (simp add: naive_score_def fprod_def)
    have naive_score_2_8: "naive_score {|coin50_100|} {|coin50_100|} = 1"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_2_7: "naive_score {|coin50_100|} {|coin50_50|} = 1"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_2_5: "naive_score {|coin50_100|} {|vend_coke|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_1_9: "naive_score {|coin50_50, coin100_100|} {|vend_pepsi|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_1_8: "naive_score {|coin50_50, coin100_100|} {|coin50_100|} = 2"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_1_7: "naive_score {|coin50_50, coin100_100|} {|coin50_50|} = 2"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_1_5: "naive_score {|coin50_50, coin100_100|} {|vend_coke|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_0_9: "naive_score {|selectCoke, selectPepsi|} {|vend_pepsi|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_0_8: "naive_score {|selectCoke, selectPepsi|} {|coin50_100|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_0_7: "naive_score {|selectCoke, selectPepsi|} {|coin50_50|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_0_5: "naive_score {|selectCoke, selectPepsi|} {|vend_coke|} = 0"
      by (simp add: naive_score_def pta_transitions fprod_def)
    have naive_score_0_1: "naive_score {|selectCoke, selectPepsi|} {|coin50_50, coin100_100|} = 0"
    proof-
      have abs_fset: "Abs_fset
       {(selectCoke, coin50_50), (selectCoke, coin100_100), (selectPepsi, coin100_100), (selectPepsi, coin50_50),
        (selectPepsi, coin100_100)} = {|(selectCoke, coin50_50), (selectCoke, coin100_100), (selectPepsi, coin100_100), (selectPepsi, coin50_50),
        (selectPepsi, coin100_100)|}"
        by (metis fset_inverse fset_simps(1) fset_simps(2))
      show ?thesis
        apply (simp add: naive_score_def fprod_def abs_fset)
        by (simp add: pta_transitions)
    qed
    show ?thesis
      apply (simp add: score_def ffilter filtered_pairs_def)
      apply (simp only: outgoing_transitions_0 outgoing_transitions_1 outgoing_transitions_2 outgoing_transitions_3 outgoing_transitions_4 outgoing_transitions_5 outgoing_transitions_6 outgoing_transitions_7 outgoing_transitions_8 outgoing_transitions_9 outgoing_transitions_10)
      apply (simp add: fimage_def)
      by (simp only: naive_score_empty naive_score_empty_2 naive_score_8_9 naive_score_7_9 naive_score_7_8
                        naive_score_5_9 naive_score_5_8 naive_score_5_7 naive_score_3_5 naive_score_2_8 naive_score_2_7 naive_score_2_5
                        naive_score_1_9 naive_score_1_8 naive_score_1_7 naive_score_1_5
                        naive_score_0_9 naive_score_0_8 naive_score_0_7 naive_score_0_5 naive_score_0_1)
  qed
  show ?thesis
    by (simp add: ffilter scoring sorted_list_of_fset_def)
qed

definition merged_1_7 :: transition_matrix where
  "merged_1_7 = {|((0, 1), selectCoke), ((1, 2), coin50_50), ((2, 3), coin50_100), ((3, 4), vend_coke),
                                                             ((1, 5), coin100_100), ((5, 6), vend_coke),
                  ((0, 1), selectPepsi), ((1, 8), coin50_50), ((8, 9), coin50_100), ((9, 10), vend_pepsi)|}"

lemma merge_states_1_7: "merge_states 1 7 pta = merged_1_7"
  by (simp add: merge_states_def merge_states_aux_def pta_def merged_1_7_def)

lemma no_choice_coin50_50_coin_100_100: "\<not>choice coin50_50 coin100_100"
  by (simp add: choice_def pta_transitions)

lemma no_choice_coin_100_100_coin_50_50: "\<not>choice coin100_100 coin50_50"
  using choice_symmetry no_choice_coin50_50_coin_100_100 by blast

lemma choice_coin50_50_coin50_50: "choice coin50_50 coin50_50"
  apply (simp add: choice_def pta_transitions)
  by auto

lemma no_choice_selectPepsi_selectCoke: "\<not>choice selectPepsi selectCoke"
  by (simp add: choice_def pta_transitions)

lemma no_choice_selectCoke_selectPepsi: "\<not>choice selectCoke selectPepsi"
  by (simp add: choice_def pta_transitions)

lemma choice_coin50_100_coin50_100: "choice coin50_100 coin50_100"
  apply (simp add: choice_def pta_transitions)
  by auto

lemma choice_vend_coke_vend_pepsi: "choice vend_coke vend_pepsi"
  by (simp add: choice_def pta_transitions)

lemmas choices = choice_vend_coke_vend_pepsi choice_symmetry choice_coin50_100_coin50_100 no_choice_selectCoke_selectPepsi no_choice_selectPepsi_selectCoke choice_coin50_50_coin50_50 no_choice_coin50_50_coin_100_100 no_choice_coin_100_100_coin_50_50

lemma nondeterministic_pairs_merged_1_7: "nondeterministic_pairs merged_1_7 = {|(1, (2, 8), coin50_50, coin50_50)|}"
proof-
  have card1: "card {(1, selectCoke), (1, selectPepsi)} = 2"
    by (simp add: pta_transitions)
  have minus_1: "{(2, coin50_50), (5, coin100_100), (8, coin50_50)} - {(5, coin100_100)} = {(2, coin50_50), (8, coin50_50)}"
    apply (simp add: pta_transitions)
    by auto
  have minus_2: "{(2::nat, coin50_50), (5, coin100_100), (8, coin50_50)} - {(8, coin50_50)} = {(2, coin50_50), (5,coin100_100)}"
    apply (simp add: pta_transitions)
    by auto
  have set_filter_1: "Set.filter (\<lambda>(uu, uu, t, t'). t \<le> t' \<and> choice t t')
       {(1, (2, 5), coin50_50, coin100_100), (1, (2, 8), coin50_50, coin50_50), (1, (8, 2), coin50_50, coin50_50),
        (1, (8, 5), coin50_50, coin100_100), (1, (5, 2), coin100_100, coin50_50), (1, (5, 8), coin100_100, coin50_50)} =
       {(1, (2, 8), coin50_50, coin50_50), (1, (8, 2), coin50_50, coin50_50)}"
    apply (simp add: Set.filter_def)
    apply safe
    by (simp_all add: choices)

  have minus_3: "{(1::nat, selectPepsi)} - {(1::nat, selectCoke)} = {(1::nat, selectPepsi)}"
    by (simp add: pta_transitions)
  have minus_4: "{(1::nat, selectCoke), (1, selectPepsi)} - {(1::nat, selectPepsi)} = {(1::nat, selectCoke)}"
    apply (simp add: pta_transitions)
    by auto
  have set_filter_2: "Set.filter (\<lambda>(uu, u, t, t'). t \<le> t' \<and> choice t t')
                   {(0, (1, 1), selectPepsi, selectCoke), (0, (1, 1), selectCoke, selectPepsi)} = {}"
    apply (simp add: Set.filter_def)
    apply safe
    by (simp_all add: choices)

  have state_nondeterminism_1:  "state_nondeterminism 1 {|(2, coin50_50), (5, coin100_100), (8, coin50_50)|} = {|
   (1, (5, 8), coin100_100, coin50_50),
   (1, (2, 8), coin50_50, coin50_50),
   (1, (2, 5), coin50_50, coin100_100)|}"
    apply (simp add: state_nondeterminism_def ffilter_def card1 fimage_def)
    apply (simp add: minus_1 minus_2)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    by auto
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke), (1, selectPepsi)|} = {|(0, (1, 1), selectPepsi, selectCoke), (0, (1, 1), selectCoke, selectPepsi)|}"
    apply (simp add: state_nondeterminism_def ffilter_def card1 fimage_def)
    by (simp add: minus_3 minus_4)

  show ?thesis
    apply (simp add: nondeterministic_pairs_def)
    apply (simp add: S_def merged_1_7_def)
    apply (simp add: outgoing_transitions_def Set.filter_def fimage_def)
    apply (simp add: state_nondeterminism_1 state_nondeterminism_0)
    apply (simp add: ffilter_def Set.filter_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    apply safe
    by (simp_all add: choices)
qed

lemma nondeterminism_merged_1_7: "nondeterminism merged_1_7"
  by (simp add: nondeterminism_def nondeterministic_pairs_merged_1_7)

definition merged_2_8 :: transition_matrix where
  "merged_2_8 = {|((0, 1), selectCoke), ((1, 2), coin50_50), ((2, 3), coin50_100), ((3, 4), vend_coke),
                  ((1, 5), coin100_100), ((5, 6), vend_coke), ((0, 1), selectPepsi), ((1, 2), coin50_50),
                  ((2, 9), coin50_100), ((9, 10), vend_pepsi)|}"

lemma merge_states_2_8: "merge_states 2 8 merged_1_7 = merged_2_8"
  by (simp add: merge_states_def merge_states_aux_def merged_1_7_def merged_2_8_def)

lemma nondeterministic_pairs_merged_2_8: "nondeterministic_pairs merged_2_8 = {|(2, (3, 9), coin50_100, coin50_100)|}"
proof-
  have card1: "card {(1, selectCoke), (1, selectPepsi)} = 2"
    by (simp add: pta_transitions)
  have card2_aux: "{(2, coin50_50), (5, coin100_100), (2, coin50_50)} = {(5, coin100_100), (2, coin50_50)}"
    by auto

  have minus_1: "{(5::nat, coin100_100), (2, coin50_50)} - {(2, coin50_50)} = {(5, coin100_100)}"
    by auto
  have minus_2: "{(3::nat, coin50_100), (9, coin50_100)} - {(9, coin50_100)} = {(3, coin50_100)}"
    by auto
  have minus_3: "{(1::nat, selectPepsi)} - {(1, selectCoke)} = {(1, selectPepsi)}"
    by (simp add: pta_transitions)
  have minus_4: "{(1, selectCoke), (1, selectPepsi)} - {(1, selectPepsi)} = {(1, selectCoke)}"
    apply (simp add: pta_transitions)
    by auto
  have state_nondeterminism_1: "state_nondeterminism 1 {|(2, coin50_50), (5, coin100_100), (2, coin50_50)|} = {|(1, (2, 5), coin50_50, coin100_100), (1, (2, 5), coin50_50, coin100_100)|}"
    apply (simp add: state_nondeterminism_def card1 Set.filter_def fimage_def)
    apply (simp add: minus_1 minus_2 minus_3 minus_4)
    by (simp add: fset_both_sides Abs_fset_inverse card2_aux)
  have state_nondeterminism_2: "state_nondeterminism 2 {|(3, coin50_100), (9, coin50_100)|} = {|(2, (3, 9), coin50_100, coin50_100)|}"
    apply (simp add: state_nondeterminism_def card1 Set.filter_def fimage_def)
    by (simp add: minus_1 minus_2 minus_3 minus_4)
  have state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke), (1, selectPepsi)|} = {|(0, (1, 1), selectPepsi, selectCoke), (0, (1, 1), selectCoke, selectPepsi)|}"
    apply (simp add: state_nondeterminism_def card1 Set.filter_def fimage_def)
    by (simp add: minus_1 minus_2 minus_3 minus_4)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def)
    apply (simp add: S_def merged_2_8_def)
    apply (simp add: outgoing_transitions_def Set.filter_def fimage_def)
    apply (simp add: state_nondeterminism_1 state_nondeterminism_2 state_nondeterminism_0)
    apply (simp add: ffilter_def Set.filter_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    apply safe
    by (simp_all add: choices)
qed

lemma nondeterminism_merged_2_8: "nondeterminism merged_2_8"
  by (simp add: nondeterminism_def nondeterministic_pairs_merged_2_8)

definition merged_3_9 :: transition_matrix where
 "merged_3_9 = {|
((0, 1), selectCoke), ((1, 2), coin50_50), ((2, 3), coin50_100), ((3, 4), vend_coke), 
                                           ((1, 5), coin100_100), ((5, 6), vend_coke),
((0, 1), selectPepsi), ((1, 2), coin50_50), ((3, 10), vend_pepsi)|}"

lemma merge_states_3_9: "merge_states 3 9 merged_2_8 = merged_3_9"
  apply (simp add: merge_states_def merge_states_aux_def merged_2_8_def merged_3_9_def)
  by auto

lemma card1: "card {(1, selectCoke), (1, selectPepsi)} = 2"
    by (simp add: pta_transitions)

lemma minus_3: "{(1::nat, selectPepsi)} - {(1, selectCoke)} = {(1, selectPepsi)}"
  by (simp add: pta_transitions)

lemma minus_4: "{(1, selectCoke), (1, selectPepsi)} - {(1, selectPepsi)} = {(1, selectCoke)}"
    apply (simp add: pta_transitions)
  by auto

lemma minus_1: "{(5::nat, coin100_100), (2, coin50_50)} - {(2, coin50_50)} = {(5, coin100_100)}"
  by auto

lemma minus_2: "{(4::nat, vend_coke), (10, vend_pepsi)} - {(10, vend_pepsi)} = {(4, vend_coke)}"
  by auto

lemma card2_aux: "{(2, coin50_50), (5, coin100_100), (2, coin50_50)} = {(5, coin100_100), (2, coin50_50)}"
  by auto

lemma state_nondeterminism_1:  "state_nondeterminism 1 {|(2, coin50_50), (5, coin100_100), (2, coin50_50)|} = {|
   (1, (2, 5), coin50_50, coin100_100), (1, (2, 5), coin50_50, coin100_100)|}"
    apply (simp add: state_nondeterminism_def Set.filter_def fimage_def card1 card2_aux)
    by (simp add: minus_1)

lemma state_nondeterminism_0: "state_nondeterminism 0 {|(1, selectCoke), (1, selectPepsi)|} = {|(0, (1, 1), selectPepsi, selectCoke), (0, (1, 1), selectCoke, selectPepsi)|}"
  apply (simp add: state_nondeterminism_def card1 Set.filter_def fimage_def)
  by (simp add: minus_3 minus_4)

lemma nondeterministic_pairs_merged_3_9: "nondeterministic_pairs merged_3_9 = {|(3, (4, 10), vend_coke, vend_pepsi)|}"
proof-
  have state_nondeterminism_3: "state_nondeterminism 3 {|(4, vend_coke), (10, vend_pepsi)|} = {|(3, (4, 10), vend_coke, vend_pepsi)|}"
    apply (simp add: state_nondeterminism_def card1 Set.filter_def fimage_def)
    by (simp add: minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def)
    apply (simp add: S_def merged_3_9_def)
    apply (simp add: outgoing_transitions_def Set.filter_def fimage_def)
    apply (simp add: state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_3)
    apply (simp add: ffilter_def Set.filter_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    apply safe
                        apply (simp_all add: choices)
    by (simp add: pta_transitions less_eq_transition_ext_def less_transition_ext_def less_aexp_def)
qed

lemma nondeterminism_merged_3_9: "nondeterminism merged_3_9"
  by (simp add: nondeterminism_def nondeterministic_pairs_merged_3_9)

definition merged_4_10 :: transition_matrix where
  "merged_4_10 = {|
((0, 1), selectCoke), ((1, 2), coin50_50), ((2, 3), coin50_100), ((3, 4), vend_coke), 
                                           ((1, 5), coin100_100), ((5, 6), vend_coke),
((0, 1), selectPepsi), ((1, 2), coin50_50), ((3, 4), vend_pepsi)|}"

lemma merge_states_4_10: "merge_states 4 10 merged_3_9 = merged_4_10"
  by (simp add: merge_states_def merge_states_aux_def merged_4_10_def merged_3_9_def)

lemma nondeterministic_pairs_merged_4_10: "nondeterministic_pairs merged_4_10 = {|(3, (4, 4), vend_coke, vend_pepsi)|}"
proof-
  have minus: "{(4::nat, vend_pepsi)} - {(4, vend_coke)} = {(4, vend_pepsi)}"
    by (simp add: pta_transitions)
  have card: "card {(4, vend_coke), (4, vend_pepsi)} = 2"
    by (simp add: pta_transitions)
  have minus_2: "{(4::nat, vend_coke), (4, vend_pepsi)} - {(4::nat, vend_pepsi)} = {(4::nat, vend_coke)}"
    apply (simp add: pta_transitions)
    by auto
  have state_nondeterminism_4: "state_nondeterminism 3 {|(4, vend_coke), (4, vend_pepsi)|} = {|(3, (4, 4), vend_pepsi, vend_coke), (3, (4, 4), vend_coke, vend_pepsi)|}"
    apply (simp add: state_nondeterminism_def Set.filter_def fimage_def card1 card2_aux)
    by (simp add: minus card minus_2)
  show ?thesis
    apply (simp add: nondeterministic_pairs_def)
    apply (simp add: S_def merged_4_10_def)
    apply (simp add: outgoing_transitions_def Set.filter_def fimage_def)
    apply (simp add: state_nondeterminism_0 state_nondeterminism_1 state_nondeterminism_4)
    apply (simp add: ffilter_def Set.filter_def)
    apply (simp add: fset_both_sides Abs_fset_inverse)
    apply safe
                        apply (simp_all add: choices)
    by (simp_all add: pta_transitions less_eq_transition_ext_def less_transition_ext_def less_aexp_def)
qed

lemma nondeterminism_merged_4_10: "nondeterminism merged_4_10"
  by (simp add: nondeterminism_def nondeterministic_pairs_merged_4_10)

definition vend_general :: transition where
  "vend_general = \<lparr>Label = ''vend'', Arity = 0, Guard = [], Outputs = [V (R 1)], Updates = []\<rparr>"

definition selectGeneral :: transition where
  "selectGeneral = \<lparr>Label = ''select'', Arity = 1, Guard = [], Outputs = [], Updates = [(R 1, (V (I 1)))]\<rparr>"

definition merged_vends :: transition_matrix where
  "merged_vends = {|
((0, 1), selectGeneral), ((1, 2), coin50_50), ((2, 3), coin50_100), ((3, 4), vend_general), 
                         ((1, 5), coin100_100), ((5, 6), vend_coke)|}"

definition mapping :: "nat \<Rightarrow> nat" where
  "mapping n = (if n = 7 then 1 else if n = 8 then 2 else if n = 9 then 3 else if n = 10 then 4 else n)"

definition modify :: update_modifier where
  "modify t1 t2 newFrom newEFSM oldEFSM = (if newEFSM = merged_4_10 then Some (merged_vends, (\<lambda>n. n), mapping) else None)"

lemma first_step: "inference_step pta
             [(2, 1, 7), (2, 1, 2), (1, 7, 8), (1, 5, 9), (1, 3, 9), (1, 3, 5), (1, 2, 8), (1, 2, 7), (0, 9, 10), (0, 8, 10), (0, 8, 9),
              (0, 7, 10), (0, 7, 9), (0, 6, 10), (0, 6, 9), (0, 6, 8), (0, 6, 7), (0, 5, 10), (0, 5, 8), (0, 5, 7), (0, 5, 6), (0, 4, 10),
              (0, 4, 9), (0, 4, 8), (0, 4, 7), (0, 4, 6), (0, 4, 5), (0, 3, 10), (0, 3, 8), (0, 3, 7), (0, 3, 6), (0, 3, 4), (0, 2, 10),
              (0, 2, 9), (0, 2, 6), (0, 2, 5), (0, 2, 4), (0, 2, 3), (0, 1, 10), (0, 1, 9), (0, 1, 6), (0, 1, 5), (0, 1, 4), (0, 1, 3),
              (0, 0, 10), (0, 0, 9), (0, 0, 8), (0, 0, 7), (0, 0, 6), (0, 0, 5), (0, 0, 4), (0, 0, 3), (0, 0, 2), (0, 0, 1)]
             (\<lambda>a b c d e. Some t) modify = Some drinks"
proof-
  have exits_state_pta_coin50_50_1: "exits_state pta coin50_50 1"
    by (simp add: exits_state_def pta_def pta_transitions)
  have exits_state_merged_1_7_coin50_100_2: "exits_state merged_1_7 coin50_100 2"
    by (simp add: exits_state_def pta_transitions merged_1_7_def)
  have exits_state_merged_2_8_vend_coke_3: "exits_state merged_2_8 vend_coke 3"
    by (simp add: exits_state_def pta_transitions merged_2_8_def)
  have not_exits_state_merged_2_8_vend_pepsi_3: "\<not>exits_state merged_2_8 vend_pepsi 3"
    by (simp add: exits_state_def pta_transitions merged_2_8_def)
  have not_exits_state_merged_3_9_vend_coke_4: "\<not>exits_state merged_3_9 vend_coke 4"
    by (simp add: exits_state_def pta_transitions merged_3_9_def)
  have not_exits_state_merged_3_9_vend_pepsi_4: "\<not>exits_state merged_3_9 vend_pepsi 4"
    by (simp add: exits_state_def pta_transitions merged_3_9_def)

  show ?thesis
    apply simp
    apply (simp add: merge_states_1_7)
    apply (simp add: nondeterministic_pairs_merged_1_7 nondeterminism_merged_1_7 max_def exits_state_pta_coin50_50_1)
    apply (simp add: merge_states_2_8)
    apply (simp add: exits_state_merged_1_7_coin50_100_2 nondeterministic_pairs_merged_2_8 nondeterminism_merged_2_8)
    apply (simp add: merge_states_3_9)
    apply (simp add: nondeterministic_pairs_merged_3_9 nondeterminism_merged_3_9 exits_state_merged_2_8_vend_coke_3 not_exits_state_merged_2_8_vend_pepsi_3)
    apply (simp add: merge_states_4_10)
    apply (simp add: nondeterministic_pairs_merged_4_10 not_exits_state_merged_3_9_vend_coke_4 not_exits_state_merged_3_9_vend_pepsi_4 nondeterminism_merged_4_10)



lemma "learn traces naive_score (\<lambda>a b c d e. Some t) (\<lambda>a b c d e. Some e') = drinks"
  apply (simp add: learn_def pta_of_log scoring)
  sorry

end