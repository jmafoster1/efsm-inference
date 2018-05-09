theory Generalisation
imports Constraints drinks_machine2
begin
definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [(gexp.Eq (V ''i1'') (N 1))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq (V ''i1'') (N 50))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition coin_init :: "transition" where
"coin_init \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(''r1'', (V ''i1''))]
      \<rparr>"

definition coin_inc :: "transition" where
"coin_inc \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [(''r1'', (Plus (V ''r1'') (V ''i1'')))]
      \<rparr>"

definition vends :: "transition" where
"vends \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [],
        Outputs =  [(N 1)],
        Updates = []
      \<rparr>"

definition vends_g :: "transition" where
"vends_g \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V ''r1'') (N 100))],
        Outputs =  [(N 1)],
        Updates = []
      \<rparr>"

definition venderr :: "transition" where
"venderr \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [],
        Outputs =  [],
        Updates = []
      \<rparr>"

definition venderr_g :: "transition" where
"venderr_g \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(gexp.Lt (V ''r1'') (N 100))],
        Outputs =  [(N 1)],
        Updates = []
      \<rparr>"

definition vend :: "efsm" where
"vend \<equiv> \<lparr> 
          S = [1,2,3,4,5],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [select] 
              else if (a,b) = (2,3) then [coin50]
              else if (a,b) = (3,3) then [venderr]
              else if (a,b) = (3,4) then [coin50]
              else if (a,b) = (4,5) then [vends]
              else [] (* There are no other transitions *)
         \<rparr>"

definition vend_g :: "efsm" where
"vend_g \<equiv> \<lparr> 
          S = [1,2,3,4],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [select] 
              else if (a,b) = (2,3) then [coin_init]
              else if (a,b) = (3,3) then [venderr_g, coin_inc]
              else if (a,b) = (3,4) then [vends_g]
              else [] (* There are no other transitions *)
         \<rparr>"

lemma "(subsumes (constraints_apply_guards r1_r2_true (Guard coin_init)) (constraints_apply_guards r1_r2_true (Guard coin50)))"
  by (simp add: coin50_def coin_init_def subsumes_def)

lemma "posterior r1_r2_true coin_init = r1_true"
  apply (rule ext)
  apply (simp add: coin_init_def posterior_def consistent_def)
  using consistent_empty_1 by force

lemma "is_generalisation empty coin_init r1_r2_true coin50"
  apply (simp add: coin50_def coin_init_def posterior_def is_generalisation_def subsumes_def consistent_def)
  using consistent_empty_1 by fastforce

lemma "is_generalisation empty coin_inc r1_r2_true coin50"
  apply (simp add: is_generalisation_def subsumes_def coin50_def coin_inc_def posterior_def)
  apply (simp add: consistent_def satisfiable_def valid_def)
  using consistent_empty_1 by fastforce

lemma "(posterior_sequence [coin_init, coin_inc] empty) = r1_true"
  apply (simp add: posterior_sequence_def posterior_def coin_init_def coin_inc_def satisfiable_def valid_def consistent_def)
  by (metis (no_types, lifting) consistent_empty_1 posterior_r1_r2_true_t2 valid_constraints_def valid_t2_empty)

lemma "is_generalisation empty vends_g empty vends"
  apply (simp add: is_generalisation_def)
  apply safe
    apply (simp add: subsumes_def vends_def vends_g_def)
   apply (simp add: vends_def vends_g_def)
  apply (simp add: posterior_def vends_def vends_g_def consistent_def subsumes_def)
  using consistent_def consistent_empty by auto

definition test1 :: transition where
"test1 \<equiv> \<lparr>
        Label = ''foo'',
        Arity = 1,
        Guard = [(gexp.Eq (V ''i1'') (N 6))],
        Outputs =  [(N 6)],
        Updates = [(''r1'', (V ''i1''))]
      \<rparr>"

definition test2 :: transition where
"test2 \<equiv> \<lparr>
        Label = ''foo'',
        Arity = 1,
        Guard = [(gexp.Gt (V ''i1'') (N 0))],
        Outputs =  [(V ''i1'')],
        Updates = [(''r1'', (V ''i1''))]
      \<rparr>"

lemma false_not_equal: "(\<lambda>i. cexp.Bc False) \<noteq> (\<lambda>x. if x = V ''r1'' then cexp.Eq 6 else Constraints.empty x)"
  by (metis cexp.distinct(13))

lemma posterior_test1: "(posterior empty test1) = (\<lambda>x. if x = V ''r1'' then Eq 6 else empty x)"
  apply (simp add: posterior_def test1_def consistent_def)
  apply (simp add: false_not_equal)
  apply (rule_tac x="<''i1'' := 6>" in exI)
  apply (simp add: null_state_def)
  by (metis (no_types, lifting) and.simps(10) and.simps(16) consistent_empty_1 posterior_r1_r2_true_t2 valid_constraints_def valid_t2_empty)

lemma apply_guards_test1: "(constraints_apply_guards empty (Guard test1)) = (\<lambda>x. if x = V ''i1'' then Eq 6 else empty x)"
  apply (simp add: test1_def)
  apply (rule ext)
  apply (case_tac "r = V ''i1''")
   apply simp
  apply simp
  by (metis and.simps(10) and.simps(16) consistent_empty_1)

lemma "is_generalisation empty test2 empty test1"
  apply (simp add: is_generalisation_def)
  apply safe
    apply (simp add: subsumes_def test1_def test2_def)
   apply (simp add: test1_def test2_def)
  apply (simp add: posterior_test1 apply_guards_test1)
  by (simp add: subsumes_def posterior_def consistent_def test2_def)
end