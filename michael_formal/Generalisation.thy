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

(* vend_g has one register so this should be derestricted and the rest set to false *)
abbreviation vend_g_start :: constraints where
  "vend_g_start \<equiv> (\<lambda>x. if x = (V ''r1'') then Bc True else empty x)"

lemma "subsumes vend_g_start empty"
  by (simp add: subsumes_def)

lemma "(subsumes (constraints_apply_guards r1_r2_true (Guard coin_init)) (constraints_apply_guards r1_r2_true (Guard coin50)))"
  apply (simp add: coin50_def coin_init_def subsumes_def)
  using consistent_empty_1 by force

lemma "posterior r1_r2_true coin_init = vend_g_start"
  apply (rule ext)
  apply (simp add: coin_init_def posterior_def consistent_def)
  using consistent_empty_1 by force

lemma "is_generalisation vend_g_start coin_init r1_r2_true coin50"
  apply (simp add: coin50_def coin_init_def posterior_def is_generalisation_def subsumes_def consistent_def)
  using consistent_empty_1 by fastforce

lemma "is_generalisation vend_g_start coin_inc r1_r2_true coin50"
  by (simp add: posterior_def coin_init_def coin_inc_def coin50_def)

lemma "(posterior_sequence [coin_init, coin_inc] vend_g_start) = vend_g_start"
  by (simp add: coin_init_def coin_inc_def posterior_def)

lemma "is_generalisation vend_g_start vends_g r1_r2_true vends"
  by (simp add: coin_init_def coin_inc_def posterior_def vends_def vends_g_def)



definition test1 :: transition where
"test1 \<equiv> \<lparr>
        Label = ''foo'',
        Arity = 1,
        Guard = [(gexp.Eq ''i1'' (N 6))],
        Outputs =  [(N 6)],
        Updates = [(''r1'', (V ''i1''))]
      \<rparr>"

definition test2 :: transition where
"test2 \<equiv> \<lparr>
        Label = ''foo'',
        Arity = 1,
        Guard = [(gexp.Gt ''i1'' (N 0))],
        Outputs =  [(V ''i1'')],
        Updates = [(''r1'', (V ''i1''))]
      \<rparr>"

lemma "is_generalisation vend_g_start test2 vend_g_start test1"
  apply (simp add: test2_def posterior_def)
  by (simp add: test1_def join_def)
end