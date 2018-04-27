theory Generalisation
imports Constraints drinks_machine
begin
definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [(gexp.Eq ''i1'' (N 1))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq ''i1'' (N 50))],
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
        Guard = [(Ge ''r1'' (N 100))],
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
        Guard = [(gexp.Lt ''r1'' (N 100))],
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
  "vend_g_start \<equiv> (\<lambda>x. if x = ''r1'' then Bc True else no_regs x)"

lemma "subsumes vend_g_start no_regs"
  by simp

lemma "(subsumes (Constraints.apply_guards vend_start (Guard coin_init)) (Constraints.apply_guards vend_start (Guard coin50)))"
  by (simp add: coin50_def coin_init_def)

lemma "(posterior vend_start coin50) =  no_regs"
  apply (rule ext)
  by (simp add: coin50_def posterior_def)

lemma "posterior vend_start coin_init = vend_g_start"
  apply (rule ext)
  by (simp add: coin_init_def posterior_def)

lemma "is_generalisation vend_g_start coin_init no_regs coin50"
  by (simp add: coin50_def coin_init_def posterior_def)

lemma "is_generalisation vend_g_start coin_inc no_regs coin50"
  by (simp add: posterior_def coin_init_def coin_inc_def coin50_def)

lemma "(posterior_sequence [coin_init, coin_inc] vend_g_start) = vend_g_start"
  by (simp add: coin_init_def coin_inc_def posterior_def)

lemma "is_generalisation vend_g_start vends_g  no_regs vends"
  by (simp add: coin_init_def coin_inc_def posterior_def vends_def vends_g_def)
end