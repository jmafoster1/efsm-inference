theory Generalisation
imports Contexts drinks_machine2
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

lemma "posterior r1_r2_true coin_init = r1_true"
  apply (rule ext)
  apply (simp add: coin_init_def posterior_def consistent_def)
  using consistent_empty_1 by force

lemma posterior_empty_coin_inc_not_consistent: "\<not> consistent (posterior empty coin_inc)"
  apply (simp add: posterior_def coin_inc_def valid_def satisfiable_def)
  apply (simp add: consistent_def)
  apply (rule allI)
  apply (rule_tac x="V ''r1''" in exI)
  by simp

lemma posterior_empty_coin_inc: "(posterior empty coin_inc) = (\<lambda>r. if r = V ''r1'' then cexp.Bc False else Contexts.empty r)"
  by (simp add: posterior_def coin_inc_def satisfiable_def)

lemma foo: "\<not> (\<forall>s. \<exists>r. (r = V ''i1'' \<longrightarrow> s ''i1'' \<noteq> 50) \<and>
             (r \<noteq> V ''i1'' \<longrightarrow> and (Contexts.empty r) (cexp.Bc True) \<noteq> Undef \<and> \<not> gval (cexp2gexp r (and (Contexts.empty r) (cexp.Bc True))) s))"
  apply simp
  apply (rule_tac x="<''i1'' := 50>" in exI, simp)
  by (metis (no_types, lifting) consistent_empty_1 posterior_r1_r2_true_t2 valid_context_def valid_t2_empty)

lemma empty_neq_false: "(\<lambda>i. cexp.Bc False) \<noteq> Contexts.empty"
  by (metis empty_never_false)

lemma posterior_empty_coin50: "(posterior empty coin50) = empty"
  apply (simp add: posterior_def coin50_def satisfiable_def consistent_def empty_neq_false)
  apply (rule_tac x="<''i1'' := 50>" in exI, simp)
  using empty_not_undef by force

lemma "subsumes empty coin_init coin50"
  apply (simp add: subsumes_def coin_init_def coin50_def posterior_def)
  by (simp add: consistent_def)

lemma "(posterior empty coin_inc) (V ''r1'') = Bc False"
  by (simp add: posterior_def coin_inc_def valid_def satisfiable_def)

lemma "\<not> subsumes empty coin_inc coin50"
  apply (simp add: subsumes_def coin_inc_def coin50_def posterior_def valid_def satisfiable_def)
  apply (simp add: consistent_def)
  apply safe
  using consistent_def consistent_empty_1 consistent_empty_3 apply auto[1]
   apply auto[1]
  apply (rule_tac x="<''i1'' := 50>" in exI, simp)
  by (metis cexp2gexp.simps(1) consistent_empty_1 gval.simps(1))

lemma "subsumes r1_true coin_inc coin50"
  apply (simp add: subsumes_def coin_inc_def coin50_def posterior_def consistent_def satisfiable_def)
  by auto

lemma "(posterior_sequence [coin_init, coin_inc] empty) = r1_true"
  apply (simp add: posterior_sequence_def posterior_def coin_init_def coin_inc_def satisfiable_def valid_def consistent_def)
  using consistent_empty_1 by force

lemma "\<not> subsumes empty vends_g vends"
  apply (simp add: subsumes_def vends_g_def vends_def posterior_def)
  apply (simp add: consistent_def)
  by auto

lemma "subsumes r1_true vends_g vends"
  apply (simp add: subsumes_def vends_def vends_g_def posterior_def)
  apply (simp add: consistent_def)
  apply safe
  by presburger

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

lemma false_not_equal: "(\<lambda>i. cexp.Bc False) \<noteq> (\<lambda>x. if x = V ''r1'' then cexp.Eq 6 else Contexts.empty x)"
  by (metis cexp.distinct(13))

lemma medial_test1: "medial empty (Guard test1) = (\<lambda>i. if i = V ''i1'' then Eq 6 else empty i)"
  apply (simp add: test1_def)
  apply (rule ext)
  by auto

lemma medial_test2: "medial empty (Guard test2) = (\<lambda>i. if i = V ''i1'' then Gt 0 else empty i)"
  apply (simp add: test2_def)
  apply (rule ext)
  by auto

lemma posterior_test1: "posterior empty test1 = (\<lambda>i. if i = V ''r1'' then Eq 6 else empty i)"
  apply (simp add: test1_def posterior_def consistent_def false_not_equal)
  apply (rule_tac x="<''i1'' := 6>" in exI, simp)
  using consistent_empty_1 by fastforce

lemma false_not_equal_2: "(\<lambda>i. cexp.Bc False) \<noteq> (\<lambda>i. if i = V ''r1'' then cexp.Gt 0 else Contexts.empty i)"
  by (metis cexp.distinct(17))
  
lemma posterior_test2: "posterior empty test2 = (\<lambda>i. if i = V ''r1'' then Gt 0 else empty i)"
  apply (simp add: test2_def posterior_def consistent_def false_not_equal_2)
  apply (rule_tac x="<''i1'' := 6>" in exI, simp)
  using consistent_empty_1 by fastforce

lemma consistent: "consistent (\<lambda>i. if i = V ''r1'' then cexp.Gt 0 else Contexts.empty i)"
  apply (simp add: consistent_def)
  apply (rule_tac x="<''r1'' := 6>" in exI, simp)
  using consistent_empty_1 by fastforce

lemma "subsumes empty test2 test1"
  by (simp add: subsumes_def medial_test1 medial_test2 posterior_test1 posterior_test2 consistent)
end