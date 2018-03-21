theory Vend
  imports EFSM
begin

definition t1 :: "transition" where
"t1 \<equiv> \<lparr> label = ''select'',
        arity = 1,
        guard = trueguard, 
        outputs = noouts,
        (* updates = \<lambda>(ip,dt) . (dt \<oplus> (1,ip(1))) \<oplus> (2, Some (I 0)) *)
        updates = u [r1 := i1, r2 := I 0]
      \<rparr>"

abbreviation u1 :: "updates" where
"u1 \<equiv> \<lambda>(ip,dt) . dt \<oplus> (2,(dt(2)) + (ip(1)))"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr> label = ''coin'',
        arity = 1,
        guard = \<lambda>(ip,dt). (ip(1) > (Some (I 0))), (* make_struct ''i1 > 0'' *)
        outputs = noouts,
        updates = u1
      \<rparr>"

definition t3 :: "transition" where
"t3 \<equiv> \<lparr> label = ''vend'',
        arity = 1,
        guard = \<lambda>(ip,dt) . (dt(2)) \<ge> (Some (I 100)), 
        outputs = \<lambda>(ip,dt) . blankouts \<oplus> (1,dt(1)),
        updates = noupdates
      \<rparr>"

definition vend :: "efsm" where
"vend \<equiv> \<lparr> S = [1,2,3],
          s0 = 1,
          M = map_of [
                      ((1,2),[t1]),
                      ((2,2),[t2]),
                      ((2,3),[t3])
                     ]
         \<rparr>"

lemma "possible_steps vend 1 ''coin'' blankips blankdata == []"
  by (simp add: vend_def t1_def)
lemma "possible_steps vend 1 ''select'' blankips blankdata == [(2,t1)]"
  by (simp add: vend_def t1_def)
lemma "possible_steps vend 2 ''coin'' (blankips \<oplus> (1,(Some (I 50)))) blankdata == [(2,t2)]"
  by (simp add: vend_def t2_def t3_def)
lemma "possible_steps vend 2 ''vend'' blankips blankdata \<noteq> [(3,t3)]"
  by (simp add: vend_def t2_def t3_def)
lemma "possible_steps vend 2 ''vend'' blankips (blankdata \<oplus> (1,Some (I 50))) \<noteq> [(3,t3)]"
  by (simp add: vend_def t2_def t3_def)
lemma "possible_steps vend 2 ''vend'' blankips (blankdata \<oplus> (1,Some (I 99))) \<noteq> [(3,t3)]"
  by (simp add: vend_def t2_def t3_def)
lemma "possible_steps vend 2''vend'' blankips ((blankdata \<oplus> (1,Some (I 42))) \<oplus> (2,Some (I 100))) = [(3,t3)]"
  by (simp add: vend_def t2_def t3_def)

lemma "step vend 2 ''coin'' (blankips  \<oplus> (1,Some (I 50))) (blankdata \<oplus> (2,Some (I 0))) = Some (2, blankouts, (blankdata \<oplus> (2,Some (I 50))))"
  by (simp add: vend_def t2_def t3_def) auto

definition tr1 :: "trace" where
"tr1 \<equiv> make_trace [(''select'',[St ''coke'']),(''coin'',[I 50]),(''coin'',[I 50]),(''vend'',[])]"
definition ob1 :: "observation" where
"ob1 \<equiv> make_obs [[],[],[],[St ''coke'']]"

definition tr2 :: "trace" where
"tr2 \<equiv> make_trace [(''select'',[St ''coke'']),(''coin'',[I 50]),(''coin'',[I 50])]"
definition ob2 :: "observation" where
"ob2 \<equiv> make_obs [[],[],[]]"

definition tr3 :: "trace" where
"tr3 \<equiv> make_trace [(''select'',[I 42])]"
definition ob3 :: "observation" where
"ob3 \<equiv> make_obs [[]]"

lemma "observe vend tr3 = ob3" 
 by (simp add: vend_def tr3_def observe_def t1_def fst_def ob3_def)  

lemma "observe vend tr2 = ob2" 
  by (simp add: vend_def tr2_def observe_def ob2_def t1_def t2_def t3_def)  

lemma "observe vend tr1 = ob1"
  by (simp add: vend_def tr1_def observe_def ob1_def t1_def t2_def t3_def)

lemma  "allPairs [1, 2, 3] = [(1, 1), (2, 1), (1, 2), (3, 1), (1, 3), (2, 2), (3, 2), (2, 3), (3, 3)]"
  by simp

end