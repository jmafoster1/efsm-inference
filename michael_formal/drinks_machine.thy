theory drinks_machine
  imports EFSM CExp EFSM_LTL
begin

(* This version of drinks_machine supercedes all of those before 03/04/18 *)
(* It also supercedes "drinks.thy"*)

datatype statename = q0 | q1 | q2

definition select :: transition where
"select \<equiv> \<lparr>
        Label = ''select'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [ (* Two updates: *)
                    (R 1, (V (I 1))), (*  Firstly set value of r1 to value of i1 *)
                    (R 2, (L (Num 0))) (* Secondly set the value of r2 to literal zero *)
                  ]
      \<rparr>"

lemma guard_select [simp]: "Guard select = []"
  by (simp add: select_def)

lemma outputs_select [simp]: "Outputs select = []"
  by (simp add: select_def)

definition coin :: transition where
"coin \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [(Plus (V (R 2)) (V (I 1)))], (* This could also be written infix with ''+'' *)
        Updates = [
                    (R 1, V (R 1)),
                    (R 2, (Plus (V (R 2)) (V (I 1)))) (* The value of r2 is increased by the value of i1 *)
                  ]
      \<rparr>"

lemma guard_coin [simp]: "Guard coin = []"
  by (simp add: coin_def)

definition vend1 :: transition where
"vend1 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(gexp.Lt (V (R 2)) (L (Num 100)))], (* This is syntactic sugar for ''Not (Lt (V ''r2'') (N 100))'' which could also appear *)
        Outputs =  [],
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

definition vend2 :: transition where
"vend2 \<equiv> \<lparr>
        Label = ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))], (* This is syntactic sugar for ''Not (Lt (V ''r2'') (N 100))'' which could also appear *)
        Outputs =  [(V (R 1))], (* This has one output o1:=r1 where ''r1'' is a variable with a value *)
        Updates = [(R 1, V (R 1)), (R 2, V (R 2))]
      \<rparr>"

definition drinks :: "statename efsm" where
"drinks \<equiv> \<lparr> 
          s0 = q0,
          T = \<lambda>(a,b). case (a,b) of
              (q0,q1) \<Rightarrow> {select} |
              (q1,q1) \<Rightarrow> {coin, vend1} |
              (q1,q2) \<Rightarrow> {vend2} |
              _ \<Rightarrow> {}
         \<rparr>"

lemma s0_drinks [simp]: "s0 drinks = q0"
  by (simp add: drinks_def)

(*
  These are lemmas about the machine which could maybe be in another file.
  They don't need to be translated to SAL
*)

lemmas transitions = select_def coin_def vend2_def is_singleton_def the_elem_def

lemma "observe_trace drinks (s0 drinks) <> [] = []"
  by simp

lemma label_select_q1: "Label t = ''select'' \<and>
             t \<in> (if s' = q1 then {select} else if (q0, s') = (q1, q1) then {coin} else if (q0, s') = (q1, q2) then {vend} else {}) \<Longrightarrow> t = select \<and> s' = q1"
  apply (cases s')
    apply simp
   apply simp
  by (simp add: select_def)

lemma label_coin_q1: "Label b = ''coin'' \<Longrightarrow>
           b \<in> (if a = q1 then {coin} else if (q1, a) = (q1, q2) then {vend2} else {}) \<Longrightarrow> b=coin \<and> a = q1"
  apply (cases a)
    apply simp
   apply simp
  by (simp add: vend2_def)

lemma label_vend_q2: "Label b = ''vend'' \<Longrightarrow>
           b \<in> (if a = q1 then {coin} else if (q1, a) = (q1, q2) then {vend2} else {}) \<Longrightarrow> b=vend2 \<and> a = q2"
  apply (cases a)
    apply simp
   apply (simp add: coin_def)
  by (simp add: vend2_def)

lemma possible_steps_q0:  "possible_steps drinks q0 Map.empty ''select'' [Str ''coke''] = {(q1, select)}"
  apply (simp add: possible_steps_def drinks_def)
  apply safe
       apply (metis empty_iff statename.exhaust statename.simps(7) statename.simps(9))
      apply (metis empty_iff singletonD statename.exhaust statename.simps(7) statename.simps(8) statename.simps(9))
     prefer 2
     apply (simp add: drinks_def)
  by (simp_all add: select_def)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke''])] = [[]]"
  by (simp add: is_singleton_def the_elem_def possible_steps_q0)

lemma select_updates [simp]: "(apply_updates (Updates select) (case_vname (\<lambda>n. if n = Suc 0 then Some (Str ''coke'') else index2state [] (Suc 0 + 1) (I n)) Map.empty) Map.empty) = <R 1:=Str ''coke'', R 2 := Num 0>"
  apply (simp add: select_def)
  apply (rule ext)
  by simp

lemma label_coin_q2: "Label b = ''coin'' \<Longrightarrow> b \<in> T drinks (q1, a) \<Longrightarrow> b = coin \<and> a = q1"
  apply (simp add: drinks_def)
  apply (case_tac a)
    apply simp
   apply (metis coin_def insert_iff label_vend_q2 singletonD statename.simps(6) statename.simps(8) transition.simps(1) vend1_def)
  by (simp add: vend2_def)

lemma possible_steps_q1_coin: "possible_steps drinks q1 r ''coin'' [Num n'] = {(q1, coin)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_coin_q2)
      apply (simp add: label_coin_q2)
  by (simp_all add: drinks_def coin_def)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50])] = [[], [Num 50]]"
  apply (simp add: is_singleton_def the_elem_def possible_steps_q0 possible_steps_q1_coin)
  by (simp add: coin_def)

lemma coin_50_updates [simp]: "(apply_updates (Updates coin)
               (case_vname (\<lambda>n. if n = Suc 0 then Some (Num 50) else index2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else <R (Suc 0) := Str ''coke''> (R n)))
               <R (Suc 0) := Str ''coke'', R 2 := Num 0>) = <R 1 := Str ''coke'', R 2 := Num 50>"
  apply (simp add: transitions)
  apply (rule ext)
  by simp

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50])] = [[], [Num 50], [Num 100]]"
  apply (simp add: is_singleton_def the_elem_def possible_steps_q0 possible_steps_q1_coin)
  by (simp add: transitions)

lemma coin_100_updates [simp]: "(apply_updates (Updates coin)
               (case_vname (\<lambda>n. if n = Suc 0 then Some (Num 50) else index2state [] (Suc 0 + 1) (I n)) (\<lambda>n. if n = 2 then Some (Num 50) else <R (Suc 0) := Str ''coke''> (R n)))
               <R (Suc 0) := Str ''coke'', R 2 := Num 50>) = <R 1 := Str ''coke'', R 2 := Num 100>"
  apply (simp add: transitions)
  apply (rule ext)
  by simp

lemma label_vend_q1: "Label b = ''vend'' \<Longrightarrow> b \<in> T drinks (q1, a) \<Longrightarrow> (b = vend2 \<and> a = q2) \<or> (b=vend1 \<and> a = q1)"
  apply (simp add: drinks_def)
  apply (cases a)
    apply simp
   apply (metis insert_iff label_vend_q2 statename.simps(8))
  by simp
  
lemma possible_steps_q2_vend: "possible_steps drinks q1 <R (Suc 0) := Str ''coke'', R 2 := Num 100> ''vend'' [] = {(q2, vend2)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply simp
       apply (case_tac a)
  using label_vend_q1 apply blast
        apply simp
        apply (case_tac "b=vend1")
         apply (simp add: vend1_def)
  using label_vend_q1 apply blast
       apply simp
      apply (case_tac "b = vend2")
       apply simp
      apply (case_tac "b = vend1")
       apply (simp add: vend1_def)
  using label_vend_q1 apply blast
     prefer 2
     apply (simp add: drinks_def)
  by (simp_all add: vend2_def)


lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''coin'', [Num 50]), (''coin'', [Num 50]), (''vend'', [])] = [[], [Num 50], [Num 100], [Str ''coke'']]"
  apply (simp add: possible_steps_q0)
  apply (simp add: possible_steps_q1_coin)
  apply (simp add: possible_steps_q2_vend)
  by (simp add: coin_def vend2_def)

lemma q1_q1_not_cat: "b \<in> T drinks (q1, q1) \<longrightarrow> Label b \<noteq> ''cat''"
  by (simp add: drinks_def coin_def vend1_def)

lemma q1_q2_not_cat: "b \<in> T drinks (q1, q2) \<longrightarrow> Label b \<noteq> ''cat''"
  by (simp add: drinks_def vend2_def)

lemma cat_impossible: "possible_steps drinks q1 <R (Suc 0) := Str ''coke'', R 2 := Num 0> ''cat'' [Num 50] = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI, rule allI)
  apply (case_tac a)
    apply (simp add: drinks_def)
   apply (simp add: q1_q1_not_cat)
  by (simp add: q1_q2_not_cat)

(*Stop when we hit a spurious input*)
lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''cat'', [Num 50])] = [[]]"
  by (simp add: is_singleton_def the_elem_def possible_steps_q0 cat_impossible)

lemma "\<not> (valid_trace (drinks) [(''select'', [Str ''coke'']), (''cat'', [Num 50])])"
  apply (simp add: possible_steps_q0 cat_impossible)
  by (simp add: transitions)

lemma "observe_trace drinks (s0 drinks) <> [(''select'', [Str ''coke'']), (''cat'', [Num 50]), (''coin'', [Num 50])] = [[]]"
  apply (simp add: possible_steps_q0 cat_impossible)
  by (simp add: transitions)

lemma "( t = []) \<Longrightarrow> (observe_trace e (s0 e) <> t = []) "
  by(simp)

abbreviation watch_drinks :: "event stream \<Rightarrow> statename full_observation" where
  "watch_drinks i \<equiv> (make_full_observation drinks (Some (s0 drinks)) <> i)"

abbreviation dispense_drink :: "statename property" where
  "dispense_drink s \<equiv> (label (shd s) = ''vend'') \<and> (\<exists>x. output (shd s) = [x]) \<and> (statename (shd s) = Some q0)"

abbreviation r2_100 :: "statename property" where
  "r2_100 s \<equiv> gval (Ge (V (R 2)) (L(Num 100))) (datastate (shd s)) = Some True"

lemma select_drink_first: "\<exists>d. shd t = (''select'', [d]) = ((make_full_observation drinks (Some q0) Map.empty t) = \<lparr>statename=Some q0, datastate = <>, event=(''select'', [d]), output=[]\<rparr>##(make_full_observation drinks (Some q1) <R 1 := d, R 2 := Num 0> (stl t)))"
proof -
  have f1: "\<forall>v vs va vsa. ((v::value) # vs = va # vsa) = (v = va \<and> vs = vsa)"
    by blast
  have f2: "[Num 1] \<noteq> [Num 0]"
by simp
  have f3: "\<forall>cs vs csa vsa. ((cs::char list, vs::value list) = (csa, vsa)) = (cs = csa \<and> vs = vsa)"
    by blast
  have f4: "\<forall>z f p vs u za fa pa vsa ua. (\<lparr>statename = z::statename option, datastate = f, event = p, output = vs, \<dots> = u::unit\<rparr> = \<lparr>statename = za, datastate = fa, event = pa, output = vsa, \<dots> = ua\<rparr>) = (z = za \<and> f = fa \<and> p = pa \<and> vs = vsa \<and> u = ua)"
    by blast
  have "\<forall>s sa sb sc. ((s::statename state) ## sa = sb ## sc) = (s = sb \<and> sa = sc)"
    by fastforce
  then have f5: "\<lparr>statename = Some q0, datastate = <>, event = (''select'', [Num 1]), output = []\<rparr> ## make_full_observation drinks (Some q1) <R 1 := Num 1, R 2 := Num 0> (stl t) \<noteq> \<lparr>statename = Some q0, datastate = <>, event = (''select'', [Num 2]), output = []\<rparr> ## make_full_observation drinks (Some q1) <R 1 := Num 2, R 2 := Num 0> (stl t)"
    using f4 f3 f1 value.inject(1) by presburger
  have f6: "\<lparr>statename = Some q0, datastate = <>, event = (''select'', [Num 1]), output = []\<rparr> ## make_full_observation drinks (Some q1) <R 1 := Num 1, R 2 := Num 0> (stl t) \<noteq> \<lparr>statename = Some q0, datastate = <>, event = (''select'', [Num 0]), output = []\<rparr> ## make_full_observation drinks (Some q1) <R 1 := Num 0, R 2 := Num 0> (stl t)"
    by fastforce
  have f7: "(''select'', [Num 1]) \<noteq> (''select'', [Num 2])"
    using f3 f1 value.inject(1) by presburger
  have f8: "(''select'', [Num 2]) \<noteq> (''select'', [Num 0])"
    by auto
  have "\<lparr>statename = Some q0, datastate = <>, event = (''select'', [Num 2]), output = []\<rparr> ## make_full_observation drinks (Some q1) <R 1 := Num 2, R 2 := Num 0> (stl t) \<noteq> \<lparr>statename = Some q0, datastate = <>, event = (''select'', [Num 0]), output = []\<rparr> ## make_full_observation drinks (Some q1) <R 1 := Num 0, R 2 := Num 0> (stl t)"
by fastforce
  then show ?thesis
    using f8 f7 f6 f5 f3 f2 by (metis (no_types))
qed

lemma "(ev null) (watch_drinks t)"
  sorry

(* <>P -> (!P U (S & !P)) *)
lemma "((ev dispense_drink) impl ((not dispense_drink) until (r2_100 aand (not dispense_drink)))) (watch_drinks t)"
proof (induction)
  case q0
  then show ?case
    apply simp
      sorry
  next
  case q1
  then show ?case sorry
next
  case q2
  then show ?case sorry
qed
end
