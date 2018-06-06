theory valid_aux
  imports EFSM
begin

abbreviation "reg_of t \<equiv> (if t = [] then <> else snd (snd (last t)))"
abbreviation "state_of e t \<equiv> (if t = [] then s0 e else fst (last t))"

lemma valid_trace_non_empty_observe: "valid_trace e (a#list) \<Longrightarrow> [] \<noteq> observe_all e (s0 e) <> (a # list)"
  apply(simp only:observe_all.simps(2))
  by auto

lemma nonempty: "valid_trace e t \<and> t \<noteq> [] \<longrightarrow> observe_all e (s0 e) <> t \<noteq> []"
  by auto

lemma valid_trace_head_not_none:  "valid_trace efsm [a] \<Longrightarrow> ( step efsm (s0 efsm) <> (fst a) (snd a) \<noteq> None)"
  apply simp
  apply(cases  "(step efsm (s0 efsm) <> (fst a) (snd a)) = None")
  by(simp_all)

lemma valid_trace_cons: "valid_trace efsm (a#t) \<Longrightarrow> valid_trace efsm [a]"
  apply(simp)
  apply(cases  "(step efsm (s0 efsm) <> (fst a) (snd a)) = None")
  apply(simp)
  by auto

lemma length_observe_all_restricted: "\<And>s r. length (observe_all e s r t) \<le> length t"
proof (induction t) 
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case 
  proof cases 
    assume "step e s r (fst a) (snd a) = None"
    then show ?thesis by simp  
  next 
    assume "step e s r (fst a) (snd a) \<noteq>  None"
    with Cons show ?thesis by(auto) 
  qed
qed

(* abbreviation "drop_last a \<equiv> rev (tl (rev a))" *)

function drop_last :: "'a list \<Rightarrow> 'a list" where
"drop_last [] = []" |
"drop_last (xs@[x]) = xs"
  using rev_exhaust apply blast
  by simp_all
termination drop_last
  using "termination" by blast

function last :: "'a list \<Rightarrow> 'a list" where
"last [] = []" |
"last (xs@[x]) = [x]"
  using rev_exhaust apply blast
  by simp_all
termination last
  using "termination" by blast

lemma foo: "step e (s0 e) <> (fst a) (snd a) = None \<or>  (\<exists>s' outputs updated. step e (s0 e) <> (fst a) (snd a) = Some (s', outputs, updated))"
  apply (cases "step e (s0 e) <> (fst a) (snd a)")
   apply simp
  by auto

lemma "(valid_trace_1 e s <> (ts@[t]) \<longrightarrow> valid_trace_1 e s <> ts)" 
proof (induct ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  then show ?case 
    apply simp
    apply (case_tac "step e s <> (fst a) (snd a) = None")
     apply simp
    apply simp
    apply (rule_tac exE)
qed


  


  

lemma "valid_trace e t \<Longrightarrow> ((observe_all e (s0 e) <> (drop_last t)) = xs \<longrightarrow> (observe_all e (s0 e) <> t) = xs@(observe_all e (state_of e xs) (reg_of xs) (last t)))"
proof (induct t rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc y ys)
  then show ?case 
    apply simp
     apply (case_tac "step e (s0 e) <> (fst y) (snd y) = None")
      apply simp

qed


  




end