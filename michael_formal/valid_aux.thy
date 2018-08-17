theory valid_aux
  imports EFSM Filesystem
begin

abbreviation "reg_of t \<equiv> (if t = [] then <> else snd (snd (last t)))"
abbreviation "state_of e t \<equiv> (if t = [] then s0 e else fst (last t))"

lemma valid_trace_non_empty_observe: "valid_trace e (a#list) \<Longrightarrow> [] \<noteq> observe_all e (s0 e) <> (a # list)"
  by fastforce

lemma nonempty: "valid_trace e t \<and> t \<noteq> [] \<longrightarrow> observe_all e (s0 e) <> t \<noteq> []"
  by auto

lemma first_none_invalid: "step efsm (s0 efsm) <> (fst a) (snd a) = None \<Longrightarrow> \<not> valid_trace efsm [a]"
  apply (cases "is_singleton (possible_steps efsm (s0 efsm) Map.empty (fst a) (snd a))")
   apply simp
  by simp

lemma valid_trace_head_not_none:  "valid_trace efsm [a] \<Longrightarrow> (step efsm (s0 efsm) <> (fst a) (snd a) \<noteq> None)"
  apply (rule ccontr)
  using first_none_invalid by blast

lemma valid_trace_cons: "valid_trace efsm (a#t) \<Longrightarrow> valid_trace efsm [a]"
  apply(simp)
  apply (cases "is_singleton (possible_steps efsm (s0 efsm) Map.empty (fst a) (snd a))")
   apply (simp add: the_elem_def)
   apply (cases "THE x. possible_steps efsm (s0 efsm) Map.empty (fst a) (snd a) = {x}")
   apply simp
  by simp

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

inductive valid :: "'statename efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  base: "valid e s d []" |
  step: "step e s d (fst h) (snd h) = Some (s', p', d') \<Longrightarrow> valid e s' d' t \<Longrightarrow> valid e s d (h#t)"

lemma "\<not> valid filesystem (s0 filesystem) <> [(''lalal'', [])]"
  sorry

lemma valid_steps: "the_elem (possible_steps e s d (fst h) (snd h)) = (a, b) \<Longrightarrow>
       is_singleton (possible_steps e s d (fst h) (snd h)) \<Longrightarrow>
       valid e a (apply_updates (Updates b) (case_vname (\<lambda>n. index2state (snd h) (Suc 0) (I n)) (\<lambda>n. d (R n))) d) t \<Longrightarrow>
       valid e s d (h#t)"
  by (simp add: valid.step)

lemma invalid_conditions: "\<not>valid e s d (h # t) \<Longrightarrow> step e s d (fst h) (snd h) = None \<or> (\<exists>s' p' d'. step e s d (fst h) (snd h) =  Some (s', p', d') \<and> \<not>valid e s' d' t)"
  apply simp
  apply (case_tac "the_elem (possible_steps e s d (fst h) (snd h))")
  apply simp
  apply safe
  by (simp add: valid_steps)

lemma "((step e s d (fst h) (snd h)) = None) \<Longrightarrow>\<not> (valid e s d (h#t))"
  apply(clarify)
  apply(cases rule:valid.cases)
    apply(simp)
   apply simp
  by(auto)



lemma "step e s d (fst h) (snd h) = None \<Longrightarrow> \<not>valid e s d (h # t)"
proof (induction "\<not>valid e s d (h # t)")
case True
then show ?case by simp
next
  case False
  then show ?case
    apply simp
qed


lemma conditions_invalid: "step e s d (fst h) (snd h) = None \<or> (\<exists>s' p' d'. step e s d (fst h) (snd h) =  Some (s', p', d') \<and> \<not>valid e s' d' t) \<Longrightarrow> \<not> valid e s d (h # t)"
  apply safe
  sorry

lemma valid_head: "valid e s d (h#t) \<Longrightarrow> valid e s d [h]"
  by (meson base conditions_invalid invalid_conditions)

lemma invalid_prefix: "\<not>valid e s d t \<Longrightarrow> \<not>valid e s d (t@t')"
proof (induction t)
  case Nil
  then show ?case by (simp add: base)
next
  case (Cons h t)
  then show ?case
    apply simp
    apply (case_tac "step e s d (fst h) (snd h)")
qed

lemma prefix_closure: "valid e s d (t@t') \<Longrightarrow> valid e s d t"
  apply (rule ccontr)
  by (simp add: invalid_prefix)



lemma "valid_trace e (t@[t']) \<Longrightarrow> valid_trace e t"
proof (induct "t@[t']" rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then show ?case
    apply simp
      sorry
  qed

lemma "(valid_trace e (ts@[t]) \<longrightarrow> valid_trace e ts)" 
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