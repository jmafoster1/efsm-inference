theory valid_aux
  imports EFSM
begin

lemma valid_trace_head_not_none:  "valid_trace efsm [a] \<Longrightarrow> ( step efsm (s0 efsm) <> (fst a) (snd a) \<noteq> None)"
  apply(simp add:valid_trace_def)
  apply(cases  "(step efsm (s0 efsm) <> (fst a) (snd a)) = None")
   by(simp_all)

lemma valid_trace_cons: "valid_trace efsm (a#t) \<Longrightarrow> valid_trace efsm [a]"
  apply(unfold valid_trace_def)
  apply(simp)
  apply(cases  "(step efsm (s0 efsm) <> (fst a) (snd a)) = None")
  apply(simp)
  by auto

lemma lengh_observe_all_restricted: "\<And>s r. length (observe_all e s r t) \<le> length t"
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


end
