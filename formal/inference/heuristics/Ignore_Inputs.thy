theory Ignore_Inputs
imports "../Inference"
begin

definition enumerate_outputs :: "iEFSM \<Rightarrow> label \<Rightarrow> arity \<Rightarrow>  opred list fset" where
  "enumerate_outputs e l a = (fimage (\<lambda>(_, _, t). Outputs t) (ffilter (\<lambda>(_, _, t). Label t = l \<and> Arity t = a) e))"

definition drop_guards :: "transition \<Rightarrow> transition" where
  "drop_guards t = \<lparr>Label = Label t, Arity = Arity t, Guard = [], Outputs = Outputs t, Updates = Updates t\<rparr>"

lemma can_take_transition_right_length: "length i = Arity t \<Longrightarrow> can_take_transition (drop_guards t) i c"
  by (simp add: drop_guards_def can_take_transition_def can_take_def)

definition drop_inputs :: "update_modifier" where
  "drop_inputs t1ID t2ID s new old np = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID) in
     if fis_singleton (enumerate_outputs new (Label t1) (Arity t1)) then
     Some (fimage 
      (\<lambda>(id, route, t). 
       if id = t1ID then
         (id, route, drop_guards t)
       else (id, route, t)) (ffilter (\<lambda>(id, _). id \<noteq> t2ID) new))
     else None
   )"

definition transitionwise_drop_inputs :: update_modifier where
  "transitionwise_drop_inputs t1ID t2ID s new old np = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID) in
     if Outputs t1 = Outputs t2 then
       Some (replace (drop_transition new t2ID) t1ID (drop_guards t1))
     else
       None)"

definition statewise_drop_inputs :: "update_modifier" where
  "statewise_drop_inputs t1ID t2ID s new old np = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID) in
     if \<forall>(_, t, _) |\<in>| outgoing_transitions s new. (Label t = Label t1 \<and> Arity t = Arity t1) \<longrightarrow> Outputs t = Outputs t1 then
       Some (replace (drop_transitions new ((fimage (comp snd snd) (outgoing_transitions s new)) - {|t1ID|})) t1ID (drop_guards t1))
     else
       None)"

lemma drop_inputs_subsumption: "subsumes (drop_guards t1) c t1"
  apply (rule subsumption)
      apply (simp add: drop_guards_def)
     apply (simp add: drop_guards_def can_take_def can_take_transition_def)
    apply (simp add: drop_guards_def)
   apply (simp add: drop_guards_def posterior_separate_def)
   apply auto[1]
  apply (simp add: drop_guards_def posterior_def posterior_separate_def)
  by auto

end