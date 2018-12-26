theory Nondeterministic_EFSM
imports EFSM
begin

definition nondeterministic_step :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> outputs \<times> datastate) option" where
"nondeterministic_step e s r l i = (
  if \<exists>x. x |\<in>| (possible_steps e s r l i) then (
    let (s', t) =  (Eps (\<lambda>x. x |\<in>| (possible_steps e s r l i))) in
    Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)))
  else None)"

primrec nondeterministic_observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> (transition \<times> nat \<times> outputs \<times> datastate) list" where
  "nondeterministic_observe_all _ _ _ [] = []" |
  "nondeterministic_observe_all e s r (h#t) =
    (case (nondeterministic_step e s r (fst h) (snd h)) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (((transition, s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

definition nondeterministic_observe_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> observation" where
  "nondeterministic_observe_trace e s r t \<equiv> map (\<lambda>(t,x,y,z). y) (nondeterministic_observe_all e s r t)"

inductive nondeterministic_simulates_trace :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  base: "nondeterministic_simulates_trace e1 e2 s1 s2 d1 d2 []" |
  step_some: "nondeterministic_step e1 s1 d1 (fst h) (snd h) = Some (tr1, s1', p', d1') \<Longrightarrow>
              \<exists>tr2. nondeterministic_step e2 s2 d2 (fst h) (snd h) = Some (tr2, s2', p', d2') \<and>
              nondeterministic_simulates_trace e1 e2 s1' s2' d1' d2' t \<Longrightarrow>
              nondeterministic_simulates_trace e1 e2 s1 s2 d1 d2 (h#t)" |
  step_none: "nondeterministic_step e1 s1 d1 (fst h) (snd h) = None \<Longrightarrow> nondeterministic_simulates_trace e1 e2 s1 s2 d1 d2 (h#t)"

definition nondeterministic_simulates :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "nondeterministic_simulates m1 m2 = (\<forall>t. nondeterministic_simulates_trace m1 m2 0 0 <> <> t)"

end