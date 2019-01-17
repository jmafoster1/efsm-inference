theory Nondeterministic_EFSM
imports EFSM
begin

definition nondeterministic_step :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> nat \<times> outputs \<times> datastate) option" where
"nondeterministic_step e s r l i = (
  if \<exists>x. x |\<in>| (possible_steps e s r l i) then (
    let (s', t) =  (Eps (\<lambda>x. x |\<in>| (possible_steps e s r l i))) in
    Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)))
  else None)"

lemma [code]: "nondeterministic_step e s r l i = (
  if possible_steps e s r l i \<noteq> {||} then (
    let (s', t) =  (Eps (\<lambda>x. x |\<in>| (possible_steps e s r l i))) in
    Some (t, s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)))
  else None)"
  apply (simp add: nondeterministic_step_def)
  by auto

lemma fis_singleton_possible_steps: "fis_singleton (possible_steps e s r l i) \<Longrightarrow> \<exists>a b. (a, b) |\<in>| possible_steps e s r l i"
  by (metis fempty_iff fset_eqI not_singleton_emty prod.exhaust_sel)

lemma singleton_elem_eps: "is_singleton s \<Longrightarrow> the_elem s = x \<Longrightarrow> (SOME x. x \<in> s) = x"
  by (simp add: is_singleton_the_elem)

lemma step_nondet_step_equiv: "step e s r l i = Some t \<Longrightarrow> nondeterministic_step e s r l i = Some t"
  apply (simp add: step_def nondeterministic_step_def)
  apply (case_tac "fis_singleton (possible_steps e s r l i)")
   apply (case_tac "fthe_elem (possible_steps e s r l i)")
   apply simp
   apply clarify
   apply (case_tac "SOME x. x |\<in>| possible_steps e s r l i")
   apply simp
   apply (simp add: fis_singleton_possible_steps)
   apply (simp add: fis_singleton_def fthe_elem_def fmember_def)
   apply (simp add: singleton_elem_eps)
  by simp

primrec nondeterministic_observe_all :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> (transition \<times> nat \<times> outputs \<times> datastate) list" where
  "nondeterministic_observe_all _ _ _ [] = []" |
  "nondeterministic_observe_all e s r (h#t) =
    (case (nondeterministic_step e s r (fst h) (snd h)) of
      (Some (transition, s', outputs, updated)) \<Rightarrow> (((transition, s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

definition nondeterministic_observe_trace :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> observation" where
  "nondeterministic_observe_trace e s r t \<equiv> map (\<lambda>(t,x,y,z). y) (nondeterministic_observe_all e s r t)"

inductive nondeterministic_simulates_trace :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  base: "nondeterministic_simulates_trace e2 e1 s2 s1 d2 d1 [] _" |
  step_some: "s2 = H s1 \<Longrightarrow>
              nondeterministic_step e1 s1 d1 l i = Some (tr1, s1', p', d1') \<Longrightarrow>
              (s2', tr2) |\<in>| possible_steps e2 s2 d2 l i \<Longrightarrow>
              d2' = (apply_updates (Updates tr2) (join_ir i d2) d2) \<Longrightarrow>
              p' = (apply_outputs (Outputs tr2) (join_ir i r)) \<Longrightarrow>
              nondeterministic_simulates_trace e2 e1 s2' s1' d2' d1' t H \<Longrightarrow>
              nondeterministic_simulates_trace e2 e1 s2 s1 d2 d1 ((l, i)#t) H" |
  step_none: "nondeterministic_step e1 s1 d1 l i = None \<Longrightarrow> nondeterministic_simulates_trace e2 e1 s2 s1 d2 d1 ((l, i)#t) _"

lemma nondeterministic_step_none: "nondeterministic_step e s r l i = None \<Longrightarrow> step e s r l i = None"
proof-
  assume premise: "nondeterministic_step e s r l i = None"
  have aux1: "\<forall>a b. (a, b) |\<notin>| possible_steps e s r l i \<Longrightarrow>
        possible_steps e s r l i = {||}"
    by auto
  show ?thesis
    using premise
    apply (simp add: step_def nondeterministic_step_def)
    apply (case_tac "\<exists>a b. (a, b) |\<in>| possible_steps e s r l i")
     apply simp
     apply (cases "SOME x. x |\<in>| possible_steps e s r l i")
     apply simp
    apply simp
    apply clarify
    by (simp add: aux1)
qed

definition nondeterministic_simulates :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "nondeterministic_simulates m2 m1 H = (\<forall>t. nondeterministic_simulates_trace m2 m1 0 0 <> <> t H)"

inductive nondeterministic_accepts :: "transition_matrix \<Rightarrow> nat \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> bool" where
  base: "nondeterministic_accepts e s d []" |
  step: "nondeterministic_step e s d (fst h) (snd h) = Some (tr, s', p', d') \<Longrightarrow> nondeterministic_accepts e s' d' t \<Longrightarrow> nondeterministic_accepts e s d (h#t)"

definition nondeterministic_accepts_trace :: "transition_matrix \<Rightarrow> trace \<Rightarrow> bool" where
  "nondeterministic_accepts_trace e t = nondeterministic_accepts e 0 <> t"

lemma no_nondeterministic_step_none: "nondeterministic_step e s r aa ba = None \<Longrightarrow> \<not>nondeterministic_accepts e s r ((aa, ba) # p)"
  apply safe
  apply (rule nondeterministic_accepts.cases)
    apply simp
   apply simp
  by auto


end