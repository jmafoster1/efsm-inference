theory EFSM
  imports Types
begin

definition
  S :: "'statename efsm \<Rightarrow> 'statename set" where
  "S m = {a. (\<exists>x. (T m) (a, x) \<noteq> {}) \<or> (\<exists>x. (T m) (x, a) \<noteq> {})}"

primrec apply_outputs :: "output_function list \<Rightarrow> datastate \<Rightarrow> outputs" where
  "apply_outputs [] _ = []" |
  "apply_outputs (h#t) s = (case aval h s of None \<Rightarrow> [] | Some p \<Rightarrow> p#(apply_outputs t s))"

primrec apply_guards :: "guard list \<Rightarrow> datastate \<Rightarrow> bool" where
  "apply_guards [] _ = True" |
  "apply_guards (h#t) s =  ((gval h s) = Some True \<and> (apply_guards t s))"

primrec apply_updates :: "(vname \<times> aexp) list \<Rightarrow> datastate \<Rightarrow> datastate \<Rightarrow> datastate" where
  "apply_updates [] _ new = new" |
  "apply_updates (h#t) old new = (\<lambda>x. if x = (fst h) then (aval (snd h) old) else (apply_updates t old new) x)"

lemma "apply_updates [(R 1, L (Num 6))] <> <R 2:= Num 3> = <R 1:= Num 6, R 2:= Num 3>"
  apply (rule ext)
  by simp

abbreviation is_possible_step :: "'statename efsm \<Rightarrow> 'statename \<Rightarrow> 'statename \<Rightarrow> transition \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> bool" where
"is_possible_step e s s' t r l i \<equiv> (((Label t) = l) \<and> (t \<in> T e (s,s')) \<and> ((length i) = (Arity t)) \<and> (apply_guards (Guard t) (join_ir i r)))"

definition possible_steps :: "'statename efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> ('statename \<times> transition) set" where
(* "possible_steps e s r l i \<equiv> {(s',t) . s' \<in> S e \<and> t \<in> T e (s,s') \<and> is_possible_step e s s' t r l i}" *)
"possible_steps e s r l i \<equiv> {(s',t). is_possible_step e s s' t r l i}"

abbreviation step :: "'statename efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> ('statename \<times> outputs \<times> datastate) option" where
"step e s r l i \<equiv>
(if is_singleton (possible_steps e s r l i) then (let (s', t) =  (the_elem (possible_steps e s r l i)) in Some (s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r))) else None)"

primrec observe_temp :: "'statename efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> ('statename \<times> event \<times> datastate \<times> outputs) list" where
  "observe_temp e s r [] = []" |
  "observe_temp e s r (h#t) =
    (case (step e s r (fst h) (snd h)) of
      (Some (s', outputs, updated)) \<Rightarrow> (s, h, r, outputs)#(observe_temp e s' updated t) |
      _ \<Rightarrow> []
    )"

primrec observe_all :: "'statename efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> ('statename \<times> outputs \<times> datastate) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t) = 
    (case (step e s r (fst h) (snd h)) of
      (Some (s', outputs, updated)) \<Rightarrow> (((s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

abbreviation observe_trace :: "'statename efsm \<Rightarrow> 'statename \<Rightarrow> datastate \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace e s r t \<equiv> map (\<lambda>(x,y,z). y) (observe_all e s r t)"

definition equiv :: "'statename efsm \<Rightarrow> 'statename' efsm \<Rightarrow> trace \<Rightarrow> bool" where
  "equiv e1 e2 t \<equiv> ((observe_trace e1 (s0 e1) <> t) = (observe_trace e2 (s0 e2) <> t))"

lemma equiv_comute: "equiv e1 e2 t \<equiv> equiv e2 e1 t"
  apply (simp add: equiv_def)
  by argo

lemma equiv_trans: "equiv e1 e2 t \<and> equiv e2 e3 t \<longrightarrow> equiv e1 e3 t"
  by (simp add: equiv_def)

lemma equiv_idem: "equiv e1 e1 t"
  by (simp add: equiv_def)

abbreviation valid_trace :: "'statename efsm \<Rightarrow> trace \<Rightarrow> bool" where
  "valid_trace e t \<equiv> (length t = length (observe_all e (s0 e) <> t))"

lemma empty_trace_valid [simp]: "valid_trace e []"
  by simp

primrec in_list :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "in_list _ [] = False" |
  "in_list x (h#t) = (if (x=h) then True else (in_list x t))"

definition can_take :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "can_take t1 t2 \<equiv> ((Label t1) = (Label t2)) \<and> ((Arity t1) = (Arity t2))"

primrec find_match :: "transition \<Rightarrow> destination list \<Rightarrow> destination option" where
  "find_match _ [] = None" |
  "find_match t (h#tail) = (if (can_take t (snd h)) then (Some h) else (find_match t tail))"

lemma valid_unit_trace: "step e (s0 e) <> l i = Some (s',outs,r) \<Longrightarrow> valid_trace e [(l,i)]"
  apply (simp add: is_singleton_def the_elem_def possible_steps_def)
  using Suc_length_conv by fastforce

lemma different_observation_techniques: 
  shows "length(observe_all e s r t) = length(observe_trace e s r t)"
  by simp

lemma valid_extension:
  fixes e and t and l and i and s and r
  assumes "valid_trace e t" 
  and "observe_all e (s0 e) <> t = (oo @ [(s, outs, r)])"
  and "step e s r l i = Some (s'',outs',r')"
shows "valid_trace e (t @ [(l,i)])"
  sorry
  
  

end