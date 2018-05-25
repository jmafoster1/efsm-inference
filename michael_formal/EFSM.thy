theory EFSM
  imports Types
begin

primrec apply_outputs :: "output_function list \<Rightarrow> state \<Rightarrow> registers \<Rightarrow> outputs" where
  "apply_outputs [] _ _ = []" |
  "apply_outputs (h#t) i r = (aval h (join i r))#(apply_outputs t i r)"

primrec apply_guards :: "guard list \<Rightarrow> state \<Rightarrow> registers \<Rightarrow> bool" where
  "apply_guards [] _ _ = True" |
  "apply_guards (h#t) i r =  ((gval h (join i r)) \<and> (apply_guards t i r))"

primrec apply_updates :: "(string \<times> aexp) list \<Rightarrow> state \<Rightarrow> registers \<Rightarrow> registers" where
  "apply_updates [] _ _ = <>" |
  "apply_updates (h#t) i r = join <(fst h) := (aval (snd h) (join i r))> (apply_updates t i r)"

abbreviation is_possible_step :: "efsm \<Rightarrow> statename \<Rightarrow> statename \<Rightarrow> transition \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> bool" where
"is_possible_step e s s' t r l i \<equiv> (((Label t) = l) \<and> (find (\<lambda>x . x = t) (T e(s,s')) \<noteq> None) \<and> ((length i) = (Arity t)) \<and> (apply_guards (Guard t) (input2state i 1) r))"

abbreviation possible_steps :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename * transition) list" where
"possible_steps e s r l i \<equiv> [(s',t) . s' \<leftarrow> S e, t \<leftarrow> T e(s,s'), is_possible_step e s s' t r l i]"

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option" where
"step e s r l i \<equiv>
  case (possible_steps e s r l i) of
    [(s',t)] \<Rightarrow> Some (s', (apply_outputs (Outputs t) (input2state i 1) r), (apply_updates (Updates t) (input2state i 1) r)) |
    _ \<Rightarrow> None"

primrec observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace _ _ _ [] = []" |
  "observe_trace e s r (h#t) = 
    (case (step e s r (fst h) (snd h)) of
      Some (s', outputs, updated) \<Rightarrow> (outputs#(observe_trace e s' updated t)) |
      _ \<Rightarrow> []
    )"

primrec observe_all :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (statename \<times> outputs \<times> registers) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t) = 
    (case (step e s r (fst h) (snd h)) of
      (Some (s', outputs, updated)) \<Rightarrow> (((s', outputs, updated)#(observe_all e s' updated t))) |
      _ \<Rightarrow> []
    )"

definition equiv :: "efsm \<Rightarrow> efsm \<Rightarrow> trace \<Rightarrow> bool" where
  "equiv e1 e2 t \<equiv> ((observe_trace e1 (s0 e1) <> t) = (observe_trace e2 (s0 e2) <> t))"

lemma equiv_comute: "equiv e1 e2 t \<equiv> equiv e2 e1 t"
  apply (simp add: equiv_def)
  by argo

lemma equiv_trans: "equiv e1 e2 t \<and> equiv e2 e3 t \<longrightarrow> equiv e1 e3 t"
  by (simp add: equiv_def)

lemma equiv_idem: "equiv e1 e1 t"
  by (simp add: equiv_def)

primrec valid_trace_1 :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  "valid_trace_1 _ _ _ [] = True" |
  "valid_trace_1 e s r (h#t) = 
    (case (step e s r (fst h) (snd h)) of
      Some (s', _, updated) \<Rightarrow> (valid_trace_1 e s' updated t) |
      _ \<Rightarrow> False
    )"

abbreviation valid_trace :: "efsm \<Rightarrow> trace \<Rightarrow> bool" where
  "valid_trace e t \<equiv> (length t = length (observe_all e (s0 e) <> t))"

lemma "valid_trace e t = valid_trace_1 e (s0 e) <> t"
proof (induct t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply (cases "step e (s0 e) <> (fst a) (snd a)")
     apply simp
    apply simp
    apply safe
qed


lemma empty_trace_valid [simp]: "valid_trace e []"
  by simp

primrec in_list :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "in_list _ [] = False" |
  "in_list x (h#t) = (if (x=h) then True else (in_list x t))"

definition all_outs :: "efsm \<Rightarrow> statename \<Rightarrow> destination list" where
  "all_outs e s = [(s',t) . s' \<leftarrow> S e, t \<leftarrow> T e(s,s'), (in_list t (T e(s,s')))]"

definition can_take :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "can_take t1 t2 \<equiv> ((Label t1) = (Label t2)) \<and> ((Arity t1) = (Arity t2))"

primrec find_match :: "transition \<Rightarrow> destination list \<Rightarrow> destination option" where
  "find_match _ [] = None" |
  "find_match t (h#tail) = (if (can_take t (snd h)) then (Some h) else (find_match t tail))"
end