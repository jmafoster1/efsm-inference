theory EFSM
  imports Constraints
begin

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
    [] \<Rightarrow> None |
    [(s',t)] \<Rightarrow> Some (s', (apply_outputs (Outputs t) (input2state i 1) r), (apply_updates (Updates t) (input2state i 1) r)) |
    _ \<Rightarrow> None"

primrec observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace _ _ _ [] = []" |
  "observe_trace e s r (h#t) = 
    (case (step e s r (fst h) (snd h)) of
      None \<Rightarrow> [] |
      Some (s', outputs, updated) \<Rightarrow> (outputs#(observe_trace e s' updated t))
    )"

primrec observe_all :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (statename \<times> outputs \<times> registers) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r (h#t) = 
    (case (step e s r (fst h) (snd h)) of
      None \<Rightarrow> [] |
      (Some (s', outputs, updated)) \<Rightarrow> (((s', outputs, updated)#(observe_all e s' updated t)))
    )"

primrec observe_registers :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> state" where
  "observe_registers _ _ r [] = r" |
  "observe_registers e s r (h#t) = 
    (case (step e s r (fst h) (snd h)) of
      None \<Rightarrow> r |
      Some (s', outputs, updated) \<Rightarrow> (observe_registers e s' updated t)
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

definition valid_trace :: "efsm \<Rightarrow> trace \<Rightarrow> bool" where
  "valid_trace e t = (length t = length (observe_all e (s0 e) <> t))"

lemma empty_trace_valid [simp]: "valid_trace e []"
  by(simp add:valid_trace_def)

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

(*fun match_all :: "efsm \<Rightarrow> destination list \<Rightarrow> efsm \<Rightarrow> destination list \<Rightarrow> statename list \<Rightarrow> bool"
  and compare :: "efsm \<Rightarrow> statename \<Rightarrow> efsm \<Rightarrow> statename \<Rightarrow> statename list \<Rightarrow> bool"
  where
  "match_all _  []    _  _  _      = True" |
  "match_all e1 (h#t) e2 d2 open = (
    case (find_match (snd h) d2) of
      None \<Rightarrow> False |
      Some (s', _) \<Rightarrow> ((compare e1 (fst h) e2 s' open) \<and> (match_all e1 t e2 d2 open))
    )" |
  "compare e1 s1 e2 s2 open = (if (in_list s1 open) then (match_all e1 (all_outs e1 s1) e2 (all_outs e2 s2) (removeAll s1 open)) else True)"

definition simulates :: "efsm \<Rightarrow> efsm \<Rightarrow> bool" where
  "simulates e1 e2 = compare e1 (s0 e1) e2 (s0 e2) (S e1)"
*)
end