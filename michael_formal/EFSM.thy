theory EFSM
  imports types
begin

definition apply_updates :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> state" where
  "apply_updates t i r = (Updates t) i r"
declare apply_updates_def [simp]

definition apply_outputs :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> outputs" where
  "apply_outputs t i r = (Outputs t) i r"
declare apply_outputs_def [simp]

definition blank :: output_function where
  "blank _ _ = []"
declare blank_def [simp]

definition trueguard :: guard  where
  "trueguard _ _ = True"
declare trueguard_def [simp]

definition no_updates :: update_function where
  "no_updates _ r = r"
declare no_updates_def [simp]

abbreviation is_possible_step :: "efsm \<Rightarrow> statename \<Rightarrow> statename \<Rightarrow> transition \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> bool" where
"is_possible_step e s s' t r l i \<equiv> (((Label t) = l) \<and> (find (\<lambda>x . x = t) (T e(s,s')) \<noteq> None) \<and> ((length i) = (Arity t)) \<and> ((Guard t) i r))"

abbreviation possible_steps :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename * transition) list" where
"possible_steps e s r l i \<equiv> [(s',t) . s' \<leftarrow> S e, t \<leftarrow> T e(s,s'), is_possible_step e s s' t r l i]"

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option" where
"step e s r l i \<equiv>
  case (possible_steps e s r l i) of
    [] \<Rightarrow> None |
    [(s',t)] \<Rightarrow> Some (s', (apply_outputs t i r), (apply_updates t i r)) |
    _ \<Rightarrow> None"
declare step_def [simp]

primrec observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace _ _ _ [] = []" |
  "observe_trace e s r (h#t) = 
    (case (step e s r (fst h) (snd h)) of
      None \<Rightarrow> [] |
      Some (s', outputs, updated) \<Rightarrow> (outputs#(observe_trace e s' updated t))
    )"
declare observe_trace_def [simp]

definition equiv :: "efsm \<Rightarrow> efsm \<Rightarrow> trace \<Rightarrow> bool" where
  "equiv e1 e2 t \<equiv> ((observe_trace e1 (s0 e1) <> t) = (observe_trace e2 (s0 e2) <> t))"
declare equiv_def [simp]

lemma equiv_comute: "equiv e1 e2 t \<equiv> equiv e2 e1 t"
  apply simp
  by argo

lemma equiv_trans: "equiv e1 e2 t \<and> equiv e2 e3 t \<longrightarrow> equiv e1 e3 t"
  by simp

lemma equiv_idem: "equiv e1 e1 t"
  by simp

definition all_outs :: "efsm \<Rightarrow> statename \<Rightarrow> destination list" where
  "all_outs e s = [(s',t) . s' \<leftarrow> S e, t \<leftarrow> T e(s,s'), (find (\<lambda>x . x = t) (T e(s,s')) \<noteq> None)]"

definition can_take :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "can_take t1 t2 \<equiv> ((Label t1) = (Label t2)) \<and> ((Arity t1) = (Arity t2))"

primrec find_match :: "transition \<Rightarrow> destination list \<Rightarrow> destination option" where
  "find_match _ [] = None" |
  "find_match t (h#tail) = (if (can_take t (snd h)) then (Some h) else (find_match t tail))"

fun match_all :: "efsm \<Rightarrow> (string, bexp) map \<Rightarrow> destination list \<Rightarrow> efsm \<Rightarrow> (string, bexp) map \<Rightarrow> destination list \<Rightarrow> statename list \<Rightarrow> bool" 
  and compare :: "efsm \<Rightarrow> statename \<Rightarrow> (string, bexp) map \<Rightarrow> efsm \<Rightarrow> statename \<Rightarrow> (string, bexp) map \<Rightarrow> statename list \<Rightarrow> bool" 
  where
  "match_all _ _ [] _ _ _ _ = True" |
  "match_all e1 c1 (h#t) e2 c2 d2 closed = (
    case (find_match (snd h) d2) of
      None \<Rightarrow> False  |
      Some (s', _) \<Rightarrow> (compare e1 (fst h) c1 e2 s' c2 closed ) \<and> (match_all e1 c1 t e2 c2 d2 closed)
    )" |
 "compare  e1 s1 c1 e2 s2 c2 closed = (
    if ((find (\<lambda>x . x = s1) closed) \<noteq> None) then
      True
    else (match_all e1 c1 (all_outs e1 s1) e2 c2 (all_outs e2 s2) (s1#closed)
     ))"

definition simulates :: "efsm \<Rightarrow> efsm \<Rightarrow> bool" where
  "simulates e1 e2 = compare e1 (s0 e1) empty e2 (s0 e2) empty []"

end