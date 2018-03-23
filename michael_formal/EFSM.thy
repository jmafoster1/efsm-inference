theory EFSM
  imports types
begin

primrec apply_updates :: "(string \<times> aexp) list \<Rightarrow> state \<Rightarrow> registers \<Rightarrow> registers" where
  "apply_updates [] _ _ = <>" |
  "apply_updates (h#t) i r = join <(fst h) := (aval (snd h) (join i r))> (apply_updates t i r)"
declare apply_updates_def [simp]

primrec apply_outputs :: "(string \<times> aexp) list \<Rightarrow> state \<Rightarrow> registers \<Rightarrow> outputs" where
  "apply_outputs [] _ _ = []" |
  "apply_outputs (h#t) i r = (aval (snd h) (join i r))#(apply_outputs t i r)"
declare apply_outputs_def [simp]

primrec apply_guards :: "guard \<Rightarrow> state \<Rightarrow> registers \<Rightarrow> bool" where
  "apply_guards [] _ _ = True" |
  "apply_guards (h#t) i r =  ((bval h (join i r)) \<and> (apply_guards t i r))"
declare apply_guards_def [simp]

definition blank :: output_function where
  "blank = []"
declare blank_def [simp]

definition trueguard :: guard  where
  "trueguard = [(Bc True)]"
declare trueguard_def [simp]

definition no_updates :: update_function where
  "no_updates = []"
declare no_updates_def [simp]

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
end