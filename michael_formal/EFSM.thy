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






end