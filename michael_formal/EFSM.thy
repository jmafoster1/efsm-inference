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

definition possible_transitions :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> inputs \<Rightarrow> statename list" where
  "possible_transitions e s r i = []"

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (outputs \<times> registers)" where
  "step e s r l i = ([], <>)" (*For each step, return the outputs and updated registers *)

primrec observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where
  "observe_trace _ _ _ [] = []" |
  "observe_trace e s r (h#t) = (outputs#(observe_trace e s updated t)) where
  (outputs, updated) = step e s r label inputs
  label = fst h
  inputs = snd h"






end