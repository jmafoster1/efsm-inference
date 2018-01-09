theory EFSM
imports Main Expressions 
begin

type_synonym state = "nat"
type_synonym guard = "BExp"
type_synonym output_fun = "(data * inputs) \<Rightarrow> outputs"
type_synonym update = "(data * inputs) \<Rightarrow> data"

(* Produce complete vectors with the unassigned elements filled in Nil *)
definition output_vexp_to_fun :: "VExp => output_fun" where
"output_vexp_to_fun ve \<equiv> \<lambda> (d::data, i::inputs) . veval d i empty_outputs ve"

(* Produce a complete vector with unassigned elements unchanged *)
definition update_vexp_to_fun :: "VExp \<Rightarrow> update" where
"update_vexp_to_fun ve \<equiv> \<lambda> (d::data, i::inputs) . veval d i d ve"

type_synonym transition = "(guard * output_fun * update)"

type_synonym transition_matrix = "(state * state) \<Rightarrow> transition set"

(* An EFSM is defined by its transition matrix, an initial state, and an initial data state *)
type_synonym EFSM = "(transition_matrix * state * data)"

fun is_possible :: "transition => data => inputs => bool" where
"is_possible (g,_,_) d i = beval d i g"

fun all_possible :: "transition_matrix => state => data => inputs => (state * transition) set" where
"all_possible M s d i = {(s',t) . t \<in> (M (s,s')) \<and> is_possible t d i}"

(* The Transition matrix is deterministic at a particular state for a particular set of 
  data in inputs if there is either one transition or none *)
fun deterministic :: "transition_matrix \<Rightarrow> state \<Rightarrow> data \<Rightarrow> inputs \<Rightarrow> bool" where
"deterministic M s d i = (card (all_possible M s d i) \<le> 1)"

datatype maybe_action = Stop | Do "(state * data * outputs)" | NonDet

fun apply_inputs :: "transition_matrix \<Rightarrow> state \<Rightarrow> data \<Rightarrow> inputs \<Rightarrow> maybe_action" where
"apply_inputs M s d i = 
  (let pos = all_possible M s d i in
    if card pos = 0 then Stop
    else if card pos > 1 then NonDet
    else (let (s',(_,out,upd)) = SOME a . a \<in> pos in Do (s', upd (d,i), out (d,i)))
  )"

end