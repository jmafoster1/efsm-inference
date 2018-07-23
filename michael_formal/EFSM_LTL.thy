theory EFSM_LTL
imports EFSM "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams" Filesystem
begin

record state =
  statename :: "statename option"
  datastate :: datastate
  event :: event
  "output" :: outputs

type_synonym full_observation = "state stream"
type_synonym property = "full_observation \<Rightarrow> bool"

abbreviation label :: "state \<Rightarrow> string" where
  "label s \<equiv> fst (event s)"

abbreviation inputs :: "state \<Rightarrow> value list" where
  "inputs s \<equiv> snd (event s)"

fun ltl_step :: "efsm \<Rightarrow> statename option \<Rightarrow> datastate \<Rightarrow> event \<Rightarrow> (statename option \<times> outputs \<times> datastate)" where
"ltl_step _ None r _ = (None, [], r)" |
"ltl_step e (Some s) r (l, i) = (case (possible_steps e s r l i) of
    [(s',t)] \<Rightarrow> (Some s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)) |
    _ \<Rightarrow> (None, [], r)
  )"

primcorec make_full_observation :: "efsm \<Rightarrow> statename option \<Rightarrow> datastate \<Rightarrow> event stream \<Rightarrow> full_observation" where
  "make_full_observation e s d i = (let (s', o', d') = ltl_step e s d (shd i) in \<lparr>statename = s, datastate = d, event=(shd i), output = o'\<rparr>##(make_full_observation e s' d' (stl i)))"

end