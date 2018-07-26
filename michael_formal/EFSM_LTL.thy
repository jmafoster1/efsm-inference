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

abbreviation non_null :: property where
  "non_null s \<equiv> (statename (shd s) \<noteq> None)"

abbreviation null :: property where
  "null s \<equiv> (statename (shd s) = None)"

lemma null_forever [simp]: "s = make_full_observation e (Some (s0 e)) <> t \<Longrightarrow> null s \<Longrightarrow> nxt (alw null) s"
  by simp

abbreviation some_state :: "full_observation \<Rightarrow> bool" where
  "some_state s \<equiv> (\<exists>state. statename (shd s) = Some state)"

lemma non_null_equiv: "non_null = some_state"
  by simp

lemma start_some_state:  "s = make_full_observation e (Some (s0 e)) <> t \<Longrightarrow> some_state s"
  by simp

lemma self_eq:  "make_full_observation e (Some (s0 e)) <> t = make_full_observation e (Some (s0 e)) <> t"
  by simp


lemma some_until_none: "s = make_full_observation e (Some (s0 e)) <> t \<Longrightarrow> (some_state until null) s "
proof (coinduction)
  case UNTIL
  then show ?case
    by (smt UNTIL.coinduct non_null_equiv)
qed



end