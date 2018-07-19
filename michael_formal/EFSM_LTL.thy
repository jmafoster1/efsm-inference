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

abbreviation inputs :: "state \<Rightarrow> int list" where
  "inputs s \<equiv> snd (event s)"

fun ltl_step :: "efsm \<Rightarrow> statename option \<Rightarrow> datastate \<Rightarrow> event \<Rightarrow> (statename option \<times> outputs \<times> datastate)" where
"ltl_step _ None r _ = (None, [], r)" |
"ltl_step e (Some s) r (l, i) = (case (possible_steps e s r l i) of
    [(s',t)] \<Rightarrow> (Some s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)) |
    _ \<Rightarrow> (None, [], r)
  )"

primcorec make_full_observation :: "efsm \<Rightarrow> statename option \<Rightarrow> datastate \<Rightarrow> event stream \<Rightarrow> full_observation" where
  "make_full_observation e s d i = (let (s', o', d') = ltl_step e s d (shd i) in \<lparr>statename = s, datastate = d, event=(shd i), output = o'\<rparr>##(make_full_observation e s' d' (stl i)))"

abbreviation one_or_2 :: "full_observation \<Rightarrow> bool" where
  "one_or_2 s \<equiv> ((statename (shd s)) = Some 1 \<or> (statename (shd s)) = Some 2)"

abbreviation none :: "full_observation \<Rightarrow> bool" where
  "none s \<equiv> ((statename (shd s)) = None)"

lemma "UNTIL one_or_2 none (make_full_observation filesystem (Some 1) <> i)"
proof (coinduction)
  case UNTIL
  then show ?case
    apply simp
    apply safe
    sorry
qed

(* G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout)) => U(label=read=>X(op_1_read_0=0), label=logout)) *)
abbreviation watch_filesystem :: "event stream \<Rightarrow> full_observation" where
  "watch_filesystem i \<equiv> (make_full_observation filesystem (Some 1) <> i)"

fun label_not_logout :: property where
  "label_not_logout (h##t) = (label h \<noteq> ''logout'')"

fun label_logout :: property where
  "label_logout (h##t) = (label h = ''logout'')"

fun label_create :: property where
  "label_create (h##t) = (label h = ''create'')"

fun read_0 :: property where
  "read_0 (h##t) = (label h=''read'' \<longrightarrow> output h=[0])"

fun login_attacker :: property where
  "login_attacker (h##t) = (event h = (''login'',  [1]))"

fun login_user :: property where
  "login_user (h##t) = (event h = (''login'',  [0]))"

fun non_null :: property where
  "non_null (h##t) = (statename h \<noteq> None)"

lemma "login_user (watch_filesystem i) \<Longrightarrow> shd i = (''login'', [0])"
  by (metis login_user.elims(2) make_full_observation.simps(1) state.select_convs(3) stream.sel(1))

lemma login_user_first: "alw non_null (watch_filesystem i) \<Longrightarrow> (login_user (watch_filesystem i) = (shd i = (''login'', [0])))"
  by (metis login_user.simps make_full_observation.simps(1) state.select_convs(3) stream.collapse)
      (* G(cfstate /= NULL_STATE)         =>  ((label=login AND ip_1_login_1=(user)) AND U(label/=logout, label=create))                             => F(G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout))  =>   U(label=read=>X(op_1_read_0=0), label=logout))) *)
lemma "alw non_null (watch_filesystem i) \<Longrightarrow> login_user (watch_filesystem i)         \<and> ((label_not_logout until label_create) (watch_filesystem i)) \<Longrightarrow> ev (alw ((login_attacker                      aand ev label_logout) impl (read_0 until label_logout))) (watch_filesystem i)"
  apply simp
end