theory EFSM_LTL
imports EFSM "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams" Filesystem
begin
type_synonym full_observation = "(statename option \<times> datastate \<times> event \<times> outputs) stream"
type_synonym property = "full_observation \<Rightarrow> bool"

fun ltl_step :: "efsm \<Rightarrow> statename option \<Rightarrow> datastate \<Rightarrow> event \<Rightarrow> (statename option \<times> outputs \<times> datastate)" where
"ltl_step _ None r _ = (None, [], r)" |
"ltl_step e (Some s) r (l, i) = (case (possible_steps e s r l i) of
    [(s',t)] \<Rightarrow> (Some s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)) |
    _ \<Rightarrow> (None, [], r)
  )"

primcorec make_full_observation :: "efsm \<Rightarrow> statename option \<Rightarrow> datastate \<Rightarrow> event stream \<Rightarrow> full_observation" where
  "make_full_observation e s d i = (let (s', o', d') = ltl_step e s d (shd i) in (s, d, (shd i), o')##(make_full_observation e s' d' (stl i)))"

abbreviation one_or_2 :: "full_observation \<Rightarrow> bool" where
  "one_or_2 s \<equiv> ((fst (shd s)) = Some 1 \<or> (fst (shd s)) = Some 2)"

abbreviation none :: "full_observation \<Rightarrow> bool" where
  "none s \<equiv> ((fst (shd s)) = None)"

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
  "label_not_logout ((s, d, (l, i), p)##t) = (l \<noteq> ''logout'')"

fun label_logout :: property where
  "label_logout ((s, d, (l, i), p)##t) = (l = ''logout'')"

fun label_create :: property where
  "label_create ((s, d, (l, i), p)##t) = (l = ''create'')"

fun read_0 :: property where
  "read_0 ((s, d, (l, i), p)##t) = (l=''read'' \<longrightarrow> p=[0])"

fun login_attacker :: property where
  "login_attacker ((s, d, (l, i), p)##t) = (l = ''read'' \<and> i = [1])"

fun login_user :: property where
  "login_user ((s, d, (l, i), p)##t) = (l = ''read'' \<and> i = [0])"

fun non_null :: property where
  "non_null ((s, d, (l, i), p)##t) = (s \<noteq> None)"

lemma "alw ((login_attacker aand ev label_logout) impl (read_0 until label_logout)) (make_full_observation filesystem (Some 1) <> i)"
  sorry (* This is false but is a part of the formula that we actually want *)

      (* G(cfstate /= NULL_STATE)         =>  ((label=login AND ip_1_login_1=(user)) AND U(label/=logout, label=create))                             => F(G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout))  =>   U(label=read=>X(op_1_read_0=0), label=logout))) *)
lemma "alw non_null (watch_filesystem i) \<Longrightarrow> login_user (watch_filesystem i)         \<and> ((label_not_logout until label_create) (watch_filesystem i)) \<Longrightarrow> ev (alw ((login_attacker                      aand ev label_logout) impl (read_0 until label_logout))) (watch_filesystem i)"
  sorry

end