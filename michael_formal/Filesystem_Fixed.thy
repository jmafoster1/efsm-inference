theory Filesystem_Fixed
imports Filesystem EFSM_LTL
begin

(* Takes a user ID and stores it in r1 *)
definition "write" :: "transition" where
"write \<equiv> \<lparr>
        Label = ''write'',
        Arity = 1,
        Guard = [(Eq (V (R 1)) (V (R 3)))], (* No guards *)
        Outputs = [],
        Updates = [ 
                    (R 1, (V (R 1))), (* Value of r1 remains unchanged *)
                    (R 2, (V (I 1))), (* Write the input to r2 *)
                    (R 3, (V (R 1)))  (* Store the writer in r3 *)
                  ]
      \<rparr>"

(* Create the file if it doesn't already exist *)
definition create :: "transition" where
"create \<equiv> \<lparr>
        Label = ''create'',
        Arity = 0,
        Guard = [(Null (R 3))],
        Outputs = [],
        Updates = [ 
                    (R 1, (V (R 1))),
                    (R 2, (V (R 2))),
                    (R 3, (V (R 1)))  (* Initialise the current user as the file owner *)
                  ]
      \<rparr>"

definition "write_fail" :: "transition" where
"write_fail \<equiv> \<lparr>
        Label = ''write'',
        Arity = 1,
        Guard = [(Ne (V (R 3)) (V (R 1)))],
        Outputs = [L (Str ''accessDenied'')],
        Updates = []
      \<rparr>"

definition filesystem :: "efsm" where
"filesystem \<equiv> \<lparr> 
          S = [1,2],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [login]
              else if (a,b) = (2,1) then [logout]
              else if (a,b) = (2,2) then [write, read_success, read_fail, write_fail, create]
              else []
         \<rparr>"

(* export_code filesystem in "Scala" *)

lemmas fs_simp = filesystem_def login_def logout_def write_def read_success_def read_fail_def write_fail_def create_def

lemma "observe_trace filesystem (s0 filesystem) <> [(''login'', [Str ''user'']), (''create'', []), (''write'', [Num 50]), (''read'', [])] = [[], [], [], [Num 50]]"
  by (simp add: fs_simp step_def)

(* step :: efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option *)
(* observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where *)

(* noChangeOwner: THEOREM filesystem |- G(cfstate /= NULL_STATE) => FORALL (owner : UID): G((label=write AND r_1=owner) => F(G((label=read AND r_1/=owner) => X(op_1_read_0 = accessDenied)))); *)

lemma r_equals_r [simp]: "<R 1:=user, R 2:=content, R 3:=owner> = (\<lambda>a. if a = R 3 then Some owner else if a = R 2 then Some content else if a = R 1 then Some user else <> a)"
  apply (rule ext)
  by simp

lemma read_2:  " r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 2 r ''read'' [] = Some (2, [Str ''accessDenied''], r)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

lemma logout_2:  " r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 2 r ''logout'' [] = Some (1, [], r)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

abbreviation one_or_2 :: "full_observation \<Rightarrow> bool" where
  "one_or_2 s \<equiv> ((statename (shd s)) = Some 1 \<or> (statename (shd s)) = Some 2)"

lemma one_or_2_some: "one_or_2 s \<Longrightarrow> some_state s"
  by auto

lemma "(s0 e) \<in> set (S e) \<Longrightarrow> (alw (\<lambda>s. statename (shd s) = Some a \<longrightarrow> a \<in> set (S e))) (make_full_observation e (Some (s0 e)) <> i)"
proof (coinduction)
  case alw
  then show ?case
    apply (rule_tac x="make_full_observation e (Some (s0 e)) <> i" in exI)
    apply safe
     apply simp
    sorry
  qed

lemma "some_state (make_full_observation Filesystem_Fixed.filesystem s r i ) = one_or_2 (make_full_observation Filesystem_Fixed.filesystem s r i )"
  apply (case_tac s)
   apply simp
  apply simp

lemma start_in_1: "one_or_2 ( make_full_observation Filesystem_Fixed.filesystem (Some 1) <> i )"
  by (simp add: filesystem_def)

lemma fs_some_until_null: "(some_state until null) (make_full_observation filesystem (Some (s0 filesystem)) <> i)"
  by (simp add: some_until_none)



(* G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout)) => U(label=read=>X(op_1_read_0=0), label=logout)) *)
abbreviation watch_filesystem :: "event stream \<Rightarrow> full_observation" where
  "watch_filesystem i \<equiv> (make_full_observation filesystem (Some 1) <> i)"

abbreviation label_not_logout :: property where
  "label_not_logout s \<equiv> (label (shd s) \<noteq> ''logout'')"

abbreviation label_logout :: property where
  "label_logout s \<equiv> (label (shd s) = ''logout'')"

abbreviation label_create :: property where
  "label_create s \<equiv> (label (shd s) = ''create'')"

abbreviation read_0 :: property where
  "read_0 s \<equiv> (label (shd s)=''read'' \<longrightarrow> output (shd s)=[Str ''accessDenied''])"

abbreviation login_attacker :: property where
  "login_attacker s \<equiv> (event (shd s) = (''login'',  [Str ''attacker'']))"

abbreviation login_user :: property where
  "login_user s \<equiv> (event (shd s) = (''login'',  [Str ''user'']))"

lemma "login_user (watch_filesystem i) \<Longrightarrow> shd i = (''login'', [Str ''user''])"
  by simp

lemma login_user_first: "alw non_null (watch_filesystem i) \<Longrightarrow> (login_user (watch_filesystem i) = (shd i = (''login'', [Str ''user''])))"
  by simp
      (* G(cfstate /= NULL_STATE)         =>  ((label=login AND ip_1_login_1=(user)) AND U(label/=logout, label=create))                              => F(G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout))  =>   U(label=read=>X(op_1_read_0=0), label=logout))) *)
lemma "alw non_null (watch_filesystem i) \<Longrightarrow> login_user (watch_filesystem i)         \<and> ((label_not_logout suntil label_create) (watch_filesystem i)) \<Longrightarrow> ev (alw ((login_attacker                      aand ev label_logout) impl (read_0 suntil label_logout))) (watch_filesystem i)"
  apply simp
  sorry

      (* G(cfstate /= NULL_STATE)  => ((label=login AND ip_1_login_1=(user)) AND U(label/=logout, label=create)) => F(G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout))  =>   U(label=read=>X(op_1_read_0=0), label=logout))) *)

lemma "((alw non_null) impl (login_user aand (label_not_logout until label_create))) impl (ev (alw ((login_attacker                      aand ev label_logout) impl (read_0 suntil label_logout))) (watch_filesystem i))"

end