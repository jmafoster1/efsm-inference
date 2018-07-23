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
  "read_0 (h##t) = (label h=''read'' \<longrightarrow> output h=[Str ''accessDenied''])"

fun login_attacker :: property where
  "login_attacker (h##t) = (event h = (''login'',  [Str ''attacker'']))"

fun login_user :: property where
  "login_user (h##t) = (event h = (''login'',  [Str ''user'']))"

fun non_null :: property where
  "non_null (h##t) = (statename h \<noteq> None)"

lemma "login_user (watch_filesystem i) \<Longrightarrow> shd i = (''login'', [Str ''user''])"
  by (metis login_user.elims(2) make_full_observation.simps(1) state.select_convs(3) stream.sel(1))

lemma login_user_first: "alw non_null (watch_filesystem i) \<Longrightarrow> (login_user (watch_filesystem i) = (shd i = (''login'', [Str ''user''])))"
  by (metis login_user.simps make_full_observation.simps(1) state.select_convs(3) stream.collapse)

      (* G(cfstate /= NULL_STATE)         =>  ((label=login AND ip_1_login_1=(user)) AND U(label/=logout, label=create))                             => F(G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout))  =>   U(label=read=>X(op_1_read_0=0), label=logout))) *)
lemma "alw non_null (watch_filesystem i) \<Longrightarrow> login_user (watch_filesystem i)         \<and> ((label_not_logout until label_create) (watch_filesystem i)) \<Longrightarrow> ev (alw ((login_attacker                      aand ev label_logout) impl (read_0 until label_logout))) (watch_filesystem i)"
  apply simp

end