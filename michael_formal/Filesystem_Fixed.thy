theory Filesystem_Fixed
imports Filesystem EFSM_LTL
begin

text_raw{*\snip{write}{1}{2}{%*}
definition "write" :: "transition" where
"write \<equiv> \<lparr>
        Label = ''write'',
        Arity = 1,
        Guard = [((V (R 1)) = (V (R 3)))], (* No guards *)
        Outputs = [],
        Updates = [
                    (R 1, (V (R 1))), (* Value of r1 remains unchanged *)
                    (R 2, (V (I 1))), (* Write the input to r2 *)
                    (R 3, (V (R 1)))  (* Store the writer in r3 *)
                  ]
      \<rparr>"
text_raw{*}%endsnip*}

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

lemma arity_write_fail: "Arity write_fail = 1"
  by (simp add: write_fail_def)

lemma guard_write_fail: "Guard write_fail = [(Ne (V (R 3)) (V (R 1)))]"
  by (simp add: write_fail_def)

text_raw{*\snip{filesystem}{1}{2}{%*}
definition filesystem :: "statename efsm" where
"filesystem \<equiv> \<lparr>
          s0 = q1,
          T = \<lambda> (a,b) .
              if (a,b) = (q1,q2) then {login}
              else if (a,b) = (q2,q1) then {logout}
              else if (a,b) = (q2,q2) then {write, read_success, read_fail, write_fail, create}
              else {}
         \<rparr>"
text_raw{*}%endsnip*}

lemma s0_filesystem: "s0 filesystem = q1"
  by (simp add: filesystem_def)

(* export_code filesystem in "Scala" *)

lemmas fs_simp = filesystem_def login_def logout_def write_def read_success_def read_fail_def write_fail_def create_def

lemma label_login_q2: "Label t = ''login'' \<and> t \<in> T filesystem (q1, s') \<Longrightarrow> t = login \<and> s' = q2"
  apply (simp add: filesystem_def)
  apply (cases s')
   apply simp
  by simp

lemma possible_steps_q1: "possible_steps Filesystem_Fixed.filesystem q1 r ''login'' [u] = {(q2, login)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_login_q2)
      apply (simp add: label_login_q2)
     apply (simp add: login_def)
    apply (simp add: filesystem_def)
   apply (simp add: login_def)
  by (simp add: login_def)

lemma apply_updates_login [simp]: "(apply_updates (Updates login) (case_vname (\<lambda>n. if n = 1 then Some u else index2state [] (1 + 1) (I n)) Map.empty) Map.empty) = <R 1 := u>"
  apply (rule ext)
  by (simp add: login_def)

lemma label_create_q2: " Label b = ''create'' \<Longrightarrow> b \<in> T Filesystem_Fixed.filesystem (q2, a) \<Longrightarrow> b = create \<and> a = q2"
  apply (simp add: filesystem_def)
  apply (cases a)
   apply (simp add: logout_def)
  apply (simp add: fs_simp)
  by auto

lemma possible_steps_q2_create: "possible_steps filesystem q2 <R 1 := Str ''user''> ''create'' [] = {(q2, create)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_create_q2)
      apply (simp add: label_create_q2)
     apply (simp add: create_def)
    apply (simp add: filesystem_def)
  by (simp_all add: create_def)

lemma apply_updates_create [simp]: "(apply_updates (Updates create) (case_vname Map.empty (\<lambda>n. if n = 1 then Some u else None)) <R 1 := Str ''user''>) = <R 1 := u, R 3 := u>"
  apply (rule ext)
  by (simp add: create_def)

lemma label_write_q2: "Label t = ''write'' \<and> t \<in> T filesystem (q2, s') \<Longrightarrow> (t = write \<or> t = write_fail) \<and> s' = q2"
  apply (simp add: filesystem_def)
  apply (cases s')
   apply (simp add: logout_def)
   apply auto[1]
  apply (simp add: fs_simp)
  by auto

lemma possible_steps_q2_write:  "possible_steps Filesystem_Fixed.filesystem q2 <R 1 := Str ''user'', R 3 := Str ''user''> ''write'' [Num 50] = {(q2, write)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_write_q2)
      apply (case_tac "b = write")
       apply simp
      apply (case_tac "b = write_fail")
       apply (simp add: arity_write_fail guard_write_fail)
      using label_write_q2 apply blast
     apply (simp add: write_def)
    apply (simp add: filesystem_def)
      by (simp_all add: write_def)

lemma apply_updates_write : "(apply_updates (Updates Filesystem_Fixed.write)
          (case_vname (\<lambda>n. if n = 1 then Some c else index2state [] (1 + 1) (I n)) (\<lambda>n. if n = 3 then Some u else <R 1 := u> (R n)))
          <R 1 := u, R 3 := u>) = < R 1 := u, R 2 := c, R 3 := u>"
  apply (rule ext)
  by (simp add: write_def)

lemma label_read_q2: "b \<in> T filesystem (q2, a) \<Longrightarrow> Label b = ''read'' \<Longrightarrow> a = q2 \<and> (b = read_success \<or> b = read_fail)"
  apply (simp add: filesystem_def)
  apply (cases a)
   apply (simp add: logout_def)
  apply safe
  apply simp
  apply (simp add: fs_simp)
  by auto

lemma possible_steps_q2_read: "possible_steps Filesystem_Fixed.filesystem q2 <R 1 := u, R 2 := c, R 3 := u> ''read'' [] = {(q2, read_success)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_read_q2)
      apply (simp add: label_read_q2)
      apply (case_tac "b = read_success")
       apply simp
      apply (case_tac "b = read_fail")
       apply simp
       apply (simp add: read_fail_def)
       using label_read_q2 apply blast
          apply (simp add: read_success_def)
         apply (simp add: filesystem_def)
       by (simp_all add: read_success_def)

lemma "observe_trace filesystem (s0 filesystem) <> [(''login'', [Str ''user'']), (''create'', []), (''write'', [Num 50]), (''read'', [])] = [[], [], [], [Num 50]]"
  apply (simp add: possible_steps_q1 possible_steps_q2_create possible_steps_q2_write s0_filesystem del: One_nat_def)
  apply (simp only: apply_updates_write possible_steps_q2_read)
  by (simp add: fs_simp)

(* step :: efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option *)
(* observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where *)

(* noChangeOwner: THEOREM filesystem |- G(cfstate /= NULL_STATE) => FORALL (owner : UID): G((label=write AND r_1=owner) => F(G((label=read AND r_1/=owner) => X(op_1_read_0 = accessDenied)))); *)

lemma r_equals_r [simp]: "<R 1:=user, R 2:=content, R 3:=owner> = (\<lambda>a. if a = R 3 then Some owner else if a = R 2 then Some content else if a = R 1 then Some user else <> a)"
  apply (rule ext)
  by simp

lemma possible_steps_q2_read_fail: "owner \<noteq> user \<Longrightarrow> possible_steps Filesystem_Fixed.filesystem q2 <R (Suc 0) := user, R 2 := content, R 3 := owner> ''read'' [] = {(q2, read_fail)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_read_q2)
      apply (simp add: label_read_q2)
      apply (case_tac "b = read_fail")
       apply simp
      apply (case_tac "b = read_success")
       apply (simp add: read_success_def)
       using label_read_q2 apply blast
     apply (simp add: read_fail_def)
    apply (simp add: filesystem_def)
  by (simp_all add: read_fail_def)

lemma read_2:  " r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem q2 r ''read'' [] = Some (q2, [Str ''accessDenied''], r)"
  apply (simp add: possible_steps_q2_read_fail read_fail_def)
  apply (rule ext)
  by simp

lemma label_logout_q1: "Label b = ''logout'' \<Longrightarrow> b \<in> T Filesystem_Fixed.filesystem (q2, a) \<Longrightarrow> b = logout \<and> a = q1"
  apply (simp add: filesystem_def)
  apply (cases a)
   apply simp
  apply (simp add: fs_simp)
  by auto

lemma possible_steps_q2_logout:  "possible_steps Filesystem_Fixed.filesystem q2 r ''logout'' [] = {(q1, logout)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_logout_q1)
      apply (simp add: label_logout_q1)
     prefer 2
  apply (simp add: filesystem_def)
  by (simp_all add: logout_def)

lemma logout_2:  "step filesystem q2 r ''logout'' [] = Some (q1, [], r)"
  apply (simp add: possible_steps_q2_logout logout_def)
  apply (rule ext)
  by simp

abbreviation one_or_2 :: "statename full_observation \<Rightarrow> bool" where
  "one_or_2 s \<equiv> ((statename (shd s)) = Some q1 \<or> (statename (shd s)) = Some q2)"

lemma one_or_2_some: "one_or_2 s \<Longrightarrow> some_state s"
  by auto

lemma filesystem_states: "S filesystem = {q1, q2}"
  apply (simp add: fs_simp S_def)
  by auto

lemma states_1_2: "some_state (make_full_observation Filesystem_Fixed.filesystem s r i ) = one_or_2 (make_full_observation Filesystem_Fixed.filesystem s r i )"
  apply (case_tac s)
   apply simp
  apply simp
  using statename.exhaust by blast

lemma start_in_1: "one_or_2 ( make_full_observation Filesystem_Fixed.filesystem (Some q1) <> i )"
  by (simp add: filesystem_def)

lemma fs_some_until_null: "(some_state until null) (make_full_observation filesystem (Some (s0 filesystem)) <> i)"
  by (simp add: some_until_none)

abbreviation label_not_logout :: "statename property" where
  "label_not_logout s \<equiv> (label (shd s) \<noteq> ''logout'')"

abbreviation label_logout :: "statename property" where
  "label_logout s \<equiv> (label (shd s) = ''logout'')"

abbreviation label_create :: "statename property" where
  "label_create s \<equiv> (label (shd s) = ''create'')"

abbreviation read_0 :: "statename property" where
  "read_0 s \<equiv> (label (shd s)=''read'' \<longrightarrow> output (shd s)=[Str ''accessDenied''])"

abbreviation login_attacker :: "statename property" where
  "login_attacker s \<equiv> (event (shd s) = (''login'',  [Str ''attacker'']))"

abbreviation login_user :: "statename property" where
  "login_user s \<equiv> (event (shd s) = (''login'',  [Str ''user'']))"

lemma "login_user (watch filesystem i) \<Longrightarrow> shd i = (''login'', [Str ''user''])"
  by simp

lemma possible_steps_q1_select: "(possible_steps filesystem q1 r ''login'' [Str ''user'']) = {(q2, login)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: filesystem_def)
  using prod.inject apply fastforce
       apply (simp add: filesystem_def)
      apply (metis empty_iff prod.inject singletonD)
  by (simp_all add: filesystem_def login_def)

lemma logout_label:  "t = logout \<Longrightarrow> Label t = ''logout''"
  by (simp add: logout_def)

lemma create_label:  "t = create \<Longrightarrow> Label t = ''create''"
  by (simp add: create_def)

lemma r2_none_read_fail: "r (R 2) = None \<Longrightarrow> Label t = ''read'' \<and> t \<in> T Filesystem_Fixed.filesystem (q2, s') \<and> apply_guards (Guard t) (join_ir [] r) \<Longrightarrow> t = read_fail \<and> s' = q2"
  apply (simp add: filesystem_def)
  apply (cases s')
   apply simp
  using logout_label apply fastforce
  apply simp
  apply (case_tac "t = write")
  apply (simp add: write_def)
  apply (case_tac "t = read_success")
   apply (simp add: read_success_def)
  apply (case_tac "t = read_fail")
   apply simp
  apply (case_tac "t = write_fail")
   apply (simp add: write_fail_def)
  using create_label by force

lemma every_event_step: "\<forall>s r. \<exists>e. fst (ltl_step filesystem (Some s) r e) \<noteq> None"
  apply (rule allI, rule allI)
  apply (case_tac s)
   apply (rule_tac x="(''login'', [Str ''user''])" in exI)
   apply simp
   apply (simp add: possible_steps_q1_select)
  apply (rule_tac x="(''read'', [])" in exI)
  apply simp
  apply safe
   apply (rule_tac x=q2 in exI)
   apply (case_tac "the_elem (possible_steps Filesystem_Fixed.filesystem q2 r ''read'' [])")
   apply simp
   apply (simp add: is_singleton_def)
   apply (simp add: possible_steps_def)
   apply safe[1]
   apply (simp add: label_read_q2)
  using label_read_q2 apply blast
  apply (simp add: is_singleton_def)
  apply (rule_tac x=q2 in exI)
  apply (simp add: possible_steps_def)
  apply (case_tac "r (R 2) = None")
   apply (rule_tac x=read_fail in exI)
   apply safe[1]
        apply (simp add: label_read_q2)
  using r2_none_read_fail apply blast
      apply (simp add: read_fail_def)
     apply (simp add: filesystem_def)
  apply (simp add: read_fail_def)
   apply (simp add: read_fail_def)
  apply (case_tac "r (R 1) = r (R 3)")
   apply (simp del: One_nat_def)
   apply (rule_tac x=read_success in exI)
   apply safe[1]
  using label_read_q2 apply blast
       apply simp
       apply (case_tac a)
        apply (simp add: filesystem_def logout_def read_success_def)
       apply (simp add: filesystem_def)
       apply (case_tac "b = write")
        apply (simp add: write_def)
       apply (case_tac "b = read_success")
        apply simp
       apply (case_tac "b = read_fail")
        apply (simp add: read_fail_def)
       apply (case_tac "b = write_fail")
        apply (simp add: write_fail_def)
       apply (simp add: create_def)
      apply (simp add: read_success_def)
     apply (simp add: filesystem_def)
    apply (simp add: read_success_def)
   apply (simp add: read_success_def)
  apply (rule_tac x=read_fail in exI)
  apply safe
       apply (simp add: label_read_q2)
      apply (case_tac a)
       apply (simp add: filesystem_def logout_def)
      apply (simp add: filesystem_def)
      apply (case_tac "b = write")
       apply (simp add: write_def)
      apply (case_tac "b = read_success")
       apply (simp add: read_success_def read_fail_def)
      apply (case_tac "b = read_fail")
       apply simp
      apply (case_tac "b = write_fail")
       apply (simp add: write_fail_def)
      apply (simp add: create_def)
     apply (simp add: read_fail_def)
    apply (simp add: filesystem_def)
  by (simp_all add: read_fail_def)

lemma alw_equiv: "alw p s = ((p s) \<and> alw p (stl s))"
  using alw.intros by auto

text_raw{*\snip{userdetails}{1}{2}{%*}
lemma user_details_stored_in_r1: "((\<lambda>s. (event (shd s) = (''login'',  [u]))) impl (nxt (\<lambda>s. datastate (shd s) (R 1) = Some (u)))) (watch filesystem i)"
  proof (cases u)
    case (Num x1)
    then show ?thesis
      by (simp add: possible_steps_q1 login_def s0_filesystem)
  next
    case (Str x2)
    then show ?thesis
      by (simp add: possible_steps_q1 login_def s0_filesystem)
  qed
text_raw{*}%endsnip*}

(*lemma "((\<lambda>s. (event (shd s) = (''login'',  [u]))) impl ((\<lambda>s. datastate (shd s) (R 1) = Some (u)) suntil (\<lambda>s. label (shd s) = ''logout''))) (watch filesystem i)"
  sorry*)

(*lemma globally_user_details_stored_in_r1: "alw (non_null impl ((\<lambda>s. (event (shd s) = (''login'',  [Str ''user'']))) impl (nxt (\<lambda>s. datastate (shd s) (R 1) = Some (Str ''user''))))) (watch filesystem i)"
proof (coinduction)
  case alw
  then show ?case
    sorry
qed*)

lemma login_user_first: "alw non_null (watch filesystem i) \<Longrightarrow> (login_user (watch filesystem i) = (shd i = (''login'', [Str ''user''])))"
  by simp

      (* G(cfstate /= NULL_STATE)  => ((label=login AND ip_1_login_1=(user)) AND U(label/=logout, label=create)) => F(G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout))  =>   U(label=read=>X(op_1_read_0=0), label=logout))) *)
(*lemma "(((alw non_null) impl (login_user aand (label_not_logout until label_create))) impl (ev (alw ((login_attacker aand ev label_logout) impl (read_0 suntil label_logout))))) (watch filesystem i)"
  apply simp
  sorry*)

end
