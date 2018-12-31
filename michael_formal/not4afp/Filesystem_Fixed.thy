theory Filesystem_Fixed
imports Filesystem EFSM_LTL
begin

text_raw{*\snip{write}{1}{2}{%*}
definition "write" :: "transition" where
"write \<equiv> \<lparr>
        Label = ''write'',
        Arity = 1,
        Guard = [gexp.Eq (V (R 1)) (V (R 3))], \<comment>\<open> No guards \<close>
        Outputs = [],
        Updates = [
                    (R 1, (V (R 1))), \<comment>\<open> Value of r1 remains unchanged \<close>
                    (R 2, (V (I 1))), \<comment>\<open> Write the input to r2 \<close>
                    (R 3, (V (R 1)))  \<comment>\<open> Store the writer in r3 \<close>
                  ]
      \<rparr>"
text_raw{*}%endsnip*}

\<comment>\<open> Create the file if it doesn't already exist \<close>
definition create :: "transition" where
"create \<equiv> \<lparr>
        Label = ''create'',
        Arity = 0,
        Guard = [(Null (R 3))],
        Outputs = [],
        Updates = [
                    (R 1, (V (R 1))),
                    (R 2, (V (R 2))),
                    (R 3, (V (R 1)))  \<comment>\<open> Initialise the current user as the file owner \<close>
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
definition filesystem :: "transition_matrix" where
"filesystem \<equiv> {|
              ((0,1), login),
              ((1,0), logout),
              ((1,1), write),
              ((1,1), read_success),
              ((1,1), read_fail),
              ((1,1), write_fail),
              ((1,1), create)
         |}"
text_raw{*}%endsnip*}

\<comment>\<open> export_code filesystem in "Scala" \<close>

declare One_nat_def [simp del]

lemmas fs_simp = filesystem_def login_def logout_def write_def read_success_def read_fail_def write_fail_def create_def

lemma possible_steps_0: "possible_steps Filesystem_Fixed.filesystem 0 r ''login'' [u] = {|(1, login)|}"
  apply (simp add: possible_steps_def fs_simp)
  by force

lemma possible_steps_1_create: "possible_steps filesystem 1 <R 1 := Str ''user''> ''create'' [] = {|(1, create)|}"
  apply (simp add: possible_steps_def fs_simp)
  by force

lemma possible_steps_1_write:  "possible_steps Filesystem_Fixed.filesystem 1 <R 1 := Str ''user'', R 3 := Str ''user''> ''write'' [Num 50] = {|(1, write)|}"
  apply (simp add: possible_steps_def fs_simp)
  by force

lemma possible_steps_1_read: "possible_steps Filesystem_Fixed.filesystem 1 <R 1 := u, R 2 := c, R 3 := u> ''read'' [] = {|(1, read_success)|}"
  apply (simp add: possible_steps_def fs_simp)
  by force

lemma "observe_trace filesystem 0 <> [(''login'', [Str ''user'']), (''create'', []), (''write'', [Num 50]), (''read'', [])] = [[], [], [], [Some (Num 50)]]"
proof-
  have updates_login: "(EFSM.apply_updates (Updates login)
          (case_vname (\<lambda>n. if n = 1 then Some (Str ''user'') else input2state [] (1 + 1) (I n)) Map.empty) Map.empty) = <R 1 := Str ''user''>"
    apply (rule ext)
    by (simp add: login_def)
  have updates_create: "(EFSM.apply_updates (Updates create) (case_vname Map.empty (\<lambda>n. if n = 1 then Some (Str ''user'') else None))
          <R 1 := Str ''user''>) = <R 1 := Str ''user'', R 3 := Str ''user''>"
    apply (rule ext)
    by (simp add: create_def)
  have updates_write: " (EFSM.apply_updates (Updates Filesystem_Fixed.write)
          (case_vname (\<lambda>n. if n = 1 then Some (Num 50) else input2state [] (1 + 1) (I n))
            (\<lambda>n. if n = 3 then Some (Str ''user'') else <R 1 := Str ''user''> (R n)))
          <R 1 := Str ''user'', R 3 := Str ''user''>) = <R 1 := Str ''user'', R 2 := Num 50, R 3 := Str ''user''>"
    apply (rule ext)
    by (simp add: write_def)
  show ?thesis
    unfolding observe_trace_def observe_all_def step_def
    apply (simp add: possible_steps_0 updates_login)
    apply (simp add: possible_steps_1_create updates_create)
    apply (simp add: possible_steps_1_write)
    apply (simp only: updates_write possible_steps_1_read)
    by (simp add: fs_simp)
qed

\<comment>\<open> step :: efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option \<close>
\<comment>\<open> observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where \<close>

\<comment>\<open> noChangeOwner: THEOREM filesystem |- G(cfstate /= NULL_STATE) => FORALL (owner : UID): G((label=write AND r_1=owner) => F(G((label=read AND r_1/=owner) => X(op_1_read_0 = accessDenied)))); \<close>

lemma r_equals_r [simp]: "<R 1:=user, R 2:=content, R 3:=owner> = (\<lambda>a. if a = R 3 then Some owner else if a = R 2 then Some content else if a = R 1 then Some user else <> a)"
  apply (rule ext)
  by simp

lemma possible_steps_1_read_fail: "r (R 3) = Some owner \<and> r (R 1) = Some user \<and> owner \<noteq> user \<Longrightarrow> possible_steps Filesystem_Fixed.filesystem 1 r ''read'' [] = {|(1, read_fail)|}"
  apply (simp add: possible_steps_def fs_simp)
  by force

lemma read_2:  " r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 1 r ''read'' [] = Some (read_fail, 1, [Some (Str ''accessDenied'')], r)"
  apply (simp add: step_def possible_steps_1_read_fail)
  apply (simp add: read_fail_def)
  apply (rule ext)
  by simp

lemma possible_steps_1_logout:  "possible_steps Filesystem_Fixed.filesystem 1 r ''logout'' [] = {|(0, logout)|}"
  apply (simp add: possible_steps_def fs_simp)
  by force

lemma logout_2:  "step filesystem 1 r ''logout'' [] = Some (logout, 0, [], r)"
  unfolding step_def
  apply (simp add: possible_steps_1_logout)
  apply (simp add: logout_def)
  apply (rule ext)
  by simp

abbreviation one_or_2 :: "full_observation \<Rightarrow> bool" where
  "one_or_2 s \<equiv> ((statename (shd s)) = Some 0 \<or> (statename (shd s)) = Some 1)"

lemma one_or_2_some: "one_or_2 s \<Longrightarrow> some_state s"
  by auto

lemma filesystem_states: "S filesystem = {|0, 1|}"
  apply (simp add: fs_simp S_def)
  by auto

lemma states_1_2: "s = Some s' \<Longrightarrow> s' |\<in>| S filesystem \<Longrightarrow> some_state (make_full_observation Filesystem_Fixed.filesystem s r i ) = one_or_2 (make_full_observation Filesystem_Fixed.filesystem s r i )"
  by (simp add: filesystem_states)

lemma start_in_1: "one_or_2 ( make_full_observation Filesystem_Fixed.filesystem (Some 0) <> i )"
  by (simp add: filesystem_def)

lemma fs_some_until_null: "(some_state until null) (make_full_observation filesystem (Some 0) <> i)"
  by (simp add: some_until_none)

abbreviation label_not_logout :: "property" where
  "label_not_logout s \<equiv> (label (shd s) \<noteq> ''logout'')"

abbreviation label_logout :: "property" where
  "label_logout s \<equiv> (label (shd s) = ''logout'')"

abbreviation label_create :: "property" where
  "label_create s \<equiv> (label (shd s) = ''create'')"

abbreviation read_0 :: "property" where
  "read_0 s \<equiv> (label (shd s)=''read'' \<longrightarrow> output (shd s)=[Some (Str ''accessDenied'')])"

abbreviation login_attacker :: "property" where
  "login_attacker s \<equiv> (event (shd s) = (''login'',  [Str ''attacker'']))"

abbreviation login_user :: "property" where
  "login_user s \<equiv> (event (shd s) = (''login'',  [Str ''user'']))"

lemma "login_user (watch filesystem i) \<Longrightarrow> shd i = (''login'', [Str ''user''])"
  by simp

lemma logout_label:  "t = logout \<Longrightarrow> Label t = ''logout''"
  by (simp add: logout_def)

lemma create_label:  "t = create \<Longrightarrow> Label t = ''create''"
  by (simp add: create_def)

lemma every_event_step: "\<forall>s r.  s |\<in>| S filesystem \<longrightarrow> (\<exists>e. fst (ltl_step filesystem (Some s) r e) \<noteq> None)"
  apply safe
  apply (simp only: "filesystem_states")
  apply (case_tac "s = 0")
   apply simp
   apply (rule_tac x="''login''" in exI)
   apply (rule_tac x="[x]" in exI)
   apply (simp add: possible_steps_0)
  apply simp
  apply (rule_tac x="''logout''" in exI)
  apply (rule_tac x="[]" in exI)
  by (simp add: possible_steps_1_logout)

lemma alw_equiv: "alw p s = ((p s) \<and> alw p (stl s))"
  using alw.intros by auto

text_raw{*\snip{userdetails}{1}{2}{%*}
lemma user_details_stored_in_r1: "((\<lambda>s. (event (shd s) = (''login'',  [u]))) impl (nxt (\<lambda>s. datastate (shd s) (R 1) = Some (u)))) (watch filesystem i)"
  proof (cases u)
    case (Num x1)
    then show ?thesis
      by (simp add: possible_steps_0 login_def)
  next
    case (Str x2)
    then show ?thesis
      by (simp add: possible_steps_0 login_def)
  qed
text_raw{*}%endsnip*}

\<comment>\<open>lemma "((\<lambda>s. (event (shd s) = (''login'',  [u]))) impl ((\<lambda>s. datastate (shd s) (R 1) = Some (u)) suntil (\<lambda>s. label (shd s) = ''logout''))) (watch filesystem i)"\<close>

\<comment>\<open>lemma globally_user_details_stored_in_r1: "alw (non_null impl ((\<lambda>s. (event (shd s) = (''login'',  [Str ''user'']))) impl (nxt (\<lambda>s. datastate (shd s) (R 1) = Some (Str ''user''))))) (watch filesystem i)"
proof (coinduction)
  case alw
  then show ?case
    
qed\<close>

lemma login_user_first: "alw non_null (watch filesystem i) \<Longrightarrow> (login_user (watch filesystem i) = (shd i = (''login'', [Str ''user''])))"
  by simp

      \<comment>\<open> G(cfstate /= NULL_STATE)  => ((label=login AND ip_1_login_1=(user)) AND U(label/=logout, label=create)) => F(G(((label=login AND ip_1_login_1=(attacker)) AND F(label=logout))  =>   U(label=read=>X(op_1_read_0=0), label=logout))) \<close>
\<comment>\<open>lemma "(((alw non_null) impl (login_user aand (label_not_logout until label_create))) impl (ev (alw ((login_attacker aand ev label_logout) impl (read_0 suntil label_logout))))) (watch filesystem i)"
  apply simp \<close>

end