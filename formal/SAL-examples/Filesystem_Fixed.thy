theory Filesystem_Fixed
imports Filesystem EFSM_LTL
begin

text_raw{*\snip{write}{1}{2}{%*}
definition "write" :: "transition" where
"write \<equiv> \<lparr>
        Label = (STR ''write''),
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
        Label = (STR ''create''),
        Arity = 0,
        Guard = [(Null (V (R 3)))],
        Outputs = [],
        Updates = [
                    (R 1, (V (R 1))),
                    (R 2, (V (R 2))),
                    (R 3, (V (R 1)))  \<comment>\<open> Initialise the current user as the file owner \<close>
                  ]
      \<rparr>"

definition "write_fail" :: "transition" where
"write_fail \<equiv> \<lparr>
        Label = (STR ''write''),
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

lemma possible_steps_0: "possible_steps Filesystem_Fixed.filesystem 0 r (STR ''login'') [u] = {|(1, login)|}"
  apply (simp add: possible_steps_def fs_simp)
  by force

lemma possible_steps_1_create: "possible_steps filesystem 1 <R 1 := Str ''user''> (STR ''create'') [] = {|(1, create)|}"
proof-
  have filter: "ffilter
     (\<lambda>((origin, dest), t).
         origin = 1 \<and>
         Label t = STR ''create'' \<and>
         Arity t = 0 \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n) | R n \<Rightarrow> <R 1 := EFSM.Str ''user''> (R n)))
     Filesystem_Fixed.filesystem =
    {|((1, 1), create)|}"
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)
    apply safe
    by (simp_all add: fs_simp gval.simps ValueEq_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma possible_steps_1_write:  "possible_steps Filesystem_Fixed.filesystem 1 <R 1 := Str ''user'', R 3 := Str ''user''> (STR ''write'') [Num 50] = {|(1, write)|}"
proof-
  have filter: " ffilter
     (\<lambda>((origin, dest), t).
         origin = 1 \<and>
         Label t = STR ''write'' \<and>
         Suc 0 = Arity t \<and>
         apply_guards (Guard t)
          (\<lambda>x. case x of I n \<Rightarrow> input2state [Num 50] 1 (I n) | R n \<Rightarrow> <R 1 := EFSM.Str ''user'', R 3 := EFSM.Str ''user''> (R n)))
     Filesystem_Fixed.filesystem =
    {|((1, 1), Filesystem_Fixed.write)|}"
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def filesystem_def)
    apply safe
    by (simp_all add: fs_simp gval.simps ValueEq_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma possible_steps_1_read: "possible_steps Filesystem_Fixed.filesystem 1 <R 1 := u, R 2 := c, R 3 := u> (STR ''read'') [] = {|(1, read_success)|}"
proof-
  have filter:  "ffilter
     (\<lambda>((origin, dest), t).
         origin = 1 \<and>
         Label t = STR ''read'' \<and>
         Arity t = 0 \<and>
         apply_guards (Guard t)
          (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n)
               | R n \<Rightarrow> if R n = R 3 then Some u else if R n = R 2 then Some c else if R n = R 1 then Some u else None))
     Filesystem_Fixed.filesystem =
    {|((1, 1), read_success)|}"
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def filesystem_def)
    apply safe
    by (simp_all add: fs_simp gval.simps ValueEq_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma regsimp: "(\<lambda>x. if x = R 1 then aval (snd (R 1, V (I 1))) (case_vname (\<lambda>n. input2state [EFSM.Str ''user''] 1 (I n)) Map.empty)
          else EFSM.apply_updates [] (case_vname (\<lambda>n. input2state [EFSM.Str ''user''] 1 (I n)) Map.empty) Map.empty x) = <R 1 := Str ''user''>"
  by (rule ext, simp)

lemma regsimp2: " (\<lambda>x. if x = R 1 then aval (snd (R 1, V (R 1))) (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. <R 1 := EFSM.Str ''user''> (R n)))
          else EFSM.apply_updates [(R 2, V (R 2)), (R 3, V (R 1))] (case_vname (\<lambda>n. input2state [] 1 (I n)) (\<lambda>n. <R 1 := EFSM.Str ''user''> (R n)))
                <R 1 := EFSM.Str ''user''> x) = <R 1 := Str ''user'', R 3 := Str ''user''>"
  by (rule ext, simp)

lemma apply_updates_write: "EFSM.apply_updates (Updates Filesystem_Fixed.write)
     (join_ir (snd (hd [(STR ''write'', [Num 50]), (STR ''read'', [])])) <R 1 := EFSM.Str ''user'', R 3 := EFSM.Str ''user''>)
     <R 1 := EFSM.Str ''user'', R 3 := EFSM.Str ''user''> = <R 1 := EFSM.Str ''user'', R 2 := Num 50, R 3 := EFSM.Str ''user''>"
  apply (rule ext)
  by (simp add: write_def)

lemma "observe_trace filesystem 0 <> [((STR ''login''), [Str ''user'']), ((STR ''create''), []), ((STR ''write''), [Num 50]), ((STR ''read''), [])] = [[], [], [], [Some (Num 50)]]"
  apply (rule observe_trace_step)
    apply simp
   apply (rule one_possible_step)
     apply (simp add: possible_steps_0)
    apply (simp add: login_def)
   apply (simp add: login_def regsimp)
  apply (rule observe_trace_step)
    apply simp
   apply (rule one_possible_step)
     apply (simp add: possible_steps_1_create)
    apply (simp add: create_def)
   apply (simp add: create_def)
  apply (simp add: regsimp2)
  apply (rule observe_trace_step)
    apply simp
   apply (rule one_possible_step)
     apply simp
     apply (simp add: possible_steps_1_write)
    apply (simp add: write_def)
   apply (simp only: apply_updates_write)
  apply (rule observe_trace_step)
    apply simp
   apply (rule one_possible_step)
  using possible_steps_1_read
     apply simp
    apply (simp add: read_success_def)
   apply (simp add: read_success_def)
  by (simp add: observe_trace_def)

lemma r_equals_r [simp]: "<R 1:=user, R 2:=content, R 3:=owner> = (\<lambda>a. if a = R 3 then Some owner else if a = R 2 then Some content else if a = R 1 then Some user else <> a)"
  apply (rule ext)
  by simp

lemma possible_steps_1_read_fail: "r (R 3) = Some owner \<and> r (R 1) = Some user \<and> owner \<noteq> user \<Longrightarrow> possible_steps Filesystem_Fixed.filesystem 1 r (STR ''read'') [] = {|(1, read_fail)|}"
proof-
  assume premise: "r (R 3) = Some owner \<and> r (R 1) = Some user \<and> owner \<noteq> user"
  have filter: "ffilter
     (\<lambda>((origin, dest), t).
         origin = 1 \<and>
         Label t = STR ''read'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n) | R n \<Rightarrow> r (R n)))
     Filesystem_Fixed.filesystem =
    {|((1, 1), read_fail)|}"
    using premise
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def filesystem_def)
    apply safe
    by (simp_all add: fs_simp gval.simps ValueEq_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma read_2:  " r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 1 r (STR ''read'') [] = Some (read_fail, 1, [Some (Str ''accessDenied'')], r)"
  apply (simp add: step_def possible_steps_1_read_fail)
  apply (simp add: read_fail_def)
  apply (rule ext)
  by simp

lemma possible_steps_1_logout:  "possible_steps Filesystem_Fixed.filesystem 1 r (STR ''logout'') [] = {|(0, logout)|}"
  apply (simp add: possible_steps_def fs_simp)
  by force

lemma logout_2:  "step filesystem 1 r (STR ''logout'') [] = Some (logout, 0, [], r)"
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
  "label_not_logout s \<equiv> (label (shd s) \<noteq> (STR ''logout''))"

abbreviation label_logout :: "property" where
  "label_logout s \<equiv> (label (shd s) = (STR ''logout''))"

abbreviation label_create :: "property" where
  "label_create s \<equiv> (label (shd s) = (STR ''create''))"

abbreviation read_0 :: "property" where
  "read_0 s \<equiv> (label (shd s)=(STR ''read'') \<longrightarrow> output (shd s)=[Some (Str ''accessDenied'')])"

abbreviation login_attacker :: "property" where
  "login_attacker s \<equiv> (event (shd s) = ((STR ''login''),  [Str ''attacker'']))"

abbreviation login_user :: "property" where
  "login_user s \<equiv> (event (shd s) = ((STR ''login''),  [Str ''user'']))"

lemma "login_user (watch filesystem i) \<Longrightarrow> shd i = ((STR ''login''), [Str ''user''])"
  by (simp add: watch_def)

lemma logout_label:  "t = logout \<Longrightarrow> Label t = (STR ''logout'')"
  by (simp add: logout_def)

lemma create_label:  "t = create \<Longrightarrow> Label t = (STR ''create'')"
  by (simp add: create_def)

lemma every_event_step: "\<forall>s r.  s |\<in>| S filesystem \<longrightarrow> (\<exists>e. fst (ltl_step filesystem (Some s) r e) \<noteq> None)"
  apply safe
  apply (simp only: "filesystem_states")
  apply (case_tac "s = 0")
   apply simp
   apply (rule_tac x="(STR ''login'')" in exI)
   apply (rule_tac x="[x]" in exI)
   apply (simp add: possible_steps_0)
  apply simp
  apply (rule_tac x="(STR ''logout'')" in exI)
  apply (rule_tac x="[]" in exI)
  by (simp add: possible_steps_1_logout)

lemma implode_login: "String.implode ''login'' = STR ''login''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

text_raw{*\snip{userdetails}{1}{2}{%*}
lemma LTL_user_details_stored_in_r1: "((LabelEq ''login'' aand InputEq [u]) impl
                                      (nxt (checkInx rg 1 ValueEq (Some u)))) (watch filesystem i)"
  by (simp add: event_components implode_login possible_steps_0 login_def watch_def ValueEq_def)  
text_raw{*}%endsnip*}

end