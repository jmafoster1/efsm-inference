theory Filesystem
imports "../Contexts" "../EFSM"
begin

\<comment> \<open> Takes a user ID and stores it in r1 \<close>
definition login :: "transition" where
"login \<equiv> \<lparr>
        Label = (STR ''login''),
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [
                    (R 1, (V (I 1))) \<comment> \<open> Store the user ID in r1 \<close>
                  ]
      \<rparr>"

\<comment> \<open> Logs out the current user \<close>
definition logout :: "transition" where
"logout \<equiv> \<lparr>
        Label = (STR ''logout''),
        Arity = 0,
        Guard = [], \<comment> \<open> No guards \<close>
        Outputs = [],
        Updates = [ \<comment> \<open> Two updates: \<close>
                    (R 1, (V (R 1))), \<comment> \<open> Value of r1 remains unchanged \<close>
                    (R 2, (V (R 2))), \<comment> \<open> Value of r2 remains unchanged \<close>
                    (R 3, (V (R 3)))  \<comment> \<open> Value of r3 remains unchanged \<close>
                  ]
      \<rparr>"

definition "write" :: "transition" where
"write \<equiv> \<lparr>
        Label = (STR ''write''),
        Arity = 1,
        Guard = [], \<comment> \<open> No guards \<close>
        Outputs = [],
        Updates = [
                    (R 1, (V (R 1))), \<comment> \<open> Value of r1 remains unchanged \<close>
                    (R 2, (V (I 1))), \<comment> \<open> Write the input to r2 \<close>
                    (R 3, (V (R 1)))  \<comment> \<open> Store the writer in r3 \<close>
                  ]
      \<rparr>"

definition "write_fail" :: "transition" where
"write_fail \<equiv> \<lparr>
        Label = (STR ''write''),
        Arity = 1,
        Guard = [(Ne (V (R 3)) (V (R 1)))], \<comment> \<open> No guards \<close>
        Outputs = [(L (Str ''accessDenied''))],
        Updates = []
      \<rparr>"

definition read_success :: "transition" where
"read_success \<equiv> \<lparr>
        Label = (STR ''read''),
        Arity = 0,
        Guard = [gexp.Eq (V (R 1)) (V (R 3)), (gNot (Null (V (R 2))))], \<comment> \<open> No guards \<close>
        Outputs = [(V (R 2))],
        Updates = [ \<comment> \<open> Two updates: \<close>
                    (R 1, (V (R 1))), \<comment> \<open> Value of r1 remains unchanged \<close>
                    (R 2, (V (R 2))), \<comment> \<open> Value of r2 remains unchanged \<close>
                    (R 3, (V (R 3)))  \<comment> \<open> Value of r3 remains unchanged \<close>
                  ]
      \<rparr>"

definition read_fail :: "transition" where
"read_fail \<equiv> \<lparr>
        Label = (STR ''read''),
        Arity = 0,
        Guard = [(gOr (Ne (V (R 1)) (V (R 3))) (Null (V (R 2))))],
        Outputs = [(L (Str ''accessDenied''))],
        Updates = [
                    (R 1, (V (R 1))), \<comment> \<open> Value of r1 remains unchanged \<close>
                    (R 2, (V (R 2))), \<comment> \<open> Value of r2 remains unchanged \<close>
                    (R 3, (V (R 3)))  \<comment> \<open> Value of r3 remains unchanged \<close>
                  ]
      \<rparr>"

definition filesystem :: "transition_matrix" where
"filesystem \<equiv> {|
              ((0,1), login),
              ((1,0), logout),
              ((1,1), write),
              ((1,1), read_success),
              ((1,1), read_fail),
              ((1,1), write_fail)
         |}"

lemmas transitions = login_def logout_def write_def read_success_def read_fail_def write_fail_def

primrec all :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "all [] _ = True" |
  "all (h#t) f = (if f h then all t f else False)"

\<comment> \<open> step :: efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option \<close>
\<comment> \<open> observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where \<close>

\<comment> \<open> noChangeOwner: THEOREM filesystem |- G(cfstate /= NULL_STATE) => FORALL (owner : UID): G((label=write AND r_1=owner) => F(G((label=read AND r_1/=owner) => X(op_1_read_0 = accessDenied)))); \<close>

lemma r_equals_r [simp]: "<R 1:=user, R 2:=content, R 3:=owner> = (\<lambda>a. if a = R 3 then Some owner else if a = R 2 then Some content else if a = R 1 then Some user else None)"
  apply (rule ext)
  by simp

declare One_nat_def [simp del]

lemma possible_steps_1_read: "r (R 1) = user \<and> r (R 3) = owner \<Longrightarrow> owner \<noteq> user \<Longrightarrow> possible_steps filesystem 1 r (STR ''read'') [] = {|(1, read_fail)|}"
proof-
  assume premise1: "r (R 1) = user \<and> r (R 3) = owner"
  assume premise2: "owner \<noteq> user"
  have filter: "ffilter
     (\<lambda>((origin, dest), t).
         origin = 1 \<and>
         Label t = STR ''read'' \<and> Arity t = 0 \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state [] 1 (I n) | R n \<Rightarrow> r (R n)))
     filesystem =
    {|((1, 1), read_fail)|}"
    using premise1 premise2
    apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def filesystem_def)
    apply safe
    by (simp_all add: transitions gval.simps ValueEq_def)
  show ?thesis
    by (simp add: possible_steps_def filter)
qed

lemma read_2:  "r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 1 r (STR ''read'') [] = Some (read_fail, 1, [Some (Str ''accessDenied'')], r)"
  apply (simp add: step_def possible_steps_1_read)
  apply (simp add: transitions filesystem_def)
  apply (rule ext)
  by simp

lemma possible_steps_1_logout: "possible_steps filesystem 1 r (STR ''logout'') [] = {|(0, logout)|}"
  apply (simp add: possible_steps_def transitions filesystem_def)
  by force

lemma logout_2:  "r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 1 r (STR ''logout'') [] = Some (logout, 0, [], r)"
  apply (simp add: step_def possible_steps_1_logout)
  apply (simp add: filesystem_def transitions)
  apply (rule ext)
  by simp
end
