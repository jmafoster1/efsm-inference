theory Filesystem
imports "../Contexts" "../EFSM" "HOL-Library.Code_Target_Int"
begin

\<comment> \<open> Takes a user ID and stores it in r1 \<close>
definition login :: "transition" where
"login \<equiv> \<lparr>
        Label = ''login'',
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
        Label = ''logout'',
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
        Label = ''write'',
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
        Label = ''write'',
        Arity = 1,
        Guard = [(Ne (V (R 3)) (V (R 1)))], \<comment> \<open> No guards \<close>
        Outputs = [(L (Str ''accessDenied''))],
        Updates = []
      \<rparr>"

definition read_success :: "transition" where
"read_success \<equiv> \<lparr>
        Label = ''read'',
        Arity = 0,
        Guard = [gexp.Eq (V (R 1)) (V (R 3)), (gNot (Null (R 2)))], \<comment> \<open> No guards \<close>
        Outputs = [(V (R 2))],
        Updates = [ \<comment> \<open> Two updates: \<close>
                    (R 1, (V (R 1))), \<comment> \<open> Value of r1 remains unchanged \<close>
                    (R 2, (V (R 2))), \<comment> \<open> Value of r2 remains unchanged \<close>
                    (R 3, (V (R 3)))  \<comment> \<open> Value of r3 remains unchanged \<close>
                  ]
      \<rparr>"

definition read_fail :: "transition" where
"read_fail \<equiv> \<lparr>
        Label = ''read'',
        Arity = 0,
        Guard = [(gOr (Ne (V (R 1)) (V (R 3))) (Null (R 2)))],
        Outputs = [(L (Str ''accessDenied''))],
        Updates = [
                    (R 1, (V (R 1))), \<comment> \<open> Value of r1 remains unchanged \<close>
                    (R 2, (V (R 2))), \<comment> \<open> Value of r2 remains unchanged \<close>
                    (R 3, (V (R 3)))  \<comment> \<open> Value of r3 remains unchanged \<close>
                  ]
      \<rparr>"

datatype statename = q1 | q2

lemma UNIV_statename: "UNIV = {q1 , q2}"
  using statename.exhaust by auto

instance statename :: finite
  by standard (simp add: UNIV_statename)

definition filesystem :: "statename efsm" where
"filesystem \<equiv> \<lparr>
          s0 = q1,
          T = \<lambda> (a,b) .
              if (a,b) = (q1,q2) then {login}
              else if (a,b) = (q2,q1) then {logout}
              else if (a,b) = (q2,q2) then {write, read_success, read_fail, write_fail}
              else {}
         \<rparr>"

lemma s0_filesystem [simp]: "s0 filesystem = q1"
  by (simp add: filesystem_def)


code_printing
  type_constructor bool \<rightharpoonup> (Scala) "Bool"
  | constant True \<rightharpoonup> (Scala) "true"
  | constant False \<rightharpoonup> (Scala) "false"
  | constant HOL.conj \<rightharpoonup> (Scala) "_ && _"

\<comment> \<open> export_code GExp.satisfiable in "Scala" \<close>

value "(Contexts.apply_guard \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Bc True\<rbrakk> ((gexp.Eq (V (R 2)) (L (Num 100))) \<or> (Ne (V (R 1)) (L (Num 100))))) (V (R 2))"

lemmas fs_simp = filesystem_def login_def logout_def write_def read_success_def read_fail_def write_fail_def

primrec all :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "all [] _ = True" |
  "all (h#t) f = (if f h then all t f else False)"

\<comment> \<open> step :: efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option \<close>
\<comment> \<open> observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where \<close>

\<comment> \<open> noChangeOwner: THEOREM filesystem |- G(cfstate /= NULL_STATE) => FORALL (owner : UID): G((label=write AND r_1=owner) => F(G((label=read AND r_1/=owner) => X(op_1_read_0 = accessDenied)))); \<close>

lemma r_equals_r [simp]: "<R 1:=user, R 2:=content, R 3:=owner> = (\<lambda>a. if a = R 3 then Some owner else if a = R 2 then Some content else if a = R 1 then Some user else None)"
  apply (rule ext)
  by simp

\<comment> \<open> This one takes longer than you think to prove \<close>
lemma label_read_q2: "b \<in> T filesystem (q2, a) \<Longrightarrow> Label b = ''read'' \<Longrightarrow> a = q2 \<and> (b = read_success \<or> b = read_fail)"
  apply (simp add: filesystem_def)
  apply (cases a)
   apply (simp add: logout_def)
  apply safe
  apply simp
  apply (simp add: fs_simp)
  by auto

lemma possible_steps_q2_read: "owner \<noteq> user \<Longrightarrow> possible_steps filesystem q2 <R (Suc 0) := user, R 2 := content, R 3 := owner> ''read'' [] = {(q2, read_fail)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_read_q2)
      apply (simp add: label_read_q2)
      apply (case_tac "b = read_success")
       apply (simp add: read_success_def read_fail_def)
      apply (case_tac "b = read_fail")
       apply simp
      using label_read_q2 apply blast
     apply (simp add: read_fail_def)
    apply (simp add: read_fail_def filesystem_def)
   apply (simp add: read_fail_def)
  by (simp add: read_fail_def)

lemma read_2:  "r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem q2 r ''read'' [] = Some (q2, [Str ''accessDenied''], r)"
  apply simp
  apply safe
   apply (simp add: possible_steps_q2_read read_fail_def)
   apply (rule ext)
   apply simp
  by (simp add: possible_steps_q2_read)

lemma label_logout_q1: "Label b = ''logout'' \<Longrightarrow> b \<in> T filesystem (q2, a) \<Longrightarrow> b = logout \<and> a = q1"
  apply (simp add: filesystem_def)
  apply (cases a)
   apply simp
  apply (simp add: fs_simp)
  by auto

lemma possible_steps_q2_logout: "possible_steps filesystem q2 r ''logout'' [] = {(q1, logout)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_logout_q1)
      apply (simp add: label_logout_q1)
     apply (simp add: logout_def)
    apply (simp add: filesystem_def)
  by (simp_all add: logout_def)

lemma logout_2:  "r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem q2 r ''logout'' [] = Some (q1, [], r)"
  apply (simp add: possible_steps_q2_logout)
  apply (simp add: logout_def)
  apply (rule ext)
  by simp
end
