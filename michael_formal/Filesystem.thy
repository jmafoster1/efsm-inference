theory Filesystem
imports EFSM
begin

(* Takes a user ID and stores it in r1 *)
definition login :: "transition" where
"login \<equiv> \<lparr>
        Label = ''login'',
        Arity = 1,
        Guard = [],
        Outputs = [],
        Updates = [
                    (R 1, (V (I 1))) (* Store the user ID in r1 *)
                  ]
      \<rparr>"

(* Logs out the current user *)
definition logout :: "transition" where
"logout \<equiv> \<lparr>
        Label = ''logout'',
        Arity = 0,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [ (* Two updates: *)
                    (R 1, (V (R 1))), (* Value of r1 remains unchanged *)
                    (R 2, (V (R 2))), (* Value of r2 remains unchanged *)
                    (R 3, (V (R 3)))  (* Value of r3 remains unchanged *)
                  ]
      \<rparr>"

definition "write" :: "transition" where
"write \<equiv> \<lparr>
        Label = ''write'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [ 
                    (R 1, (V (R 1))), (* Value of r1 remains unchanged *)
                    (R 2, (V (I 1))), (* Write the input to r2 *)
                    (R 3, (V (R 1)))  (* Store the writer in r3 *)
                  ]
      \<rparr>"

definition "write_fail" :: "transition" where
"write_fail \<equiv> \<lparr>
        Label = ''write'',
        Arity = 1,
        Guard = [(Ne (V (R 3)) (V (R 1)))], (* No guards *)
        Outputs = [(L (Str ''accessDenied''))],
        Updates = []
      \<rparr>"

definition read_success :: "transition" where
"read_success \<equiv> \<lparr>
        Label = ''read'',
        Arity = 0,
        Guard = [Eq (V (R 1)) (V (R 3)), (gNot (Null (R 2)))], (* No guards *)
        Outputs = [(V (R 2))],
        Updates = [ (* Two updates: *)
                    (R 1, (V (R 1))), (* Value of r1 remains unchanged *)
                    (R 2, (V (R 2))), (* Value of r2 remains unchanged *)
                    (R 3, (V (R 3)))  (* Value of r3 remains unchanged *)
                  ]
      \<rparr>"

definition read_fail :: "transition" where
"read_fail \<equiv> \<lparr>
        Label = ''read'',
        Arity = 0,
        Guard = [(gOr (Ne (V (R 1)) (V (R 3))) (Null (R 2)))],
        Outputs = [(L (Str ''accessDenied''))],
        Updates = [ 
                    (R 1, (V (R 1))), (* Value of r1 remains unchanged *)
                    (R 2, (V (R 2))), (* Value of r2 remains unchanged *)
                    (R 3, (V (R 3)))  (* Value of r3 remains unchanged *)
                  ]
      \<rparr>"

datatype statename = q1 | q2

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

(* export_code filesystem in "Scala" *)

lemmas fs_simp = filesystem_def login_def logout_def write_def read_success_def read_fail_def write_fail_def

primrec all :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "all [] _ = True" |
  "all (h#t) f = (if f h then all t f else False)"

(* step :: efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option *)
(* observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where *)

(* noChangeOwner: THEOREM filesystem |- G(cfstate /= NULL_STATE) => FORALL (owner : UID): G((label=write AND r_1=owner) => F(G((label=read AND r_1/=owner) => X(op_1_read_0 = accessDenied)))); *)

lemma r_equals_r [simp]: "<R 1:=user, R 2:=content, R 3:=owner> = (\<lambda>a. if a = R 3 then Some owner else if a = R 2 then Some content else if a = R 1 then Some user else None)"
  apply (rule ext)
  by simp

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