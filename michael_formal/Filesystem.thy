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
        Outputs = [(N 0)],
        Updates = []
      \<rparr>"

definition read_success :: "transition" where
"read_success \<equiv> \<lparr>
        Label = ''read'',
        Arity = 0,
        Guard = [Eq (V (R 1)) (V (R 3))], (* No guards *)
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
        Guard = [Ne (V (R 1)) (V (R 3))], (* No guards *)
        Outputs = [(N 0)],
        Updates = [ 
                    (R 1, (V (R 1))), (* Value of r1 remains unchanged *)
                    (R 2, (V (R 2))), (* Value of r2 remains unchanged *)
                    (R 3, (V (R 3)))  (* Value of r3 remains unchanged *)
                  ]
      \<rparr>"

definition filesystem :: "efsm" where
"filesystem \<equiv> \<lparr> 
          S = [1,2],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [login]
              else if (a,b) = (2,1) then [logout]
              else if (a,b) = (2,2) then [write, read_success, read_fail, write_fail]
              else []
         \<rparr>"

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

lemma read_2:  " r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 2 r ''read'' [] = Some (2, [0], r)"
  apply (simp add: step_def fs_simp del: Nat.One_nat_def)
  apply (rule ext)
  by simp 

lemma logout_2:  " r = <R 1:= user, R 2:= content, R 3:= owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 2 r ''logout'' [] = Some (1, [], r)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp
end