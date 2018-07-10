theory Filesystem_Fixed
imports Filesystem
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

definition "write_fail" :: "transition" where
"write_fail \<equiv> \<lparr>
        Label = ''write'',
        Arity = 1,
        Guard = [(Ne (V (R 3)) (V (R 1)))], (* No guards *)
        Outputs = [(N 0)],
        Updates = []
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

lemma r_equals_r [simp]: "<R 1:=user, R 2:=content, R 3:=owner> = (\<lambda>a. if a = R 3 then owner else if a = R 2 then content else if a = R 1 then user else <> a)"
  apply (rule ext)
  by simp

lemma read_2:  " r = <R 1:=Some user, R 2:=Some content, R 3:=Some owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 2 r ''read'' [] = Some (2, [0], r)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

lemma logout_2:  " r = <R 1:=Some user, R 2:=Some content, R 3:=Some owner> \<Longrightarrow>
    owner \<noteq> user \<Longrightarrow>
    step filesystem 2 r ''logout'' [] = Some (1, [], r)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

end