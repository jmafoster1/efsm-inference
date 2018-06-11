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
                    (''r1'', (V ''i1'')) (* Store the user ID in r1 *)
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
                    (''r1'', (V ''r1'')), (* Value of r1 remains unchanged *)
                    (''r2'', (V ''r2'')), (* Value of r2 remains unchanged *)
                    (''r3'', (V ''r3''))  (* Value of r3 remains unchanged *)
                  ]
      \<rparr>"

definition "write" :: "transition" where
"write \<equiv> \<lparr>
        Label = ''write'',
        Arity = 1,
        Guard = [], (* No guards *)
        Outputs = [],
        Updates = [ (* Two updates: *)
                    (''r1'', (V ''r1'')), (* Value of r1 remains unchanged *)
                    (''r2'', (V ''i1'')), (* Write the input to r2 *)
                    (''r3'', (V ''r1''))  (* Store the writer in r3 *)
                  ]
      \<rparr>"

definition read_success :: "transition" where
"read_success \<equiv> \<lparr>
        Label = ''read'',
        Arity = 0,
        Guard = [Eq (V ''r1'') (V ''r3'')], (* No guards *)
        Outputs = [(V ''r2'')],
        Updates = [ (* Two updates: *)
                    (''r1'', (V ''r1'')), (* Value of r1 remains unchanged *)
                    (''r2'', (V ''r2'')), (* Value of r2 remains unchanged *)
                    (''r3'', (V ''r3''))  (* Value of r3 remains unchanged *)
                  ]
      \<rparr>"

definition read_fail :: "transition" where
"read_fail \<equiv> \<lparr>
        Label = ''read'',
        Arity = 0,
        Guard = [Ne (V ''r1'') (V ''r3'')], (* No guards *)
        Outputs = [(N 0)],
        Updates = [ 
                    (''r1'', (V ''r1'')), (* Value of r1 remains unchanged *)
                    (''r2'', (V ''r2'')), (* Value of r2 remains unchanged *)
                    (''r3'', (V ''r3''))  (* Value of r3 remains unchanged *)
                  ]
      \<rparr>"

definition filesystem :: "efsm" where
"filesystem \<equiv> \<lparr> 
          S = [1,2],
          s0 = 1,
          T = \<lambda> (a,b) .
              if (a,b) = (1,2) then [login]
              else if (a,b) = (2,1) then [logout]
              else if (a,b) = (2,2) then [write, read_success, read_fail]
              else []
         \<rparr>"

lemmas fs_simp = filesystem_def login_def logout_def write_def read_success_def read_fail_def

primrec all :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "all [] _ = True" |
  "all (h#t) f = (if f h then all t f else False)"

(* step :: efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers) option *)
(* observe_trace :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> observation" where *)

(* noChangeOwner: THEOREM filesystem |- G(cfstate /= NULL_STATE) => FORALL (owner : UID): G((label=write AND r_1=owner) => F(G((label=read AND r_1/=owner) => X(op_1_read_0 = accessDenied)))); *)

lemma "x \<noteq> ''r1'' \<longrightarrow> x \<noteq> ''r3'' \<longrightarrow> x \<noteq> ''r2'' \<longrightarrow> r x = 0 \<Longrightarrow> r ''r3'' \<noteq> r ''r1'' \<Longrightarrow> step filesystem 2 r ''read'' [] = Some (2, [0], r)"
  apply (simp add: fs_simp step_def join_def null_state_def)
  apply (rule ext)
  apply simp
  
  

lemma "(r ''r3'' \<noteq> r ''r1'') \<Longrightarrow> all (observe_trace filesystem 2 r t) (\<lambda>e. e = [] \<or> e = [0])"
proof (induction t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply simp
    apply (cases "step filesystem 2 r (fst a) (snd a)")
     apply simp
    apply simp
    apply safe
    apply (cases "a = (''read'', [])")
    apply simp

qed


end