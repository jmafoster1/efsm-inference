theory drinks_machine
  imports EFSM
begin

definition t1_updates :: update_function where
  "t1_updates i _ = <''r1'' := i!0, ''r2'' := 0>"
declare t1_updates_def [simp]

definition t1 :: "transition" where
"t1 \<equiv> \<lparr> Label = ''select'',
        Arity = 1,
        Guard = trueguard, 
        Outputs = blank, (*<>*)
        Updates = t1_updates (*<''r1'' := (V ''i1''), ''r2'' := 0>*)
      \<rparr>"
declare t1_def [simp]

definition t2_updates :: update_function where
  "t2_updates i r = <
                      ''r1'' := aval (V ''r1'') r,
                      ''r2'' := aval (Plus (N (aval (V ''r2'') r)) (N (i!0))) r
                    >"
declare t2_updates_def [simp]

definition t2_outputs :: output_function where
  "t2_outputs i r = [aval (Plus (N (aval (V ''r2'') r)) (N (i!0))) r]"

definition t2 :: "transition" where
"t2 \<equiv> \<lparr> Label = ''coin'',
        Arity = 1,
        Guard = trueguard, 
        Outputs = blank, (*<>*)
        Updates = t2_updates (*<''r1'' := (V ''i1''), ''r2'' := 0>*)
      \<rparr>"
declare t2_def [simp]

definition t3_outputs :: output_function where
  "t3_outputs _ r = [(aval (V ''r1'') r)]"
declare t3_outputs_def [simp]

definition t3_guard :: guard where
"t3_guard i r = ((aval (V ''r2'') r) \<ge> 100)"
declare t3_guard_def [simp]

definition t3 :: "transition" where
"t3 \<equiv> \<lparr> Label = ''vend'',
        Arity = 0,
        Guard = t3_guard, 
        Outputs = t3_outputs,
        Updates = no_updates
      \<rparr>"
declare t3_def [simp]

lemma "Outputs t1 = blank"
  by simp

lemma "apply_outputs t1 [1] <> = []"
  by simp

lemma "apply_updates t1 [1] <> = <''r1'':= 1, ''r2'' := 0>"
  by simp

lemma blank_state : "<> = <''r1'' := 0, ''r2'' := 0>"
  by (metis fun_upd_triv null_state_def) (*As soon as I try and use this it crashes*)

lemma "apply_outputs t2 [50] <> = []"
  by simp

lemma "apply_updates t2 [50] <''r1'' := 1, ''r2'' := 0> = <''r1'':= 1, ''r2'' := 50>"
  by simp

lemma "apply_outputs t3 [] <''r1'' := 1, ''r2'' := 100> = [1]"
  by simp

lemma "apply_updates t3 [] <''r1'' := 1, ''r2'' := 100> = <''r1'' := 1, ''r2'' := 100>"
  by simp

definition vend :: "efsm" where
"vend \<equiv> \<lparr> S = [1,2,3],
          s0 = 1,
          T = \<lambda> (a,b) . 
              if (a,b) = (1,2) then [t1]
              else if (a,b) = (2,2) then [t2]
              else if (a,b) = (2,3) then [t3]
              else []
         \<rparr>"

end