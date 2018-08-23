theory Lift
  imports "../EFSM"
begin
definition t1up :: "transition" where
"t1up \<equiv> \<lparr>
        Label = ''goUp'',
        Arity = 1,
        Guard = [(gexp.Gt (V (I 1)) (L (Num 0)))],
        Outputs = [(V (I 1))],
        Updates = []
      \<rparr>"

lemma updates_t1up [simp]:"Updates t1up = []"
  by (simp add: t1up_def)

definition t2up :: "transition" where
"t2up \<equiv> \<lparr>
        Label = ''goUp'',
        Arity = 1,
        Guard = [(gexp.Gt (V (I 1)) (L (Num 0)))],
        Outputs = [(Plus (V (I 1)) (L (Num (-1))))],
        Updates = []
      \<rparr>"

lemma updates_t2up [simp]:"Updates t2up = []"
  by (simp add: t2up_def)

lemma guard_t2up: "Guard t2up = [(gexp.Gt (V (I 1)) (L (Num 0)))]"
  by (simp add: t2up_def)

definition t3up :: "transition" where
"t3up \<equiv> \<lparr>
        Label = ''goUp'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 0)))],
        Outputs = [(L (Num 0))],
        Updates = []
      \<rparr>"

lemma updates_t3up [simp]:"Updates t3up = []"
  by (simp add: t3up_def)

definition t1down :: "transition" where
"t1down \<equiv> \<lparr>
        Label = ''goDown'',
        Arity = 1,
        Guard = [(gexp.Gt (V (I 1)) (L (Num 0)))],
        Outputs = [(V (I 1))],
        Updates = []
      \<rparr>"

definition t2down :: "transition" where
"t2down \<equiv> \<lparr>
        Label = ''goDown'',
        Arity = 1,
        Guard = [(gexp.Gt (V (I 1)) (L (Num 0)))],
        Outputs = [((Plus (V (I 1)) (L (Num (-1)))))],
        Updates = []
      \<rparr>"

definition t3down :: "transition" where
"t3down \<equiv> \<lparr>
        Label = ''goDown'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 0)))],
        Outputs = [(L (Num 0))],
        Updates = []
      \<rparr>"

definition openDoors :: transition where
"openDoors \<equiv> \<lparr>
        Label = ''open'',
        Arity = 0,
        Guard = [],
        Outputs = [(L (Num 1))],
        Updates = []
      \<rparr>"

definition closeDoors :: transition where
"closeDoors \<equiv> \<lparr>
        Label = ''close'',
        Arity = 0,
        Guard = [],
        Outputs = [(L (Num 0))],
        Updates = []
      \<rparr>"

lemmas transitions = t1up_def t2up_def t3up_def t1down_def t2down_def t3down_def openDoors_def closeDoors_def

datatype statename = q1 | q2 | q3 | q4

definition lift :: "statename efsm" where
"lift \<equiv> \<lparr>
          s0 = q1,
          T = \<lambda> (a,b) . 
                   if (a,b) = (q1,q2) then {t1up}
              else if (a,b) = (q2,q2) then {t2up}
              else if (a,b) = (q2,q1) then {t3up}
              else if (a,b) = (q1,q3) then {t1down}
              else if (a,b) = (q3,q3) then {t2down}
              else if (a,b) = (q3,q1) then {t3down}
              else if (a,b) = (q1,q4) then {openDoors}
              else if (a,b) = (q4,q1) then {closeDoors}
              else {}
         \<rparr>"

lemma label_goup_q2: "Label b = ''goUp'' \<Longrightarrow> b \<in> T lift (s0 lift, a) \<Longrightarrow> a = q2 \<and> b = t1up"
  apply (simp add: lift_def)
  apply (cases a)
     apply simp
    apply simp
   apply (simp add: t1down_def)
  by (simp add: openDoors_def)

lemma possible_steps_q1_goup: "possible_steps lift (s0 lift) Map.empty ''goUp'' [Num 1] = {(q2, t1up)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_goup_q2)
      apply (simp add: label_goup_q2)
  prefer 2
  apply (simp add: lift_def)
  by (simp_all add: t1up_def)

lemma label_goup_q2_2: "Label b = ''goUp'' \<Longrightarrow> b \<in> T lift (q2, a) \<Longrightarrow> a = q2 \<or> a = q1"
  apply (simp add: lift_def)
  apply (cases a)
  by simp_all

lemma t2up_q2_q2:  "Label b = ''goUp'' \<Longrightarrow> b \<in> T lift (q2, q2) = (b = t2up)"
  by (simp add: lift_def)

lemma t3up_q2_q1: "Label b = ''goUp'' \<Longrightarrow> b \<in> T lift (q2, q1) = (b = t3up)"
  by (simp add: lift_def)

lemma possible_steps_q2_goup: "possible_steps lift q2 Map.empty ''goUp'' [Num 0] = {(q1, t3up)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac "a=q1")
        apply simp
       apply (case_tac "a=q2")
        apply (simp add: t2up_q2_q2 guard_t2up)
  using label_goup_q2_2 apply blast
      apply (case_tac "a=q1")
       apply (simp add: t3up_q2_q1)
      apply (case_tac "a=q2")
       apply (simp add: t2up_q2_q2 guard_t2up)
  using label_goup_q2_2 apply blast
     prefer 2
     apply (simp add: lift_def)
  by (simp_all add: t3up_def)

lemma label_open_q4: "Label b = ''open'' \<Longrightarrow> b \<in> T lift (q1, a) \<Longrightarrow> b = openDoors \<and> a = q4"
  apply (simp add: lift_def)
  apply (cases a)
     apply simp
    apply (simp add: t1up_def)
   apply (simp add: t1down_def)
  by simp

lemma possible_steps_open_q1: "(possible_steps lift q1 Map.empty ''open'' []) = {(q4, openDoors)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (simp add: label_open_q4)
      apply (simp add: label_open_q4)
  prefer 2
  apply (simp add: lift_def)
  by (simp_all add: openDoors_def)

lemma "observe_trace lift (s0 lift) <> [(''goUp'', [Num 1]), (''goUp'', [Num 0]), (''open'', [])] = [[Num 1], [Num 0], [Num 1]]"
  apply (simp add: possible_steps_q1_goup possible_steps_q2_goup possible_steps_open_q1 del: One_nat_def)
  by (simp add: transitions)
end