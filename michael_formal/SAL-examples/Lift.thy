theory Lift
  imports "../EFSM"
begin

declare One_nat_def [simp del]

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

definition lift :: transition_matrix where
"lift \<equiv> {|
              ((0,1), t1up),
              ((1,1), t2up),
              ((1,0), t3up),
              ((0,2), t1down),
              ((2,2), t2down),
              ((2,0), t3down),
              ((0,3), openDoors),
              ((3,0), closeDoors)
         |}"

lemma "observe_trace lift 0 <> [(''goUp'', [Num 1]), (''goUp'', [Num 0]), (''open'', [])] = [[Some (Num 1)], [Some (Num 0)], [Some (Num 1)]]"
proof-
  have possible_steps_0_goup: "possible_steps lift 0 Map.empty ''goUp'' [Num 1] = {|(1, t1up)|}"
    apply (simp add: possible_steps_def lift_def transitions)
    by force
  have possible_steps_1_goup: "possible_steps lift 1 Map.empty ''goUp'' [Num 0] = {|(0, t3up)|}"
    apply (simp add: possible_steps_def lift_def transitions)
    by force
  have possible_steps_open_0: "possible_steps lift 0 Map.empty ''open'' [] = {|(3, openDoors)|}"
    apply (simp add: possible_steps_def lift_def transitions)
    by force
  show ?thesis
    apply (simp add: observe_trace_def observe_all_def step_def)
    apply (simp add: possible_steps_0_goup possible_steps_1_goup possible_steps_open_0)
    by (simp add: transitions)
qed
end