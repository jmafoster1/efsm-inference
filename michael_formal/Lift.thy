theory Lift
  imports EFSM
begin
definition t1up :: "transition" where
"t1up \<equiv> \<lparr>
        Label = ''goUp'',
        Arity = 1,
        Guard = [((V ''i1'') > (N 0))],
        Outputs = [(V ''i1'')],
        Updates = []
      \<rparr>"

definition t2up :: "transition" where
"t2up \<equiv> \<lparr>
        Label = ''goUp'',
        Arity = 1,
        Guard = [((V ''i1'') > (N 0))],
        Outputs = [(((V ''i1'') + (N (-1))))],
        Updates = []
      \<rparr>"

definition t3up :: "transition" where
"t3up \<equiv> \<lparr>
        Label = ''goUp'',
        Arity = 1,
        Guard = [((V ''r1'') = (N 0))],
        Outputs = [(N 0)],
        Updates = []
      \<rparr>"

definition t1down :: "transition" where
"t1down \<equiv> \<lparr>
        Label = ''goDown'',
        Arity = 1,
        Guard = [((V ''i1'') > (N 0))],
        Outputs = [(V ''i1'')],
        Updates = []
      \<rparr>"

definition t2down :: "transition" where
"t2down \<equiv> \<lparr>
        Label = ''goDown'',
        Arity = 1,
        Guard = [((V ''i1'') > (N 0))],
        Outputs = [(((V ''i1'') + (N (-1))))],
        Updates = []
      \<rparr>"

definition t3down :: "transition" where
"t3down \<equiv> \<lparr>
        Label = ''goDown'',
        Arity = 1,
        Guard = [((V ''r1'') = (N 0))],
        Outputs = [(N 0)],
        Updates = []
      \<rparr>"

definition openDoors :: transition where
"openDoors \<equiv> \<lparr>
        Label = ''open'',
        Arity = 0,
        Guard = true,
        Outputs = [(N 1)],
        Updates = []
      \<rparr>"

definition closeDoors :: transition where
"closeDoors \<equiv> \<lparr>
        Label = ''close'',
        Arity = 0,
        Guard = true,
        Outputs = [(N 0)],
        Updates = []
      \<rparr>"

lemmas transitions = t1up_def t2up_def t3up_def t1down_def t2down_def t3down_def openDoors_def closeDoors_def

definition lift :: "efsm" where
"lift \<equiv> \<lparr> S = [1,2,3,4],
          s0 = 1,
          T = \<lambda> (a,b) . 
                   if (a,b) = (1,2) then [t1up]
              else if (a,b) = (2,2) then [t2up]
              else if (a,b) = (2,1) then [t3up]
              else if (a,b) = (1,3) then [t1down]
              else if (a,b) = (3,3) then [t2down]
              else if (a,b) = (3,1) then [t3down]
              else if (a,b) = (1,4) then [openDoors]
              else if (a,b) = (4,1) then [closeDoors]
              else []
         \<rparr>"

lemma "observe_trace lift (s0 lift) <> [(''goUp'', [1]), (''goUp'', [0]), (''open'', [])] = [[1], [0], [1]]"
  by (simp add: step_def lift_def transitions join_def index_def shows_stuff input2state_def)

lemma "observe_trace lift (s0 lift) <> [(''goDown'', [1]), (''goDown'', [0]), (''open'', [])] = [[1], [0], [1]]"
  by (simp add: step_def lift_def transitions join_def index_def shows_stuff input2state_def)

lemma "observe_trace lift (s0 lift) <> [(''open'', []), (''close'', []), (''open'', [])] = [[1], [0], [1]]"
  by (simp add: step_def lift_def transitions join_def index_def shows_stuff input2state_def)
end