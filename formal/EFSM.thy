theory EFSM
imports IO
begin

abbreviation is_possible_step :: "efsm \<Rightarrow> statename \<Rightarrow> statename \<Rightarrow> transition \<Rightarrow> inputs \<Rightarrow> data \<Rightarrow> bool" where
"is_possible_step e s s' t ip dt \<equiv> 
  ((find (\<lambda>x . x = t) (M e(s,s')) \<noteq> None) \<and> (fst t)(ip,dt))"

abbreviation possible_steps :: "efsm \<Rightarrow> statename \<Rightarrow> inputs \<Rightarrow> data \<Rightarrow> (statename * transition) list" where
"possible_steps e s ip dt \<equiv> [(s',t) . s' \<leftarrow> S e, t \<leftarrow> M e(s,s'), is_possible_step e s s' t ip dt]"

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> inputs \<Rightarrow> data \<Rightarrow> (statename \<times> outvalues \<times> data) option" where
"step e s ip dt \<equiv>
  case possible_steps e s ip dt of
    [] \<Rightarrow> None
    | [(s',(_,ops,ups))] \<Rightarrow> Some (s', ops (ip,dt), ups (ip,dt))
    | _ \<Rightarrow> None"
declare step_def [simp]

primrec observe_steps :: "efsm \<Rightarrow> statename \<Rightarrow> data \<Rightarrow> trace \<Rightarrow> observation" where
"observe_steps _ _ _ [] = []"
|"observe_steps e s dt (ip#ips) = 
    (case step e s ip dt of
      Some (s', ops, dt') \<Rightarrow> ops#(observe_steps e s' dt' ips)
      | None \<Rightarrow> []
    )"
declare observe_steps_def [simp]

definition observe :: "efsm \<Rightarrow> trace \<Rightarrow> observation" where
"observe e tr \<equiv> observe_steps e (s0 e) (d0 e) tr"

definition equiv :: "efsm \<Rightarrow> efsm \<Rightarrow> trace \<Rightarrow> bool" where
"equiv e1 e2 t \<equiv> (observe e1 t) = (observe e2 t)"

end