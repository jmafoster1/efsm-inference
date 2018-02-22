theory EFSM
imports IO
begin

abbreviation is_possible_step :: "efsm \<Rightarrow> statename \<Rightarrow> statename \<Rightarrow> transition \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> data \<Rightarrow> bool" where
"is_possible_step e s s' t l ip dt \<equiv> 
  (((label t) = l) \<and> (find (\<lambda>x . x = t) (M e(s,s')) \<noteq> None) \<and> (guard t)(ip,dt))"

abbreviation possible_steps :: "efsm \<Rightarrow> statename \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> data \<Rightarrow> (statename * transition) list" where
"possible_steps e s l ip dt \<equiv> [(s',t) . s' \<leftarrow> S e, t \<leftarrow> M e(s,s'), is_possible_step e s s' t l ip dt]"

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> data \<Rightarrow> (statename \<times> outvalues \<times> data) option" where
"step e s l ip dt \<equiv>
  case possible_steps e s l ip dt of
    [] \<Rightarrow> None
    | [(s',t)] \<Rightarrow> Some (s', (outputs t) (ip,dt), (updates t) (ip,dt))
    | _ \<Rightarrow> None"
declare step_def [simp]

primrec observe_steps :: "efsm \<Rightarrow> statename \<Rightarrow> data \<Rightarrow> trace \<Rightarrow> observation" where
"observe_steps _ _ _ [] = []"
|"observe_steps e s dt (ip#ips) = 
    (case step e s (fst ip) (snd ip) dt of
      Some (s', ops, dt') \<Rightarrow> ops#(observe_steps e s' dt' ips)
      | None \<Rightarrow> []
    )"
declare observe_steps_def [simp]

definition observe :: "efsm \<Rightarrow> trace \<Rightarrow> observation" where
"observe e tr \<equiv> observe_steps e (s0 e) blankdata tr"

definition equiv :: "efsm \<Rightarrow> efsm \<Rightarrow> trace \<Rightarrow> bool" where
"equiv e1 e2 t \<equiv> (observe e1 t) = (observe e2 t)"

lemma equiv_comute: "equiv e1 e2 t \<equiv> equiv e2 e1 t"
  by (smt EFSM.equiv_def)

lemma equiv_trans: "equiv e1 e2 t \<and> equiv e2 e3 t \<longrightarrow> equiv e1 e3 t"
  by (simp add: EFSM.equiv_def)

lemma equiv_idem: "equiv e1 e1 t"
  by (simp add: EFSM.equiv_def)

end