theory EFSM_LTL
imports EFSM Filesystem
begin

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> registers)" where
"step e s r l i \<equiv>
  case (possible_steps e s r l i) of
    [(s',t)] \<Rightarrow> (s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)) |
    _ \<Rightarrow> (0, [], r)"

abbreviation neXt :: "efsm \<Rightarrow> statename \<Rightarrow> registers \<Rightarrow> event \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "neXt e s r v f \<equiv> f (step e s r (fst v) (snd v)) v"

primrec globally :: "efsm \<Rightarrow> (statename \<times> outputs \<times> registers) \<Rightarrow> trace \<Rightarrow> ((statename \<times> outputs \<times> registers) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "globally e spr [] f = f spr ('''', [])" |
  "globally e spr (h#t) f = conj (f spr h) (globally e (step e (fst spr) (snd (snd spr)) (fst h) (snd h)) t f)"

lemma "globally filesystem (s,outs,r) t (\<lambda>(s, p, r) e. s \<noteq> 0) \<longrightarrow>
globally filesystem (s,outs,r) t (\<lambda>(s, p, r) e. (fst e = ''write'' \<and> r ''r1'' = 0 \<and> snd e \<noteq> [0]) \<longrightarrow>
  globally filesystem (s, p, r) t (\<lambda>(s', p', r') e'. (s' = 2 \<and> fst e' = ''read'' \<and> r' ''r1'' \<noteq> 0)\<longrightarrow>
    (fst (snd (step filesystem s' r' (fst e') (snd e')))) = [0]))"
  apply simp
proof (induction t)
case Nil
then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply simp
    apply (case_tac "s = 0")
     apply simp
    apply (case_tac "s = 1")
    apply simp
qed


end