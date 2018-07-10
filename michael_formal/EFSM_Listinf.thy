theory EFSM_Listinf
imports "List-Infinite.ListInf" EFSM Filesystem
begin

definition step :: "efsm \<Rightarrow> statename \<Rightarrow> state \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (statename \<times> outputs \<times> state)" where
  "step e s r l i \<equiv>
    case (possible_steps e s r l i) of
      [(s',t)] \<Rightarrow> (s', (apply_outputs (Outputs t) (join_ir i r)), (apply_updates (Updates t) (join_ir i r) r)) |
      _ \<Rightarrow> (0, [], r)"

primrec stepToN :: "efsm \<Rightarrow> (statename \<times> outputs \<times> state) \<Rightarrow> trace \<Rightarrow> (statename \<times> outputs \<times> state)" where
  "stepToN e spr [] = spr" |
  "stepToN e spr (h#t) = stepToN e (step e (fst spr) (snd (snd spr)) (fst h) (snd h)) t"

primrec take_n :: "'a ilist \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take_n i 0 l = l" |
  "take_n i (Suc n) l = take_n i n (l@[i (Suc n)])"

abbreviation take :: "'a ilist \<Rightarrow> nat \<Rightarrow> 'a list" where
  "take i n \<equiv> take_n i n []"

abbreviation neXt :: "efsm \<Rightarrow> statename \<Rightarrow> state \<Rightarrow> event \<Rightarrow> ((statename \<times> outputs \<times> state) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
  "neXt e s r v f \<equiv> f (step e s r (fst v) (snd v)) v"

abbreviation globally :: "efsm \<Rightarrow> statename \<Rightarrow> outputs \<Rightarrow> state \<Rightarrow> event ilist \<Rightarrow> nat \<Rightarrow> ((statename \<times> outputs \<times> state) \<Rightarrow> event \<Rightarrow> bool) \<Rightarrow> bool" where
"globally e s p r t n' f \<equiv> \<forall>n. n > n' \<longrightarrow> (f (stepToN e ((s0 e), [], <>) (take t n)) (t (n+1)))"






lemma read_success: "ba ''r1'' \<noteq> 1 \<Longrightarrow> ba ''r3'' = 1 \<Longrightarrow> step filesystem 2 ba ''read'' [] = (2, [0], ba)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

lemma read_success_1: "ba ''r1'' = ba ''r3'' \<Longrightarrow>  step filesystem 2 ba ''read'' [] = (2, [ba ''r2''], ba)"
  apply (simp add: fs_simp step_def)
  apply (rule ext)
  by simp

lemma "globally filesystem s outs reg t 0 (\<lambda>(s, p, r) e. s \<noteq> 0) \<longrightarrow>
globally filesystem s outs reg t j (\<lambda>(s, p, r) e. (fst e = ''write'' \<and> r ''r1'' = 1 \<and> snd e \<noteq> [0]) \<longrightarrow> i > j \<longrightarrow>
  globally filesystem s p r t i (\<lambda>(s', p', r') e'. (s' = 2 \<and> fst e' = ''read'' \<and> r' ''r1'' \<noteq> 1)\<longrightarrow>
    (fst (snd (step filesystem s' r' (fst e') (snd e')))) = [0])
)"
  apply safe
  apply simp
  apply (case_tac "ba ''r3'' = 1")

end