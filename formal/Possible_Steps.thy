theory Possible_Steps
imports EFSM
begin

lemma possible_steps_alt_aux: "(\<lambda>((origin, dest), t). (dest, t)) |`|
    ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state i 1 (I n) | R n \<Rightarrow> r (R n)))
     e =
    {|(d, t)|} \<Longrightarrow>
    ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state i 1 (I n) | R n \<Rightarrow> r (R n)))
     e =
    {|((s, d), t)|}"
proof(induct e)
  case empty
  then show ?case
    apply (simp add: ffilter_empty)
    by auto
next
  case (insert x e)
  then show ?case
    apply (cases x)
    apply (case_tac a)
    apply clarify
    apply simp
    apply (simp add: ffilter_finsert)
    apply (case_tac "aa = s")
     apply simp
     apply (case_tac "Label ba = l")
      apply simp
      apply (case_tac "length i = Arity ba")
       apply simp
       apply (case_tac "apply_guards (Guard ba) (case_vname (\<lambda>n. input2state i (Suc 0) (I n)) (\<lambda>n. r (R n)))")
    by auto
qed

lemma possible_steps_alt: "(possible_steps e s r l i = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t).
         origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guard t) (\<lambda>x. case x of I n \<Rightarrow> input2state i 1 (I n) | R n \<Rightarrow> r (R n)))
     e =
    {|((s, d), t)|})"
  apply standard
   apply (simp add: possible_steps_def possible_steps_alt_aux)
  by (simp add: possible_steps_def)

end