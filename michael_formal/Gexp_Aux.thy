theory Gexp_Aux
imports GExp
begin

(*Prove usual lemmas about equality*)

lemma "(gval x s = None) \<or> (gval y s = None) = (gval (Nor x y) s = None)"
  apply (cases "gval x s")
   apply simp
  apply (cases "gval y s")
   apply simp
  by simp

lemma "(gval x s \<noteq> None) \<and> (gval y s \<noteq> None) \<Longrightarrow> (gval (Nor x y) s \<noteq> None)"
  apply (cases "gval x s")
   apply (cases "gval y s")
    prefer 3
    apply (cases "gval y s")
  by simp_all

lemma "gexp_equiv x y \<Longrightarrow> gexp_equiv (gNot x) (gNot y)"
  by simp

lemma "gexp_equiv (Bc False) (gNot (Bc True))"
  by simp

lemma "gexp_equiv (gOr x y) (gOr y x)"
  apply simp
  apply (rule allI)
  apply (case_tac "gval x s")
   apply (case_tac "gval y s")
    apply simp
   apply simp
   apply (case_tac "gval y s")
   apply simp
  by auto
  
lemma "gexp_equiv x y \<Longrightarrow> gval x = gval y"
  apply (rule ext)
  by simp
end