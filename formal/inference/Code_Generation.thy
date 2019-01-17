theory Code_Generation
  imports Inference "HOL-Library.Code_Target_Int" "../FSet_Utils"
begin

declare choice_def [code del]
declare nondeterministic_simulates_def [code del]
declare directly_subsumes_def [code del]

code_printing
  constant "choice" \<rightharpoonup> (Scala) "ScalaChoice" |
  constant "nondeterministic_simulates" \<rightharpoonup> (Scala) "ScalaNondeterministicSimulates" |
  constant "directly_subsumes" \<rightharpoonup> (Scala) "ScalaDirectlySubsumes"

(*primrec fset_of_list_code :: "'a list \<Rightarrow> 'a fset" where
  "fset_of_list_code [] = {||}" |
  "fset_of_list_code (h#t) = finsert h (fset_of_list_code t)"

lemma [code]: "fset_of_list x = fset_of_list_code x"
proof(induct x)
case Nil
  then show ?case by simp
next
case (Cons a x)
  then show ?case
    by simp
qed

lemma[code]: "(bot::'a fset) = {||}"
  by simp

lemma [code]: "minus (s::'a fset) (s'::'a fset) = ffilter (\<lambda>x. x |\<notin>| s') s"
  apply (simp add: minus_fset_def ffilter_def fmember_def set_equiv Abs_fset_inverse)
  by auto

lemma [code]: "sup s s' = s |\<union>| s'"
  by simp

lemma [code]: "finsert e s = s |\<union>| {|e|}"
  by (simp add: sup_fset_def Abs_fset_inverse finsert_equiv)

lemma [code]: "ffilter f s = ffUnion (fimage (\<lambda>x. if f x then {|x|} else {||}) s)"
  apply (simp add: ffilter_def ffUnion_def fset_both_sides Abs_fset_inverse)
  by auto

lemma [code]: "ffUnion s = ffold (|\<union>|) {||} s"
proof(induct s)
  case empty
  then show ?case
    by (simp add: ffold_def)
next
  have ffold_finsert: "\<forall>x s. ffold (|\<union>|) {||} (finsert x s) = ffold (|\<union>|) x s"
    by (simp add: comp_fun_idem.ffold_finsert_idem2 comp_fun_idem_sup)
  case (insert x s)
  then show ?case
    apply simp
    apply (simp add: ffold_finsert)
    by (metis comp_fun_idem.ffold_finsert_idem comp_fun_idem_sup ffold_finsert)
qed*)

export_code learn in Scala
  file "../../src/Inference.scala"

end