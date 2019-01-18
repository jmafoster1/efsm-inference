theory FSet_Utils
  imports "~~/src/HOL/Library/FSet"
begin

context includes fset.lifting begin
lift_definition fprod  :: "'a fset \<Rightarrow> 'b fset \<Rightarrow> ('a \<times> 'b) fset " (infixr "|\<times>|" 80) is "\<lambda>a b. fset a \<times> fset b"
  by simp

lift_definition fis_singleton :: "'a fset \<Rightarrow> bool" is "\<lambda>A. is_singleton (fset A)".
end
lemma fset_both_sides: "(Abs_fset s = f) = (fset (Abs_fset s) = fset f)"
  by (simp add: fset_inject)

lemma singleton_singleton [simp]: "fis_singleton {|a|}"
  by (simp add: fis_singleton_def)

lemma not_singleton_emty [simp]: "\<not>fis_singleton {||}"
  apply (simp add: fis_singleton_def)
  by (simp add: is_singleton_altdef)

lemma abs_fset_fiveton[simp]: "Abs_fset {a, b, c, d, e} = {|a, b, c, d, e|}"
  by (metis bot_fset.rep_eq finsert.rep_eq fset_inverse)

lemma abs_fset_fourton[simp]: "Abs_fset {a, b, c, d} = {|a, b, c, d|}"
  by (metis bot_fset.rep_eq finsert.rep_eq fset_inverse)

lemma abs_fset_tripleton[simp]: "Abs_fset {a, b, c} = {|a, b, c|}"
  by (metis bot_fset.rep_eq finsert.rep_eq fset_inverse)

lemma abs_fset_doubleton[simp]: "Abs_fset {a, b} = {|a, b|}"
  by (metis bot_fset.rep_eq finsert.rep_eq fset_inverse)

lemma abs_fset_singleton[simp]: "Abs_fset {a} = {|a|}"
  by (metis bot_fset.rep_eq finsert.rep_eq fset_inverse)

lemma abs_fset_empty[simp]: "Abs_fset {} = {||}"
  by (simp add: bot_fset_def)

lemma fprod_empty[simp]: "\<forall>a. fprod {||} a = {||}"
  by (simp add: fprod_def)

lemma fprod_empty_2[simp]: "\<forall>a. fprod a {||} = {||}"
  by (simp add: fprod_def ffUnion_def)

lemma set_equiv: "(f1 = f2) = (fset f1 = fset f2)"
  by (simp add: fset_inject)

lemma fprod_equiv: "(fset (f |\<times>| f') = s) = (((fset f) \<times> (fset f')) = s)"
  by (simp add: fprod_def Abs_fset_inverse)

lemma finsert_equiv: "(finsert e f = f') = (insert e (fset f) = (fset f'))"
  by (simp add: finsert_def fset_both_sides Abs_fset_inverse)

lemma filter_elements: "x |\<in>| Abs_fset (Set.filter f (fset s)) = (x \<in> (Set.filter f (fset s)))"
  by (metis ffilter.rep_eq fset_inverse notin_fset)
end