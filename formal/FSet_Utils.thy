theory FSet_Utils
  imports "~~/src/HOL/Library/FSet"
begin

context includes fset.lifting begin
lift_definition fprod  :: "'a fset \<Rightarrow> 'b fset \<Rightarrow> ('a \<times> 'b) fset " (infixr "|\<times>|" 80) is "\<lambda>a b. fset a \<times> fset b"
  by simp

lift_definition fis_singleton :: "'a fset \<Rightarrow> bool" is "\<lambda>A. is_singleton (fset A)".
end

lemma fprod_subset: "x |\<subseteq>| x' \<and> y |\<subseteq>| y' \<Longrightarrow> x |\<times>| y |\<subseteq>| x' |\<times>| y'"
  apply (simp add: fprod_def less_eq_fset_def Abs_fset_inverse)
  by auto

lemma fimage_fprod: "(a, b) |\<in>| A |\<times>| B \<Longrightarrow> f a b |\<in>| (\<lambda>(x, y). f x y) |`| (A |\<times>| B)"
  by force

lemma fprod_singletons: "{|a|} |\<times>| {|b|} = {|(a, b)|}"
  apply (simp add: fprod_def)
  by (metis fset_inverse fset_simps(1) fset_simps(2))

lemma fset_both_sides: "(Abs_fset s = f) = (fset (Abs_fset s) = fset f)"
  by (simp add: fset_inject)

lemma Abs_ffilter: "(ffilter f s = s') = (Set.filter f (fset s) = (fset s'))"
  by (simp add: ffilter_def fset_both_sides Abs_fset_inverse)

lemma ffilter_empty: "ffilter f {||} = {||}"
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

lemma ffilter_finsert: "ffilter f (finsert a s) = (if f a then finsert a (ffilter f s) else (ffilter f s))"
  apply simp
  apply standard
   apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
   apply auto[1]
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

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

lemma singleton_equiv: "is_singleton s \<Longrightarrow> (the_elem s = i) = (s = {i})"
  by (meson is_singleton_the_elem the_elem_eq)

lemma sorted_list_of_empty [simp]: "sorted_list_of_fset {||} = []"
  by (simp add: sorted_list_of_fset_def)

lemma fmember_implies_member: "e |\<in>| f \<Longrightarrow> e \<in> fset f"
  by (simp add: fmember_def)

lemma ffilter_to_filter: "(ffilter f s = s') = (Set.filter f (fset s) = fset s')"
  by (metis ffilter.rep_eq fset_inject)

lemma fold_union_ffUnion: "fold (|\<union>|) l {||} = ffUnion (fset_of_list l)"
proof(induct l rule: rev_induct)
case Nil
  then show ?case by simp
next
  case (snoc a l)
  then show ?case
    by simp
qed

lemma filter_filter: "ffilter P (ffilter Q xs) = ffilter (\<lambda>x. Q x \<and> P x) xs"
  by auto
end