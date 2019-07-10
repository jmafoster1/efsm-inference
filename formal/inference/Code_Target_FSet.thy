theory Code_Target_FSet
imports "../FSet_Utils"
begin

code_datatype fset_of_list

lemma fprod_code [code]:
  "fprod (fset_of_list xs) (fset_of_list ys) = fset_of_list [(x, y). x \<leftarrow> xs, y \<leftarrow> ys]"
  apply (simp add: fprod_def fset_of_list_def fset_both_sides Abs_fset_inverse)
  by auto

lemma fminus_fset_filter[code]: "fset_of_list A -  xs = fset_of_list (filter (\<lambda>x. x |\<notin>| xs) A)"
  by auto

lemma sup_fset_foldr: "f1 |\<union>| (fset_of_list f2) = foldr finsert f2 f1"
proof(induct f2)
  case Nil
  then show ?case
    by simp
next
  case (Cons a f2)
  then show ?case
    by (simp add: finsert_def sup_fset_def fset_both_sides Abs_fset_inverse)
qed

lemma sup_fset_fold: "f1 |\<union>| (fset_of_list f2) = fold finsert f2 f1"
  by (metis foldr_conv_fold fset_of_list_rev rev_rev_ident sup_fset_foldr)

lemma sup_fset_fold_double[code]: "(fset_of_list f1) |\<union>| (fset_of_list f2) = fset_of_list (f1@f2)"
  by simp

lemma bot_fset[code]: "{||} = fset_of_list []"
  by simp

lemma fset_foldr: "fset (fset_of_list f) = foldr insert f {}"
proof(induct f)
  case Nil
  then show ?case
    by simp
next
  case (Cons a f)
  then show ?case
    by simp
qed

lemma fset_fold[code]: "fset (fset_of_list f) = fold insert f {}"
  using fset_of_list.rep_eq union_set_fold by fastforce

lemma finsert_cons[code]: "finsert a (fset_of_list as) = fset_of_list (a#as)"
  by simp

lemma ffilter_filter[code]: "ffilter f (fset_of_list as) = fset_of_list (List.filter f as)"
proof(induct as)
  case Nil
  then show ?case
    by auto
next
  case (Cons a as)
  then show ?case
    by auto
qed

lemma fimage_map[code]: "fimage f (fset_of_list as) = fset_of_list (List.map f as)"
proof(induct as)
  case Nil
  then show ?case
    by auto
next
  case (Cons a as)
  then show ?case
    by auto
qed

lemma ffUnion_foldr: "ffUnion (fset_of_list as) = foldr (|\<union>|) as {||}"
proof(induct as)
  case Nil
  then show ?case
    by auto
next
  case (Cons a as)
  then show ?case
    by auto
qed

lemma ffUnion_fold[code]: "ffUnion (fset_of_list as) = fold (|\<union>|) as {||}"
  by (simp add: fold_union_ffUnion)

lemma fmember[code]: "a |\<in>| (fset_of_list as) = List.member as a"
  by (simp add: fset_of_list_elem member_def)

lemma fthe_elem[code]: "fthe_elem (fset_of_list [x]) = x"
  by simp

lemma size[code]: "size (fset_of_list as) = length (remdups as)"
proof(induct as)
  case Nil
  then show ?case
    by simp
next
  case (Cons a as)
  then show ?case
    apply simp
    by (simp add: fset_of_list.rep_eq insert_absorb)
qed

lemma fMax_fold[code]: "fMax (fset_of_list (a#as)) = fold max as a"
  by (metis Max.set_eq_fold fMax.F.rep_eq fset_of_list.rep_eq)

lemma sorted_list_of_fset_sort[code]: "sorted_list_of_fset (fset_of_list as) = sort (remdups as)"
  by (metis fset_of_list.rep_eq sorted_list_of_fset.rep_eq sorted_list_of_set_sort_remdups)

lemma fremove_code[code]: "fremove a (fset_of_list A) = fset_of_list (filter (\<lambda>x. x \<noteq> a) A)"
  apply (simp add: fremove_def minus_fset_def ffilter_def fset_both_sides Abs_fset_inverse fset_of_list.rep_eq)
  by auto

lemma fsubseteq[code]: "(fset_of_list l) |\<subseteq>| A = List.list_all (\<lambda>x. x |\<in>| A) l"
proof(induct l)
case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by simp
qed

end