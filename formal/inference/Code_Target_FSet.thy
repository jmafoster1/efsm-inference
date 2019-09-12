theory Code_Target_FSet
  imports "../FSet_Utils"
    "HOL-ex.Quicksort"
"Tail_Recursive_Functions.CaseStudy1"
begin

code_datatype fset_of_list

declare FSet.fset_of_list.rep_eq [code]

lemma fprod_code [code]:
  "fprod (fset_of_list xs) (fset_of_list ys) = fset_of_list [(x, y). x \<leftarrow> xs, y \<leftarrow> ys]"
  apply (simp add: fprod_def fset_of_list_def fset_both_sides Abs_fset_inverse)
  by auto

lemma fminus_fset_filter [code]: "fset_of_list A -  xs = fset_of_list (filter (\<lambda>x. x |\<notin>| xs) A)"
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

lemma sup_fset_fold [code]: "f1 |\<union>| (fset_of_list f2) = fold finsert f2 f1"
  by (metis foldr_conv_fold fset_of_list_rev rev_rev_ident sup_fset_foldr)

lemma sup_fset_fold_double [code]: "(fset_of_list f1) |\<union>| (fset_of_list f2) = fset_of_list (f1@f2)"
  by simp

lemma bot_fset [code]: "{||} = fset_of_list []"
  by simp

lemma finsert_cons [code]: "finsert a (fset_of_list as) = fset_of_list (a#as)"
  by simp

lemma ffilter_filter [code]: "ffilter f (fset_of_list as) = fset_of_list (List.filter f as)"
proof(induct as)
  case Nil
  then show ?case
    by auto
next
  case (Cons a as)
  then show ?case
    by auto
qed

lemma fimage_map [code]: "fimage f (fset_of_list as) = fset_of_list (List.map f as)"
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

lemma ffUnion_fold [code]: "ffUnion (fset_of_list as) = fold (|\<union>|) as {||}"
  by (simp add: fold_union_ffUnion)

lemma fmember [code]: "a |\<in>| (fset_of_list as) = List.member as a"
  by (simp add: fset_of_list_elem member_def)

lemma fthe_elem [code]: "fthe_elem (fset_of_list [x]) = x"
  by simp

lemma size [code]: "size (fset_of_list as) = length (remdups as)"
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

lemma fMax_fold [code]: "fMax (fset_of_list (a#as)) = fold max as a"
  by (metis Max.set_eq_fold fMax.F.rep_eq fset_of_list.rep_eq)

lemma sorted_list_of_fset_sort [code]: "sorted_list_of_fset (fset_of_list as) = sort (remdups as)"
  by (metis fset_of_list.rep_eq sorted_list_of_fset.rep_eq sorted_list_of_set_sort_remdups)

lemma fremove_code [code]: "fremove a (fset_of_list A) = fset_of_list (filter (\<lambda>x. x \<noteq> a) A)"
  apply (simp add: fremove_def minus_fset_def ffilter_def fset_both_sides Abs_fset_inverse fset_of_list.rep_eq)
  by auto

lemma fsubseteq [code]: "(fset_of_list l) |\<subseteq>| A = List.list_all (\<lambda>x. x |\<in>| A) l"
proof(induct l)
case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by simp
qed

lemma fsum_fold [code]: "fSum (fset_of_list l) = fold (+) (remdups l) 0"
proof(induct l)
case Nil
then show ?case 
  by (simp add: fsum.F.rep_eq fSum_def)
next
  case (Cons a l)
  then show ?case
    apply simp
    apply standard
     apply (simp add: finsert_absorb fset_of_list_elem)
    by (simp add: add.commute fold_plus_sum_list_rev fset_of_list.rep_eq fsum.F.rep_eq fSum_def)
qed

lemma code_fset_eq [code]: "HOL.equal X (fset_of_list Y) \<longleftrightarrow> size X = length (remdups Y) \<and> (\<forall>x |\<in>| X. List.member Y x)"
  apply (simp only: HOL.equal_class.equal_eq fset_eq_alt)
  apply (simp only: size)
  using fmember by fastforce

lemma [code]: "s |\<subset>| s' = (s |\<subseteq>| s' \<and> size s < size s')"
  apply standard
   apply (simp only: size_fsubset)
  by auto

lemma l_sorted_sorted: "l_sorted x = sorted x"
proof(induct x)
  case Nil
  then show ?case
  by simp
next
  case (Cons a x)
  then show ?case
    apply (cases x)
     apply simp
    by fastforce
qed

lemma sorted_lsort: "sorted (l_sort xs)"
proof -
  let ?X = "(xs, [], [])"
  have "l_sort_aux ?X \<in> l_sort_set ?X" by (rule l_sort_aux_set)
  moreover have "l_sort_inv_1 ?X" by (rule l_sort_input_1)
  ultimately have "l_sort_inv_1 (l_sort_aux ?X)" by (rule l_sort_invariance_1)
  hence "l_sorted (l_sort_out (l_sort_aux ?X))" by (rule l_sort_intro_1)
  moreover have "?X = l_sort_in xs" by (simp add: l_sort_in_def)
  ultimately show ?thesis by (simp add: l_sort_def l_sorted_sorted)
qed

lemma lcount_count: "l_count i l = count (mset l) i"
proof(induct l)
  case Nil
  then show ?case
    by (simp add: l_count_def)
next
  case (Cons a l)
  then show ?case
    by (simp add: l_count_def)
qed

lemma lcount_lsort: "l_count x (l_sort xs) = l_count x xs"
proof -
  let ?X = "(xs, [], [])"
  have "l_sort_aux ?X \<in> l_sort_set ?X" by (rule l_sort_aux_set)
  moreover have "l_sort_inv_2 x xs ?X" by (rule l_sort_input_2)
  ultimately have "l_sort_inv_2 x xs (l_sort_aux ?X)" by (rule l_sort_invariance_2)
  moreover have "l_sort_form (l_sort_aux ?X)" by (rule l_sort_form_aux)
  ultimately have "l_count x (l_sort_out (l_sort_aux ?X)) = l_count x xs"
   by (rule l_sort_intro_2)
  moreover have "?X = l_sort_in xs" by (simp add: l_sort_in_def)
  ultimately show ?thesis by (simp add: l_sort_def)
qed

lemma lsort_is_sort: "sort xs = l_sort xs"
  apply (rule properties_for_sort)
   apply (simp add: multiset_eq_iff lcount_count[symmetric] lcount_lsort)
  by (simp add: sorted_lsort)

lemma [code]: "sorted_list_of_fset (fset_of_list L) = l_sort (remdups L)"
  apply (simp add: sorted_list_of_fset_def sorted_list_of_set_def)
  by (metis fset_of_list.rep_eq lsort_is_sort sorted_list_of_set_def sorted_list_of_set_sort_remdups)

end