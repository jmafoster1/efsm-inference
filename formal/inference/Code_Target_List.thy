theory Code_Target_List
imports Main
begin

declare enumerate_eq_zip [code]
declare foldr_conv_foldl [code]
declare map_filter_map_filter [code_unfold del]
declare ListMem_iff [code]

(* Use the native implementations of list functions *)
definition "flatmap l f = List.maps f l"

lemma [code]:"List.maps f l = flatmap l f"
  by (simp add: flatmap_def)

definition "map_code l f = List.map f l"
lemma [code]:"List.map f l = map_code l f"
  by (simp add: map_code_def)

lemma [code]: "removeAll a l = filter (\<lambda>x. x \<noteq> a) l"
  by (induct l arbitrary: a) simp_all

definition "filter_code l f = List.filter f l"

lemma [code]: "List.filter l f = filter_code f l"
  by (simp add: filter_code_def)

definition all :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "all l f = list_all f l"

lemma [code]: "list_all f l = all l f"
  by (simp add: all_def)

definition ex :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "ex l f = list_ex f l"

lemma [code]: "list_ex f l = ex l f"
  by (simp add: ex_def)

lemma fold_conv_foldl [code]: "fold f xs s = foldl (\<lambda>x s. f s x) s xs"
  by (simp add: foldl_conv_fold)

lemma code_list_eq [code]: "HOL.equal xs ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>(x,y) \<in> set (zip xs ys). x = y)"
  apply (simp add: HOL.equal_class.equal_eq)
  by (simp add: Ball_set list_eq_iff_zip_eq)

code_printing
  constant Cons \<rightharpoonup> (Scala) "_::_"
  | constant rev \<rightharpoonup> (Scala) "_.reverse"
  | constant List.member \<rightharpoonup> (Scala) "_ contains _"
  | constant "List.remdups" \<rightharpoonup> (Scala) "_.distinct"
  | constant "List.length" \<rightharpoonup> (Scala) "Nat.Nata(_.length)"
  | constant "zip" \<rightharpoonup> (Scala) "(_ zip _)"
  | constant "flatmap" \<rightharpoonup> (Scala) "_.par.flatMap((_)).toList"
  | constant "List.null" \<rightharpoonup> (Scala) "_.isEmpty"
  | constant "map_code" \<rightharpoonup> (Scala) "_.par.map((_)).toList"
  | constant "filter_code" \<rightharpoonup> (Scala) "_.par.filter((_)).toList"
  | constant "all" \<rightharpoonup> (Scala) "_.par.forall((_))"
  | constant "ex" \<rightharpoonup> (Scala) "_.par.exists((_))"
  | constant "nth" \<rightharpoonup> (Scala) "_(Code'_Numeral.integer'_of'_nat((_)).toInt)"
  | constant "foldl" \<rightharpoonup> (Scala) "Dirties.foldl"


end