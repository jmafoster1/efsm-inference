theory Code_Target_Set
imports Main
begin

code_datatype set
declare List.union_coset_filter [code del]
declare insert_code [code del]
declare remove_code [code del]
declare card_coset_error [code del]
declare coset_subseteq_set_code [code del]
declare eq_set_code(1) [code del]
declare eq_set_code(2) [code del]
declare eq_set_code(4) [code del]
declare List.subset_code [code del]
declare inter_coset_fold [code del]
declare subset_eq [code]

(* Get rid of that one unnamed lemma *)
lemma [code del]: "x \<in> List.coset xs \<longleftrightarrow> \<not> List.member xs x"
  by (simp add: member_def)

lemma sup_set_append [code]: "(set x) \<union> (set y) = set (x @ y)"
  by simp

declare product_concat_map [code]

end