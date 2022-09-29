section\<open>Sets\<close>
text\<open>While the default code generator setup for sets works fine, it does not make for particularly
readable code. The reason for this is that the default setup needs to work with potentially infinite
sets. All of the sets we need to use here are finite so we present an alternative setup for the
basic set operations which generates much cleaner code.\<close>

theory Code_Target_Set
  imports "HOL-Library.Code_Cardinality"
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
declare Code_Cardinality.subset'_code(1) [code del]
declare Code_Cardinality.subset'_code(3) [code del]

declare subset_eq [code]

(* Get rid of that one unnamed lemma *)
lemma [code del]:
  "x \<in> List.coset xs \<longleftrightarrow> \<not> List.member xs x"
  by (simp add: member_def)

lemma sup_set_append[code]: "(set x) \<union> (set y) = set (remdups (x @ y))"
  by simp

declare product_concat_map [code]

lemma [code]: "insert x (set s) = (if x \<in> set s then set s else set (x#s))"
  apply (simp)
  by auto

lemma [code]: "(set X) \<subseteq> (set Y) = (List.list_all (\<lambda>x. List.member Y x) X)"
  apply (induct X)
   apply simp
  by (simp add: in_set_member)

end
