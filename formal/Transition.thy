theory Transition
imports GExp
begin

type_synonym label = String.literal
type_synonym arity = nat
type_synonym inputs = "value list"
type_synonym outputs = "value option list"
type_synonym output_function = "aexp"
type_synonym update_function = "(nat \<times> aexp)"
type_synonym updates = "update_function list"

text_raw\<open>\snip{transitiontype}{1}{2}{%\<close>
record transition =
  Label :: label
  Arity :: nat
  Guard :: "gexp list"
  Outputs :: "aexp list"
  Updates :: updates
text_raw\<open>}%endsnip\<close>

lemma transition_equality: "((x::transition) = y) = ((Label x) = (Label y) \<and>
                                (Arity x) = (Arity y) \<and>
                                (Guard x) = (Guard y) \<and>
                                (Outputs x) = (Outputs y) \<and>
                                (Updates x) = (Updates y))"
  by auto

lemma unequal_labels[simp]: "Label t1 \<noteq> Label t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma unequal_arities[simp]: "Arity t1 \<noteq> Arity t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

definition same_structure :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "same_structure t1 t2 = (Label t1 = Label t2 \<and>
                           Arity t1 = Arity t2 \<and>
                           list_all (\<lambda>(g1, g2). gexp_same_structure g1 g2) (zip (Guard t1) (Guard t2)))"

definition enumerate_inputs :: "transition \<Rightarrow> nat set" where
  "enumerate_inputs t = (\<Union> (set (map enumerate_gexp_inputs (Guard t)))) \<union>
                        (\<Union> (set (map enumerate_aexp_inputs (Outputs t)))) \<union>
                        (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_inputs u) (Updates t))))"

definition enumerate_inputs_list :: "transition \<Rightarrow> nat list" where
  "enumerate_inputs_list t = (fold (@) (map enumerate_gexp_inputs_list (Guard t)) []) @
                             (fold (@) (map enumerate_aexp_inputs_list (Outputs t)) []) @
                             (fold (@) (map (\<lambda>(_, u). enumerate_aexp_inputs_list u) (Updates t)) [])"

lemma fold_enumerate_aexp_inputs_list_pairs: "set (fold (@) (map (\<lambda>(uu, y). enumerate_aexp_inputs_list y) U) []) = (\<Union>(uu, y)\<in>set U. enumerate_aexp_inputs y)"
  by (simp add: enumerate_aexp_inputs_list fold_append_concat_rev inf_sup_aci(5) split_def)

lemma fold_enumerate_aexp_inputs_list: "set (fold (@) (map enumerate_aexp_inputs_list P) []) = (\<Union>x\<in>set P. enumerate_aexp_inputs x)"
  by (simp add: enumerate_aexp_inputs_list fold_append_concat_rev inf_sup_aci(5) split_def)

lemma fold_enumerate_gexp_inputs_list: "set (fold (@) (map enumerate_gexp_inputs_list G) []) = (\<Union>x\<in>set G. enumerate_gexp_inputs x)"
    by (simp add: enumerate_gexp_inputs_list fold_append_concat_rev inf_sup_aci(5) split_def)

lemma set_enumerate_inputs_list: "enumerate_inputs t = set (enumerate_inputs_list t)"
  apply (simp add: enumerate_inputs_list_def enumerate_inputs_def)
  apply (simp add: fold_enumerate_aexp_inputs_list fold_enumerate_aexp_inputs_list_pairs)
  apply (simp add: fold_enumerate_gexp_inputs_list)
  by auto

lemma set_list_not_empty: "(set l \<noteq> {}) = (l \<noteq> [])"
  by simp

lemma max_set_nat_list: "(l:: nat list) \<noteq> [] \<Longrightarrow> Max (set l) = foldr max l 0"
proof(induct l)
case Nil
  then show ?case
    by simp
next
case (Cons a l)
  then show ?case
    apply simp
    by (metis List.finite_set Max_insert Max_singleton fold.simps(1) fold_simps(1) foldr.simps(1) max_0R set_empty)
qed

definition max_input :: "transition \<Rightarrow> nat option" where
  "max_input t = (if enumerate_inputs t = {} then None else Some (Max (enumerate_inputs t)))"

definition enumerate_registers :: "transition \<Rightarrow> nat set" where
  "enumerate_registers t = (\<Union> (set (map enumerate_gexp_regs (Guard t)))) \<union>
                           (\<Union> (set (map enumerate_aexp_regs (Outputs t)))) \<union>
                           (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_regs u) (Updates t)))) \<union>
                           (\<Union> (set (map (\<lambda>(r, _). enumerate_aexp_regs (V (R r))) (Updates t))))"

definition enumerate_registers_list :: "transition \<Rightarrow> nat list" where
  "enumerate_registers_list t = (fold (@) (map enumerate_gexp_regs_list (Guard t)) []) @
                                (fold (@) (map enumerate_aexp_regs_list (Outputs t)) []) @
                                (fold (@) (map (\<lambda>(_, u). enumerate_aexp_regs_list u) (Updates t)) []) @
                                (fold (@) (map (\<lambda>(r, _). enumerate_aexp_regs_list (V (R r))) (Updates t)) [])"

lemma fold_enumerate_aexp_regs_list_pairs: "set (fold (@) (map (\<lambda>(uu, y). enumerate_aexp_regs_list y) U) []) = (\<Union>(uu, y)\<in>set U. enumerate_aexp_regs y)"
  by (simp add: enumerate_aexp_regs_list fold_append_concat_rev inf_sup_aci(5) split_def)

lemma fold_enumerate_aexp_regs_list_pairs_2: "set (fold (@) (map (\<lambda>(r, uu). [r]) (Updates t)) []) = (\<Union>x\<in>set (Updates t). case x of (r, uu) \<Rightarrow> {r})"
    by (simp add: enumerate_aexp_regs_list fold_append_concat_rev inf_sup_aci(5) split_def)

lemma fold_enumerate_aexp_regs_list: "set (fold (@) (map enumerate_aexp_regs_list P) []) = (\<Union>x\<in>set P. enumerate_aexp_regs x)"
    by (simp add: enumerate_aexp_regs_list fold_append_concat_rev inf_sup_aci(5) split_def)

lemma fold_enumerate_gexp_regs_list: "set (fold (@) (map enumerate_gexp_regs_list G) []) = (\<Union>x\<in>set G. enumerate_gexp_regs x)"
    by (simp add: enumerate_gexp_regs_list fold_append_concat_rev inf_sup_aci(5) split_def)

lemma set_enumerate_registers_list: "enumerate_registers t = set (enumerate_registers_list t)"
  apply (simp add: enumerate_registers_list_def enumerate_registers_def)
  apply (simp add: fold_enumerate_aexp_regs_list fold_enumerate_aexp_regs_list_pairs fold_enumerate_aexp_regs_list_pairs_2)
  apply (simp add: fold_enumerate_gexp_regs_list)
  by auto

definition max_reg :: "transition \<Rightarrow> nat option" where
  "max_reg t = (if enumerate_registers t = {} then None else Some (Max (enumerate_registers t)))"

definition valid_transition :: "transition \<Rightarrow> bool" where
  "valid_transition t = (case max_input t of None \<Rightarrow> Arity t = 0 | Some x \<Rightarrow> x < Arity t)"

lemma not_leq_gt_set: "(\<forall>x\<in>(s::('a::linorder) set). \<not> a \<le> x) = (\<forall>x\<in>s. a > x)"
  by auto

lemma fold_append_Union: "(\<Union>x\<in>set G. set (enumerate_gexp_inputs_list x)) = set (fold (@) (map enumerate_gexp_inputs_list G) [])"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    by (simp add: fold_append_concat_rev inf_sup_aci(5))
qed

lemma map_enumerate_gexp_inputs: 
  "(Max (\<Union> (set (map enumerate_gexp_inputs G))) =
   (fold (max) (fold (@) (map enumerate_gexp_inputs_list G) []) 0)) \<or> ((\<Union> (set (map enumerate_gexp_inputs G)) = {}))"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply simp
    apply (simp add: enumerate_gexp_inputs_list)
    apply (simp add: fold_append_Union)
    by (metis (no_types, lifting) List.finite_set Max.set_eq_fold Max_insert fold_append_concat_rev inf_sup_aci(5) list.simps(15) max_0L set_append set_empty sup.left_idem sup_bot.right_neutral)
qed

end
