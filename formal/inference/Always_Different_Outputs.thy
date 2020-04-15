theory Always_Different_Outputs
imports Inference
begin

definition always_different_outputs :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "always_different_outputs t1 t2 = (\<forall>s. apply_outputs (Outputs t1) s \<noteq> apply_outputs (Outputs t2) s)"

definition restricting_guards :: "(vname gexp) list \<Rightarrow> vname \<Rightarrow> vname gexp list" where
  "restricting_guards G v = filter (\<lambda>g. gexp_constrains g (V v)) G"

definition enumerate_gexp_list_inputs :: "vname gexp list \<Rightarrow> nat set" where
  "enumerate_gexp_list_inputs G = (\<Union> (set (map enumerate_gexp_inputs G)))"

lemma aexp_constrains_input_swap:
  "\<not> aexp_constrains a (V (I i)) \<Longrightarrow>
   aval a (join_ir ip r) = aval a (join_ir (ip[i := v]) r)"
proof(induct a)
  case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply (simp add: join_ir_def)
     apply (metis input2state_not_None input2state_nth length_list_update nth_list_update_neq)
    by (simp add: join_ir_def)
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
next
  case (Times a1 a2)
  then show ?case 
    by simp
qed

lemma gexp_constrains_input_swap:
   "\<not> gexp_constrains a (V (I i)) \<Longrightarrow>
    gval a (join_ir ip r) = gval a (join_ir (ip[i := v]) r)"
  using unconstrained_variable_swap_gval
proof(induct a)
  case (Bc x)
  then show ?case
    by (simp add: unconstrained_variable_swap_gval)
next
  case (Eq x1a x2)
  then show ?case
    using aexp_constrains_input_swap by auto
next
  case (Gt x1a x2)
  then show ?case
    using aexp_constrains_input_swap by auto
(*next
  case (Null x)
  then show ?case
    using aexp_constrains_input_swap by auto
*)next
  case (In x1a x2)
  then show ?case 
    by (smt aexp_constrains_input_swap aval.simps gexp_constrains.simps gval.simps)
next
  case (Nor a1 a2)
  then show ?case
    by simp
qed

lemma no_restricting_guards_variable_swap:
  "length (restricting_guards G (I i)) = 0 \<Longrightarrow>
   apply_guards G (join_ir ip r) \<Longrightarrow>
   apply_guards G (join_ir (list_update ip i v) r)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp add: apply_guards_cons)
     apply (simp add: restricting_guards_def)
    apply (case_tac "gexp_constrains a (V (I i))")
     apply simp
    using gexp_constrains_input_swap by auto
qed

lemma every_input_enumerated: "x1 \<in> enumerate_gexp_list_inputs (Eq (V (I x1)) (L x1a) # G)"
  by (simp add: enumerate_gexp_list_inputs_def)

lemma restricting_guards_cons:
  "\<forall>i\<in>enumerate_gexp_list_inputs (Eq (V (I x1)) (L x1a) # G). length (restricting_guards (Eq (V (I x1)) (L x1a) # G) (I i)) = 1 \<Longrightarrow>
   length (restricting_guards G (I x1)) = 0"
  by (simp add: enumerate_gexp_list_inputs_def Ball_def Bex_def restricting_guards_def)

fun get_input_pairs :: "vname gexp list \<Rightarrow> (nat \<times> value) list" where
  "get_input_pairs [] = []" |
  "get_input_pairs (Eq (V (I x1)) (L x1a) # G) = (x1, x1a)#(get_input_pairs G)" |
  "get_input_pairs (h#t) = get_input_pairs t"

lemma enumerate_gexp_list_inputs_cons: "enumerate_gexp_list_inputs (g # G) = enumerate_gexp_inputs g \<union> enumerate_gexp_list_inputs G"
  by (simp add: enumerate_gexp_list_inputs_def)

lemma "\<forall>i\<in>enumerate_gexp_list_inputs (g # G). length (restricting_guards (g # G) (I i)) = 1 \<Longrightarrow>
       \<forall>i\<in>enumerate_gexp_list_inputs G. length (restricting_guards G (I i)) = 1"
  apply (simp add: enumerate_gexp_list_inputs_def)
  oops

lemma "\<forall>i \<in> enumerate_gexp_list_inputs G. length (restricting_guards G (I i)) = 1 \<and> i < a \<Longrightarrow>
       \<forall>g \<in> set G. literal_args g \<Longrightarrow>
       \<exists>i. length i = a \<and> apply_guards G (join_ir i r)"
proof(induct G)
case Nil
  then show ?case
    by (simp add: Ex_list_of_length)
next
  case (Cons g G)
  then show ?case
    apply (simp add: apply_guards_cons enumerate_gexp_list_inputs_cons Ball_def)
    apply (erule_tac x=g in allE)
    apply simp
    apply (erule conjE)
    oops

end