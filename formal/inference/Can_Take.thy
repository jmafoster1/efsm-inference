theory Can_Take
imports Inference
begin

unbundle finfun_syntax

definition finfun2pairs :: "('a :: linorder) \<Rightarrow>f 'b \<Rightarrow> ('a \<times> 'b) list" where
  "finfun2pairs f = (let keys = finfun_to_list f in zip keys (map (\<lambda>k. f $ k) keys))"

fun null_guard :: "gexp \<Rightarrow> bool" where
  "null_guard (Null _) = True" |
  "null_guard (Nor g1 g2) = (null_guard g1 \<or> null_guard g2)" |
  "null_guard _ = False"

definition max_input :: "gexp list \<Rightarrow> nat option" where
  "max_input g = (fold max (map (\<lambda>g. GExp.max_input g) g) None)"

lemma max_input_cons: "max_input (a # G) = max (GExp.max_input a) (max_input G)"
  apply (simp add: max_input_def)
proof -
  have "foldr max (GExp.max_input a # rev (map_tailrec GExp.max_input G)) None = foldr max (rev (None # map_tailrec GExp.max_input G)) (GExp.max_input a)"
    by (metis (no_types) Max.set_eq_fold comp_def fold.simps(2) fold_conv_foldr foldr_conv_fold list.set(2) max.commute set_rev)
  then show "fold max (map GExp.max_input G) (max (GExp.max_input a) None) = max (GExp.max_input a) (fold max (map GExp.max_input G) None)"
    by (simp add: fold_conv_foldr map_eq_map_tailrec max.commute)
qed

definition max_reg :: "gexp list \<Rightarrow> nat option" where
  "max_reg g = (fold max (map (\<lambda>g. GExp.max_reg g) g) None)"

lemma max_reg_cons: "max_reg (a # G) = max (GExp.max_reg a) (max_reg G)"
  apply (simp add: max_reg_def)
  by (metis (no_types, lifting) List.finite_set Max.insert Max.set_eq_fold fold.simps(1) id_apply list.simps(15) max.assoc set_empty)

lemma max_none: "max None x = x"
  by (meson less_option.elims(2) linorder_not_le max.absorb2 option.distinct(1))

lemma max_lt_val: "max (GExp.max_input a) (Can_Take.max_input G) = Some i \<Longrightarrow> (GExp.max_input a) \<le> Some i"
  by (metis max.cobounded1)

lemma Max_set_fold: "l \<noteq> [] \<Longrightarrow> Max (set (l)) = fold max l (hd l)"
proof(induct l)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a l)
  then show ?case
    using Max.set_eq_fold by auto
qed

lemma max_union: "x \<noteq> [] \<Longrightarrow> y \<noteq> [] \<Longrightarrow> Max (set x \<union> set y) = max (Max (set x)) (Max (set y))"
  by (simp add: Max.union)

lemma in_not_empty: "x \<in> s \<Longrightarrow> s \<noteq> {}"
  by auto

lemma gexp_max_input_nor_aux: "x \<in> set (s1) \<Longrightarrow>
       Some (Max (set (s1) \<union> set (s2))) \<noteq>
       max (Some (Max (set (s1)))) (Some (Max (set (s2)))) \<Longrightarrow>
       xa \<in> set (s2) \<Longrightarrow> False"
  using in_not_empty[of x "set (s1)"]
  using in_not_empty[of xa "set (s2)"]
  apply simp
  apply (simp add: max_union Max_set_fold)
  by (metis less_option.simps(4) linorder_not_le max_def)

lemma gexp_max_input_nor: "GExp.max_input (Nor g1 g2) = max (GExp.max_input g1) (GExp.max_input g2)"
  apply (simp add: GExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  using enumerate_gexp_inputs_list gexp_max_input_nor_aux by fastforce

lemma gexp_max_reg_nor: "GExp.max_reg (Nor g1 g2) = max (GExp.max_reg g1) (GExp.max_reg g2)"
  apply (simp add: GExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  by (metis enumerate_gexp_regs_list gexp_max_input_nor_aux)

lemma max_input_Eq: "GExp.max_input (Eq a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def GExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  using enumerate_aexp_inputs_list gexp_max_input_nor_aux by fastforce

lemma max_reg_Eq: "GExp.max_reg (Eq a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def GExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  by (metis enumerate_aexp_regs_list gexp_max_input_nor_aux)

lemma max_input_Gt: "GExp.max_input (Gt a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def GExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  by (metis Un_commute enumerate_aexp_inputs_list gexp_max_input_nor_aux)

lemma max_reg_Gt: "GExp.max_reg (Gt a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def GExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  by (metis enumerate_aexp_regs_list gexp_max_input_nor_aux inf_sup_aci(5))

lemma max_input_Plus: "AExp.max_input (Plus a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  using enumerate_aexp_inputs_list gexp_max_input_nor_aux by fastforce

lemma max_input_Minus: "AExp.max_input (Minus a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  using enumerate_aexp_inputs_list gexp_max_input_nor_aux by fastforce

lemma max_reg_Minus: "AExp.max_reg (Minus a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  by (metis enumerate_aexp_regs_list gexp_max_input_nor_aux)

lemma max_reg_Plus: "AExp.max_reg (Plus a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_none)
   apply (simp add: max.commute max_none)
  by (metis enumerate_aexp_regs_list gexp_max_input_nor_aux)

lemma max_input_I: "AExp.max_input (V (vname.I i)) = Some i"
  by (simp add: AExp.max_input_def)

definition ensure_not_null :: "nat \<Rightarrow> gexp list" where
  "ensure_not_null n = map (\<lambda>i. gNot (Null (V (vname.I i)))) [0..<n]"

lemma not_null_length: "apply_guards (ensure_not_null a) (join_ir ia r) \<Longrightarrow> length ia \<ge> a"
proof(induct a)
  case 0
  then show ?case
    by simp
next
  case (Suc a)
  then show ?case
    apply (simp add: ensure_not_null_def apply_guards_append)
    apply (simp add: apply_guards_singleton maybe_negate_true maybe_or_false)
    apply (case_tac "join_ir ia r (vname.I a) = None")
     apply simp
    by (simp add: Suc_leI datastate(1) input2state_not_None)
qed

lemma gexp_max_input_null: "GExp.max_input (Null x) = AExp.max_input x"
  by (simp add: AExp.max_input_def GExp.max_input_def)

lemma gexp_max_reg_null: "GExp.max_reg (Null x) = AExp.max_reg x"
  by (simp add: AExp.max_reg_def GExp.max_reg_def)

lemma aval_take: "AExp.max_input x < Some a \<Longrightarrow> aval x (join_ir i r) = aval x (join_ir (take a i) r)"
proof(induct x)
  case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    apply (simp add: join_ir_def max_input_I)
    apply (metis leI nat_less_le take_all test_aux_aux_2)
    using enumerate_aexp_inputs.simps(3) enumerate_aexp_inputs_empty_input_unconstrained input_unconstrained_aval_input_swap by blast
next
  case (Plus x1 x2)
  then show ?case
    by (simp add: max_input_Plus)
next
  case (Minus x1 x2)
  then show ?case
    by (simp add: max_input_Minus)
qed

lemma gval_take: "GExp.max_input g < Some a \<Longrightarrow>
    gval g (join_ir i r) = gval g (join_ir (take a i) r)"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis apply_guards(7) aval_take max.strict_boundedE max_input_Eq)
next
  case (Gt x1a x2)
  then show ?case
    by (metis apply_guards(6) aval_take max.strict_boundedE max_input_Gt)
next
  case (Nor g1 g2)
  then show ?case
    by (simp add: maybe_not_eq gexp_max_input_nor)
next
  case (Null x)
  then show ?case
    by (metis apply_guards(9) aval_take gexp_max_input_null)
qed

lemma apply_guards_take_or_pad: "Can_Take.max_input G < Some a \<Longrightarrow>
       apply_guards G (join_ir i r) \<Longrightarrow>
       apply_guards (ensure_not_null a) (join_ir i r) \<Longrightarrow>
       apply_guards G (join_ir (take_or_pad i a) r)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: max_input_def)
next
  case (Cons g gs)
  then show ?case
    apply (simp add: apply_guards_cons max_input_cons)
    using not_null_length[of a i r]
    apply simp
    apply (simp add: take_or_pad_def)
    by (metis gval_take)
qed

lemma satisfiable_can_take:
  "max_input (Guard t) < Some (Arity t) \<Longrightarrow>
   satisfiable_list ((Guard t) @ ensure_not_null (Arity t)) \<Longrightarrow>
   \<exists>i r. can_take_transition t i r"
  apply (simp add: can_take_transition_def satisfiable_list_def satisfiable_def fold_apply_guards
                   apply_guards_append can_take_def del: fold_append)
  apply clarify
  apply (rule_tac x="take_or_pad i (Arity t)" in exI)
  apply standard
   apply (simp add: length_take_or_pad)
  apply (rule_tac x=r in exI)
  by (simp add: apply_guards_take_or_pad)

lemma max_is_none: "(max x y = None) = (x = None \<and> y = None)"
  by (metis max.commute max_def max_none)

lemma aval_no_reg_swap_regs:
  "AExp.max_input x < Some a \<Longrightarrow>
   AExp.max_reg x = None \<Longrightarrow>
   aval x (join_ir i ra) = aval x (join_ir (take a i) r)"
proof(induct x)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply (metis aval_take enumerate_aexp_regs.simps(3) enumerate_aexp_regs_empty_reg_unconstrained input_unconstrained_aval_register_swap)
    by (simp add: AExp.max_reg_def)
next
  case (Plus x1 x2)
  then show ?case
    by (simp add: max_input_Plus max_is_none max_reg_Plus)
next
  case (Minus x1 x2)
  then show ?case
    by (simp add: max_input_Minus max_is_none max_reg_Minus)
qed

lemma gval_no_reg_swap_regs:
  "GExp.max_input g < Some a \<Longrightarrow>
   GExp.max_reg g = None \<Longrightarrow>
   gval g (join_ir i ra) = gval g (join_ir (take a i) r)"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis apply_guards(7) aval_no_reg_swap_regs max.strict_boundedE max_input_Eq max_is_none max_reg_Eq)
next
  case (Gt x1a x2)
  then show ?case
    by (metis apply_guards(6) aval_no_reg_swap_regs max.strict_boundedE max_input_Gt max_is_none max_reg_Gt)
next
  case (Nor g1 g2)
  then show ?case
    by (simp add: gexp_max_input_nor gexp_max_reg_nor max_is_none)
next
  case (Null x)
  then show ?case
    by (metis apply_guards(9) aval_no_reg_swap_regs gexp_max_input_null gexp_max_reg_null)
qed

lemma apply_guards_no_reg_swap_regs:
  "max_reg G = None \<Longrightarrow>
   max_input G < Some a \<Longrightarrow>
   apply_guards G (join_ir i ra) \<Longrightarrow>
   apply_guards (ensure_not_null a) (join_ir i ra) \<Longrightarrow>
   apply_guards G (join_ir (take_or_pad i a) r)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: max_input_def)
next
  case (Cons g gs)
  then show ?case
    by (metis apply_guards_cons gval_no_reg_swap_regs max.strict_boundedE max_input_cons max_is_none max_reg_cons not_null_length take_or_pad_def)
qed

lemma can_take_satisfiable:
  "max_reg (Guard t) = None \<Longrightarrow>
   max_input (Guard t) < Some (Arity t) \<Longrightarrow>
   satisfiable_list ((Guard t) @ ensure_not_null (Arity t)) \<Longrightarrow>
   \<exists>i. can_take_transition t i r"
  apply (simp add: can_take_transition_def satisfiable_list_def satisfiable_def fold_apply_guards
                   apply_guards_append can_take_def del: fold_append)
  apply clarify
  apply (rule_tac x="take_or_pad i (Arity t)" in exI)
  apply standard
   apply (simp add: length_take_or_pad)
  by (simp add: apply_guards_no_reg_swap_regs)

definition simple_mutex :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "simple_mutex t t' = (max_reg (Guard t) = None \<and>
     max_input (Guard t) < Some (Arity t) \<and>
     satisfiable_list ((Guard t) @ ensure_not_null (Arity t)) \<and>
     Label t = Label t' \<and>
     Arity t = Arity t' \<and>
     \<not> choice t' t)"

lemma simple_mutex_direct_subsumption:
  "simple_mutex t t' \<Longrightarrow>
   \<not> directly_subsumes e e' s s' t' t"
  apply (rule cant_directly_subsume)
  apply (rule allI)
  apply (simp add: simple_mutex_def)
  by (metis can_take_satisfiable no_choice_no_subsumption)

end