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

lemma max_reg_append_singleton: "max_reg (as@[bs]) = max (max_reg as) (max_reg [bs])"
  apply (simp add: max_reg_def)
  by (metis max.commute max_None_r)

lemma max_reg_append: "max_reg (as@bs) = max (max_reg as) (max_reg bs)"
proof(induct bs rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: Can_Take.max_reg_def max_None_r)
next
  case (snoc x xs)
  then show ?case
    by (metis append_assoc max.assoc max_reg_append_singleton)
qed

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
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  using enumerate_gexp_inputs_list gexp_max_input_nor_aux by fastforce

lemma gexp_max_reg_nor: "GExp.max_reg (Nor g1 g2) = max (GExp.max_reg g1) (GExp.max_reg g2)"
  apply (simp add: GExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis enumerate_gexp_regs_list gexp_max_input_nor_aux)

lemma max_input_Eq: "GExp.max_input (Eq a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def GExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  using enumerate_aexp_inputs_list gexp_max_input_nor_aux by fastforce

lemma max_reg_Eq: "GExp.max_reg (Eq a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def GExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis enumerate_aexp_regs_list gexp_max_input_nor_aux)

lemma max_input_Gt: "GExp.max_input (Gt a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def GExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis Un_commute enumerate_aexp_inputs_list gexp_max_input_nor_aux)

lemma max_reg_Gt: "GExp.max_reg (Gt a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def GExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis enumerate_aexp_regs_list gexp_max_input_nor_aux inf_sup_aci(5))

lemma max_input_Plus: "AExp.max_input (Plus a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  using enumerate_aexp_inputs_list gexp_max_input_nor_aux by fastforce

lemma max_input_Minus: "AExp.max_input (Minus a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  using enumerate_aexp_inputs_list gexp_max_input_nor_aux by fastforce

lemma max_reg_Minus: "AExp.max_reg (Minus a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis enumerate_aexp_regs_list gexp_max_input_nor_aux)

lemma max_reg_Plus: "AExp.max_reg (Plus a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis enumerate_aexp_regs_list gexp_max_input_nor_aux)

lemma max_input_I: "AExp.max_input (V (vname.I i)) = Some i"
  by (simp add: AExp.max_input_def)

definition ensure_not_null :: "nat \<Rightarrow> gexp list" where
  "ensure_not_null n = map (\<lambda>i. gNot (Null (V (vname.I i)))) [0..<n]"

lemma ensure_not_null_cons: "ensure_not_null (Suc a) = (ensure_not_null a)@[gNot (Null (V (I a)))]"
  by (simp add: ensure_not_null_def)

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

lemma gval_take_flip: "GExp.max_input g < Some a \<Longrightarrow>
    gval g (join_ir (take a i) r) = gval g (join_ir i r)"
  by (metis gval_take)

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
  by (metis max.commute max_def max_None_l)

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

(*
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
    by (metis apply_guards_cons gval_no_reg_swap_regs max.strict_boundedE max_input_cons
              max_is_none max_reg_cons not_null_length take_or_pad_def)
qed
*)

lemma max_reg_none_set: "(max_reg G = None) = (\<forall>g \<in> set G. GExp.max_reg g = None)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: max_reg_def)
next
  case (Cons a G)
  then show ?case
    by (simp add: max_reg_cons max_is_None)
qed

lemma no_reg_apply_guards_swap_regs: "max_reg G = None \<Longrightarrow> apply_guards G (join_ir i r) = apply_guards G (join_ir i r')"
  apply (simp add: apply_guards_def max_reg_none_set)
  by (metis no_reg_gval_swap_regs)

lemma max_reg_ensure_not_null: "max_reg (ensure_not_null a) = None"
proof(induct a)
  case 0
  then show ?case
    by (simp add: ensure_not_null_def max_reg_def)
next
  case (Suc a)
  then show ?case
    by (simp add: ensure_not_null_cons max_reg_append max_reg_def max_reg_gNot max_reg_Null max_reg_V)
qed

fun not_null :: "gexp \<Rightarrow> bool" where
  "not_null (Null x) = False" |
  "not_null (Nor x y) = (not_null x \<and> not_null y)" |
  "not_null _ = True"

lemma apply_guards_ensure_not_null: "length i \<ge> a \<Longrightarrow> apply_guards (ensure_not_null a) (join_ir i r)"
proof(induct a)
  case 0
  then show ?case
    by (simp add: ensure_not_null_def)
next
  case (Suc a)
  then show ?case
    apply (simp add: ensure_not_null_cons apply_guards_append apply_guards_singleton)
    by (simp add: join_ir_def input2state_nth)
qed

lemma apply_guards_pad: "apply_guards (ensure_not_null a) (join_ir (padding a) <>)"
proof(induct a)
  case 0
  then show ?case
    by (simp add: ensure_not_null_def)
next
  case (Suc a)
  then show ?case
    apply (simp add: ensure_not_null_cons apply_guards_append)
    apply standard
     apply (rule apply_guards_ensure_not_null)
     apply (simp add: length_padding)
    apply (simp add: apply_guards_singleton join_ir_def)
    by (metis input2state_nth le_imp_less_Suc length_padding linorder_not_le nat_less_le padding.simps(2))
qed

lemma max_input_Bc: "GExp.max_input (Bc x) = None"
  by (simp add: GExp.max_input_def)

lemma Some_lt_max: "Some a \<le> max (AExp.max_input A1) (AExp.max_input A2) \<Longrightarrow>
       Some a \<le> (AExp.max_input A1) \<or> Some a \<le> (AExp.max_input A2)"
  by linarith

lemma apply_guards_ensure_not_null_length: "apply_guards (ensure_not_null a) (join_ir i r) = (length i \<ge> a)"
  using apply_guards_ensure_not_null not_null_length by blast

lemma max_input_must_be_some: "(Some a \<le> AExp.max_input A ) \<Longrightarrow> (\<exists>a'. AExp.max_input A = Some a')"
  using not_le by fastforce

lemma need_aval_I_contra:
  "\<nexists>n'. aval (V (I a)) (join_ir i r) = Some (Num n') \<Longrightarrow>
   AExp.max_input A = Some a \<Longrightarrow>
   \<nexists>n. aval A (join_ir i r) = Some (Num n)"
proof(induct A)
  case (L x)
  then show ?case
    by (simp add: AExp.max_input_def)
next
  case (V x)
  then show ?case
    apply (cases x)
     defer
     apply (simp add: AExp.max_input_def)
    by (simp add: join_ir_def max_input_I)
next
case (Plus A1 A2)
  then show ?case
    apply (simp add: max_input_Plus value_plus_def MaybeArithInt_Not_Num MaybeArithInt_None)
    by (metis max_def_raw)
next
  case (Minus A1 A2)
  then show ?case
    apply (simp add: max_input_Minus value_minus_def MaybeArithInt_Not_Num MaybeArithInt_None)
    by (metis max_def_raw)
qed

lemma need_aval_I:
  "AExp.max_input A = Some a \<Longrightarrow>
   aval A (join_ir i r) = Some (Num n) \<Longrightarrow>
   \<exists>n'. aval (V (I a)) (join_ir i r) = Some (Num n')"
  using need_aval_I_contra by blast

lemma aval_input2state_within_bounds: "\<exists>n'. aval (V (I a)) (join_ir i r) = Some (Num n') \<Longrightarrow> a \<le> length i"
  apply (simp add: join_ir_def)
  using input2state_within_bounds less_imp_le_nat by blast

lemma aval_Num_apply_guards_not_null:
"Some a \<le> AExp.max_input A \<Longrightarrow>
 aval A (join_ir i r) = Some (Num n) \<Longrightarrow>
 apply_guards (ensure_not_null a) (join_ir i r)"
  using max_input_must_be_some[of a A]
  apply (simp add: apply_guards_ensure_not_null_length)
  apply clarify
  using need_aval_I aval_input2state_within_bounds
  using leD by fastforce

definition negate :: "gexp list \<Rightarrow> gexp" where
  "negate g = gNot (fold gAnd g (Bc True))"

lemma "\<not>\<^sub>? a \<or>\<^sub>? b = \<not>\<^sub>? (a \<or>\<^sub>? b)"
  by simp

lemma gval_fold_gAnd_append_singleton: "gval (fold gAnd (a @ [G]) (Bc True)) s = gval (fold gAnd a (Bc True)) s \<and>\<^sub>? gval G s "
  apply (simp add: fold_conv_foldr del: foldr.simps)
  by (simp only: foldr.simps comp_def gval_gAnd times_trilean_commutative)

lemma gval_fold_rev_true: "gval (fold gAnd (rev G) (Bc True)) s = true \<Longrightarrow> gval (fold gAnd G (Bc True)) s = true"
  by (simp add: fold_apply_guards apply_guards_def)

lemma gval_fold_not_invalid_all_valid_contra:
  "\<exists>g \<in> set G. gval g s = invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s = invalid"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp only: gval_fold_gAnd_append_singleton)
    apply simp
    using maybe_and_valid by blast
qed

lemma gval_fold_not_invalid_all_valid: "gval (fold gAnd G (Bc True)) s \<noteq> invalid \<Longrightarrow> \<forall>g \<in> set G. gval g s \<noteq> invalid"
  using gval_fold_not_invalid_all_valid_contra by blast

lemma all_gval_not_false: "(\<forall>g \<in> set G. gval g s \<noteq> false) = (\<forall>g \<in> set G. gval g s = true) \<or> (\<exists>g \<in> set G. gval g s = invalid)"
  using trilean.exhaust by auto

lemma must_have_one_false_contra: "\<forall>g \<in> set G. gval g s \<noteq> false \<Longrightarrow> gval (fold gAnd G (Bc True)) s \<noteq> false"
  using all_gval_not_false[of G s]
  apply simp
  apply (case_tac "(\<forall>g\<in>set G. gval g s = true)")
  using apply_guards_fold apply_guards_foldr gval_foldr_true apply auto[1]
  by (simp add: gval_fold_not_invalid_all_valid_contra)

lemma must_have_one_false: "gval (fold gAnd G (Bc True)) s = false \<Longrightarrow> \<exists>g \<in> set G. gval g s = false"
  using must_have_one_false_contra by blast

lemma all_valid_must_be_true_or_false: "(\<forall>g \<in> set G. gval g s \<noteq> invalid) = (\<forall>g \<in> set G. gval g s = true) \<or> (\<exists>g \<in> set G. gval g s = false)"
  using all_gval_not_false by auto

lemma all_valid_fold: "\<forall>g \<in> set G. gval g s \<noteq> invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s \<noteq> invalid"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_gAnd)
    by (simp add: maybe_and_invalid)
qed

lemma one_false_all_valid_false: "\<exists>g\<in>set G. gval g s = false \<Longrightarrow> \<forall>g\<in>set G. gval g s \<noteq> invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s = false"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_gAnd)
    apply (case_tac "gval x s = false")
     apply simp
     apply (case_tac "gval (foldr gAnd (rev xs) (Bc True)) s")
       apply simp
      apply simp
     apply simp
    using all_valid_fold
     apply (simp add: fold_conv_foldr)
    apply simp
    by (metis maybe_not.cases times_trilean.simps(5))
qed

lemma gval_fold_rev_false: "gval (fold gAnd (rev G) (Bc True)) s = false \<Longrightarrow> gval (fold gAnd G (Bc True)) s = false"
  using must_have_one_false[of "rev G" s]
        gval_fold_not_invalid_all_valid[of "rev G" s]
  by (simp add: one_false_all_valid_false)

lemma fold_invalid_means_one_invalid: "gval (fold gAnd G (Bc True)) s = invalid \<Longrightarrow> \<exists>g \<in> set G. gval g s = invalid"
  using all_valid_fold by blast

lemma gval_fold_rev_invalid: "gval (fold gAnd (rev G) (Bc True)) s = invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s = invalid"
  using fold_invalid_means_one_invalid[of "rev G" s]
  by (simp add: gval_fold_not_invalid_all_valid_contra)

lemma gval_fold_rev_equiv_fold: "gval (fold gAnd (rev G) (Bc True)) s =  gval (fold gAnd G (Bc True)) s"
  apply (cases "gval (fold gAnd (rev G) (Bc True)) s")
    apply (simp add: gval_fold_rev_true)
   apply (simp add: gval_fold_rev_false)
  by (simp add: gval_fold_rev_invalid)

lemma gval_fold_equiv_fold_rev: "gval (fold gAnd G (Bc True)) s = gval (fold gAnd (rev G) (Bc True)) s"
  by (simp add: gval_fold_rev_equiv_fold)

lemma gval_fold_gAnd: "gval (fold gAnd G (Bc True)) s = fold (\<and>\<^sub>?) (map (\<lambda>g. gval g s) G) true"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    by (simp only: foldr.simps comp_def gval_gAnd)
qed

lemma gval_fold_equiv_gval_foldr: "gval (fold gAnd G (Bc True)) s = gval (foldr gAnd G (Bc True)) s"
proof -
  have "gval (fold gAnd G (Bc True)) s = gval (fold gAnd (rev G) (Bc True)) s"
    using gval_fold_equiv_fold_rev by force
then show ?thesis
by (simp add: foldr_conv_fold)
qed

lemma gval_foldr_equiv_gval_fold: "gval (foldr gAnd G (Bc True)) s = gval (fold gAnd G (Bc True)) s"
  by (simp add: gval_fold_equiv_gval_foldr)

lemma gval_negate_cons: "gval (negate (a # G)) s = gval (gNot a) s \<or>\<^sub>? gval (negate G) s"
  apply (simp only: negate_def gval_gNot gval_fold_equiv_gval_foldr)
  by (simp only: foldr.simps comp_def gval_gAnd de_morgans_2)

lemma maybe_or_true: "(x \<or>\<^sub>? y = true) = ((x = true \<or> y = true) \<and> x \<noteq> invalid \<and> y \<noteq> invalid)"
  using plus_trilean.elims by blast

lemma not_true: "(x \<noteq> true) = (x = false \<or> x = invalid)"
  by (metis (no_types, lifting) maybe_not.cases trilean.distinct(1) trilean.distinct(3))

lemma negate_true_guard: "(gval (negate G) s = true) = (gval (fold gAnd G (Bc True)) s = false)"
  by (metis (no_types, lifting) gval_gNot maybe_double_negation maybe_not.simps(1) negate_def)

lemma maybe_or_true_not_invalid: "(true \<or>\<^sub>? x = true) = (x \<noteq> invalid)"
  by (simp add: maybe_or_true)

lemma gval_negate_not_invalid: "(gval (negate gs) (join_ir i ra) \<noteq> invalid) = (gval (fold gAnd gs (Bc True)) (join_ir i ra) \<noteq> invalid)"
  using gval_gNot maybe_not_invalid negate_def by auto

lemma gval_fold_swap_regs: "max_reg G = None \<Longrightarrow> gval (fold gAnd G (Bc True)) (join_ir i r) = gval (fold gAnd G (Bc True)) (join_ir i r')"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp only: gval_fold_equiv_gval_foldr foldr.simps comp_def gval_gAnd)
    by (metis (no_types, lifting) max_is_None max_reg_cons no_reg_gval_swap_regs)
qed

lemma negate_valid: "(\<not>\<^sub>? x \<noteq> invalid) = (x \<noteq> invalid)"
  by (simp add: maybe_not_invalid)

lemma maybe_and_false: "(x \<and>\<^sub>? y = false) = ((x = false \<or> y = false) \<and> x \<noteq> invalid \<and> y \<noteq> invalid)"
  using times_trilean.elims by blast

lemma gval_fold_cons: "gval (fold gAnd (g # gs) (Bc True)) s = gval g s \<and>\<^sub>? gval (fold gAnd gs (Bc True)) s"
  apply (simp only: apply_guards_fold gval_fold_equiv_gval_foldr)
  by (simp only: foldr.simps comp_def gval_gAnd)

lemma maybe_and_not_invalid: "(x \<and>\<^sub>? y \<noteq> invalid) = (x \<noteq> invalid \<and> y \<noteq> invalid)"
  by (simp add: maybe_and_invalid)

lemma negate_not_apply_guards: "gval (negate G) s = true \<Longrightarrow> \<not> apply_guards G s"
  by (simp add: apply_guards_fold negate_true_guard)

lemma less_eq_length_trans: "max_input G < Some a \<Longrightarrow> a \<le> length i \<Longrightarrow> max_input G \<le> Some (length i)"
  by (meson leD less_option.simps(4) not_le_imp_less order.strict_trans)

lemma gval_fold_take:
  "Can_Take.max_input G < Some a \<Longrightarrow>
   a \<le> length i \<Longrightarrow>
   Can_Take.max_input G \<le> Some (length i) \<Longrightarrow>
   gval (fold gAnd G (Bc True)) (join_ir i r) = gval (fold gAnd G (Bc True)) (join_ir (take a i) r)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons g gs)
  then show ?case
    apply (simp only: gval_fold_cons)
    apply (simp add: max_input_cons)
    using gval_take[of g a i r]
    by simp
qed


lemma gval_fold_take_false_not_true:
  "Can_Take.max_reg G = None \<Longrightarrow>
   Can_Take.max_input G < Some a \<Longrightarrow>
   gval (fold gAnd G (Bc True)) (join_ir i ra) = false \<Longrightarrow>
   a \<le> length i \<Longrightarrow>
   gval (fold gAnd G (Bc True)) (join_ir (take a i) r) \<noteq> true"
  using less_eq_length_trans[of G a i]
  apply (simp add: gval_fold_swap_regs[of G i ra r])
  by (simp add: gval_fold_take)

lemma quick_negation_aux: "Can_Take.max_reg G = None \<Longrightarrow>
    Can_Take.max_input G < Some a \<Longrightarrow>
    \<exists>i r. gval (negate G) (join_ir i r) = true \<and> apply_guards (ensure_not_null a) (join_ir i r) \<Longrightarrow>
    \<exists>i. length i = a \<and> \<not> apply_guards G (join_ir i r)"
  apply clarify
  apply (rule_tac x="take_or_pad i a" in exI)
  apply (simp add: length_take_or_pad)
  apply (simp add: apply_guards_ensure_not_null_length take_or_pad_def negate_true_guard)
  apply (simp add: apply_guards_fold)
  by (simp add: gval_fold_take_false_not_true)

lemma quick_negation:
  "max_reg (Guard t) = None \<Longrightarrow>
   max_input (Guard t) < Some (Arity t) \<Longrightarrow>
   satisfiable_list (negate (Guard t) # ensure_not_null (Arity t)) \<Longrightarrow>
   \<exists>i. length i = Arity t \<and> \<not> apply_guards (Guard t) (join_ir i r)"
  apply (simp add: satisfiable_list_def satisfiable_def fold_apply_guards apply_guards_cons del: fold.simps)
  by (simp add: quick_negation_aux)

definition "satisfiable_negation t = (max_reg (Guard t) = None \<and>
   max_input (Guard t) < Some (Arity t) \<and>
   satisfiable_list (negate (Guard t) # ensure_not_null (Arity t)))"

end