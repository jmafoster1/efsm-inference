theory Can_Take
imports "../EFSM"
begin

unbundle finfun_syntax

primrec padding :: "nat \<Rightarrow> 'a list" where
  "padding 0 = []" |
  "padding (Suc m) = (Eps (\<lambda>x. True))#(padding m)"

definition take_or_pad :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "take_or_pad a n = (if length a \<ge> n then take n a else a@(padding (n-length a)))"

lemma length_padding: "length (padding n) = n"
proof(induct n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by simp
qed

lemma length_take_or_pad: "length (take_or_pad a n) = n"
proof(induct n)
  case 0
  then show ?case
    by (simp add: take_or_pad_def)
next
  case (Suc n)
  then show ?case
    apply (simp add: take_or_pad_def)
    apply standard
     apply auto[1]
    by (simp add: length_padding)
qed

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
     apply (simp add: ValueEq_def)
    by (simp add: Suc_leI datastate(1) input2state_not_None)
qed

lemma apply_guards_take_or_pad: "max_input_list G < Some a \<Longrightarrow>
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
    apply (simp add: apply_guards_cons max_input_list_cons)
    using not_null_length[of a i r]
    apply simp
    apply (simp add: take_or_pad_def)
    by (metis gval_take)
qed

(* Begin can take *)

definition can_take :: "nat \<Rightarrow> gexp list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" where
  "can_take a g i r = (length i = a \<and> apply_guards g (join_ir i r))"

definition "can_take_transition t i r = can_take (Arity t) (Guard t) i r"

lemma can_take_transition_empty_guard: "Guard t = [] \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def Ex_list_of_length)

lemma valid_list_can_take: "valid_list (Guard t) \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def valid_list_apply_guards Ex_list_of_length)

lemma satisfiable_can_take:
  "max_input_list (Guard t) < Some (Arity t) \<Longrightarrow>
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

lemma apply_guards_no_reg_swap_regs:
  "max_reg_list G = None \<Longrightarrow>
   max_input_list G < Some a \<Longrightarrow>
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
    by (metis apply_guards_cons gval_no_reg_swap_regs max.strict_boundedE max_input_list_cons max_is_None max_reg_list_cons not_null_length take_or_pad_def)
qed

lemma can_take_satisfiable:
  "max_reg_list (Guard t) = None \<Longrightarrow>
   max_input_list (Guard t) < Some (Arity t) \<Longrightarrow>
   satisfiable_list ((Guard t) @ ensure_not_null (Arity t)) \<Longrightarrow>
   \<exists>i. can_take_transition t i r"
  apply (simp add: can_take_transition_def satisfiable_list_def satisfiable_def fold_apply_guards
                   apply_guards_append can_take_def del: fold_append)
  apply clarify
  apply (rule_tac x="take_or_pad i (Arity t)" in exI)
  apply standard
   apply (simp add: length_take_or_pad)
  by (simp add: apply_guards_no_reg_swap_regs)

lemma max_reg_list_ensure_not_null: "max_reg_list (ensure_not_null a) = None"
proof(induct a)
  case 0
  then show ?case
    by (simp add: ensure_not_null_def max_reg_list_def)
next
  case (Suc a)
  then show ?case
    by (simp add: ensure_not_null_cons max_reg_list_append max_reg_list_def max_reg_gNot max_reg_Null max_reg_V)
qed

fun not_null :: "gexp \<Rightarrow> bool" where
  "not_null (Null x) = False" |
  "not_null (Nor x y) = (not_null x \<and> not_null y)" |
  "not_null _ = True"

lemma apply_guards_ensure_not_null:
  "length i \<ge> a \<Longrightarrow>
   apply_guards (ensure_not_null a) (join_ir i r)"
proof(induct a)
  case 0
  then show ?case
    by (simp add: ensure_not_null_def)
next
  case (Suc a)
  then show ?case
    apply (simp add: ensure_not_null_cons apply_guards_append apply_guards_singleton ValueEq_def)
    by (simp add: join_ir_def input2state_nth)
qed

lemma apply_guards_ensure_not_null_length: "apply_guards (ensure_not_null a) (join_ir i r) = (length i \<ge> a)"
  using apply_guards_ensure_not_null not_null_length by blast

definition negate :: "gexp list \<Rightarrow> gexp" where
  "negate g = gNot (fold gAnd g (Bc True))"

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

lemma gval_fold_swap_regs: "max_reg_list G = None \<Longrightarrow> gval (fold gAnd G (Bc True)) (join_ir i r) = gval (fold gAnd G (Bc True)) (join_ir i r')"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp only: gval_fold_equiv_gval_foldr foldr.simps comp_def gval_gAnd)
    by (metis (no_types, lifting) max_is_None max_reg_list_cons no_reg_gval_swap_regs)
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

lemma less_eq_length_trans: "max_input_list G < Some a \<Longrightarrow> a \<le> length i \<Longrightarrow> max_input_list G \<le> Some (length i)"
  by (meson leD less_option.simps(4) not_le_imp_less order.strict_trans)

lemma gval_fold_take:
  "max_input_list G < Some a \<Longrightarrow>
   a \<le> length i \<Longrightarrow>
   max_input_list G \<le> Some (length i) \<Longrightarrow>
   gval (fold gAnd G (Bc True)) (join_ir i r) = gval (fold gAnd G (Bc True)) (join_ir (take a i) r)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons g gs)
  then show ?case
    apply (simp only: gval_fold_cons)
    apply (simp add: max_input_list_cons)
    using gval_take[of g a i r]
    by simp
qed

lemma gval_fold_take_false_not_true:
  "max_reg_list G = None \<Longrightarrow>
   max_input_list G < Some a \<Longrightarrow>
   gval (fold gAnd G (Bc True)) (join_ir i ra) = false \<Longrightarrow>
   a \<le> length i \<Longrightarrow>
   gval (fold gAnd G (Bc True)) (join_ir (take a i) r) \<noteq> true"
  using less_eq_length_trans[of G a i]
  apply (simp add: gval_fold_swap_regs[of G i ra r])
  by (simp add: gval_fold_take)

lemma quick_negation_aux: "max_reg_list G = None \<Longrightarrow>
    max_input_list G < Some a \<Longrightarrow>
    \<exists>i r. gval (negate G) (join_ir i r) = true \<and> apply_guards (ensure_not_null a) (join_ir i r) \<Longrightarrow>
    \<exists>i. length i = a \<and> \<not> apply_guards G (join_ir i r)"
  apply clarify
  apply (rule_tac x="take_or_pad i a" in exI)
  apply (simp add: length_take_or_pad)
  apply (simp add: apply_guards_ensure_not_null_length take_or_pad_def negate_true_guard)
  apply (simp add: apply_guards_fold)
  by (simp add: gval_fold_take_false_not_true)

lemma quick_negation:
  "max_reg_list (Guard t) = None \<Longrightarrow>
   max_input_list (Guard t) < Some (Arity t) \<Longrightarrow>
   satisfiable_list (negate (Guard t) # ensure_not_null (Arity t)) \<Longrightarrow>
   \<exists>i. length i = Arity t \<and> \<not> apply_guards (Guard t) (join_ir i r)"
  apply (simp add: satisfiable_list_def satisfiable_def fold_apply_guards apply_guards_cons del: fold.simps)
  by (simp add: quick_negation_aux)

definition "satisfiable_negation t = (max_reg_list (Guard t) = None \<and>
   max_input_list (Guard t) < Some (Arity t) \<and>
   satisfiable_list (negate (Guard t) # ensure_not_null (Arity t)))"

end