subsection \<open>Contexts\<close>
text\<open>
This theory defines contexts as a way of relating possible constraints on register values to
observable output. We then use contexts to extend the idea of transition subsumption to EFSM
transitions with register update functions.
\<close>

theory Contexts
  imports
    EFSM GExp
begin

declare gval.simps [simp]
declare ValueEq_def [simp]

definition can_take :: "nat \<Rightarrow> gexp list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" where
  "can_take a g i r = (length i = a \<and> apply_guards g (join_ir i r))"

definition "can_take_transition t i r = can_take (Arity t) (Guard t) i r"

lemma enumerate_gexp_regs_set_reg_unconstrained:
  "\<forall>x\<in>set G. enumerate_gexp_regs x = {} \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r))"
  by (simp add: enumerate_gexp_regs_empty_reg_unconstrained)

lemma enumerate_gexp_inputs_set_input_unconstrained:
  "\<forall>x\<in>set G. enumerate_gexp_inputs x = {} \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (vname.I r))"
  by (simp add: enumerate_gexp_inputs_empty_input_unconstrained)

lemma unconstrained_variable_swap: "\<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (vname.I r)) \<Longrightarrow>
       \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r)) \<Longrightarrow>
       apply_guards G (join_ir i r) = apply_guards G (join_ir i' r')"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    unfolding apply_guards_def
    apply simp
    by (metis input_unconstrained_gval_input_swap register_unconstrained_gval_register_swap)
qed

lemma unconstrained_variable_swap_apply_guards:
  "\<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (vname.I r)) \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r)) \<Longrightarrow>
   gval (foldr gAnd G (Bc True)) s = true \<Longrightarrow>
   apply_guards G s'"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_gAnd maybe_and_true apply_guards_cons)
    apply simp
    by (metis unconstrained_variable_swap_gval)
qed

lemma no_variables_list_aval:
  "enumerate_aexp_inputs_list a = [] \<Longrightarrow>
   enumerate_aexp_regs_list a = [] \<Longrightarrow>
   aval a s = aval a s'"
proof(induct a)
case (L x)
  then show ?case by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma no_variables_list_gval:
  "enumerate_gexp_inputs_list a = [] \<Longrightarrow>
   enumerate_gexp_regs_list a = [] \<Longrightarrow>
   gval a s = gval a s'"
proof(induct a)
case (Bc x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Eq x1a x2)
  then show ?case
    by (metis no_variables_list_aval Nil_is_append_conv enumerate_gexp_inputs_list.simps(3) enumerate_gexp_regs_list.simps(3) gval.simps(4))
next
  case (Gt x1a x2)
  then show ?case
    by (metis append_is_Nil_conv enumerate_gexp_inputs_list.simps(4) enumerate_gexp_regs_list.simps(4) gval.simps(3) no_variables_list_aval)
next
  case (Nor a1 a2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (metis enumerate_gexp_inputs_list.simps(2) enumerate_gexp_regs_list.simps(2) gval.simps(6) no_variables_list_aval)
qed

lemma no_variables_gval_any_state:
  "fold (@) (map enumerate_gexp_regs_list G) [] = [] \<Longrightarrow>
   gval (foldr gAnd G (Bc True)) s = true \<Longrightarrow>
   fold (@) (map enumerate_gexp_inputs_list G) [] = [] \<Longrightarrow>
   gval (foldr gAnd G (Bc True)) (join_ir i r) = true"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_gAnd maybe_and_true)
    apply simp
    using no_variables_list_gval
    by (metis (no_types, lifting) Nil_is_append_conv fold_append_concat_rev)
qed

lemma fold_guards_max: "foldr max (fold (@) (map enumerate_gexp_inputs_list (Guard t)) [])
          (foldr max (fold (@) (map enumerate_aexp_inputs_list (Outputs t)) [])
            (foldr max (fold (@) (map (\<lambda>(uu, y). enumerate_aexp_inputs_list y) (Updates t)) []) 0))
         < a \<Longrightarrow>
         fold (@) (map enumerate_gexp_inputs_list (Guard t)) [] \<noteq> [] \<Longrightarrow>
         foldr max (fold (@) (map enumerate_gexp_inputs_list (Guard t)) []) 0 < a"
  by (metis List.finite_set Max.set_eq_fold Max_insert foldr_conv_fold list.set(2) max_less_iff_conj max_set_nat_list set_empty set_rev)

lemma exists_input_input2state: "\<exists>i. input2state i x1 = Some a"
proof(induct x1)
case 0
  then show ?case
    apply (rule_tac x="[a]" in exI)
    by (simp add: input2state_def)
next
  case (Suc x1)
  then show ?case
    apply clarify
    apply (rule_tac x="a#i" in exI)
    apply (simp add: input2state_def)
    by (simp add: in_set_enumerate_eq)
qed

lemma exists_join_ir_ext: "\<exists>i r. join_ir i r v = s v"
  apply (simp add: join_ir_def)
  apply (case_tac "s v")
   apply (cases v)
    apply (rule_tac x="[]" in exI)
    apply (simp add: input2state_out_of_bounds)
   apply simp
   apply (rule_tac x="<>" in exI)
   apply simp
  apply simp
  apply (cases v)
   apply simp
   defer
   apply simp
   apply (rule_tac x="<x2 := a>" in exI)
   apply simp
  by (simp add: exists_input_input2state)

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

lemma enumerate_registers_list_empty: "enumerate_registers_list t = [] \<Longrightarrow> fold (@) (map enumerate_gexp_regs_list (Guard t)) [] = []"
  by (simp add: enumerate_registers_list_def)

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

lemma aval_ir_take: "A \<le> length i \<Longrightarrow>
      enumerate_aexp_regs_list a = [] \<Longrightarrow>
      enumerate_aexp_inputs_list a \<noteq> [] \<Longrightarrow>
      foldr max (enumerate_aexp_inputs_list a) 0 < A \<Longrightarrow>
      aval a (join_ir (take A i) r) = aval a (join_ir i ra)"
proof(induct a)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply (simp add: join_ir_def input2state_nth)
    by simp
next
  case (Plus a1 a2)
  then show ?case
    apply simp
    apply clarify
    by (metis (no_types, lifting) List.finite_set Max.set_eq_fold Max_insert fold_simps(1) foldr_conv_fold list.set(2) max_less_iff_conj no_variables_list_aval set_empty)
next
  case (Minus a1 a2)
  then show ?case
apply simp
    apply clarify
    by (metis (no_types, lifting) List.finite_set Max.set_eq_fold Max_insert fold_simps(1) foldr_conv_fold list.set(2) max_less_iff_conj no_variables_list_aval set_empty)
qed

lemma gval_ir_take: "A \<le> length i \<Longrightarrow>
      enumerate_gexp_regs_list a = [] \<Longrightarrow>
      enumerate_gexp_inputs_list a \<noteq> [] \<Longrightarrow>
      foldr max (enumerate_gexp_inputs_list a) 0 < A \<Longrightarrow>
      gval a (join_ir (take A i) r) = gval a (join_ir i ra)"
proof(induct a)
case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    apply simp
    apply (case_tac "enumerate_aexp_inputs_list x1a = []")
     apply simp
     apply (metis aval_ir_take no_variables_list_aval)
    apply simp
    by (metis Eq.prems(1) Eq.prems(4) List.finite_set Max.set_eq_fold Max_insert aval_ir_take fold_simps(1) foldr_conv_fold list.set(2) max.commute max_0L max_less_iff_conj no_variables_list_aval set_empty set_rev)
next
  case (Gt x1a x2)
  then show ?case
    apply simp
    apply (case_tac "enumerate_aexp_inputs_list x1a = []")
     apply simp
     apply (metis aval_ir_take no_variables_list_aval)
    apply simp
    by (metis List.finite_set Max.set_eq_fold Max_insert aval_ir_take foldr.simps(1) foldr_conv_fold id_apply list.set(2) max_less_iff_conj no_variables_list_aval set_empty set_rev)
next
  case (Nor a1 a2)
  then show ?case
    apply simp
    apply clarify
    by (metis List.finite_set Max.set_eq_fold Max_insert foldr.simps(1) foldr_conv_fold id_apply list.set(2) max_less_iff_conj no_variables_list_gval set_empty set_rev)
next
  case (Null x)
  then show ?case
    apply simp
    by (metis aval_ir_take)
qed

lemma fold_max_rev: "fold max (rev list) (0::nat) = fold max list 0"
proof(induct list)
  case Nil
  then show ?case
    by simp
next
  case (Cons a list)
  then show ?case
    apply simp
    by (metis List.finite_set Max.set_eq_fold Max_insert fold_simps(1) list.set(2) max.assoc max_0R set_empty)
qed

lemma max_individual_max_total: "enumerate_gexp_inputs_list a = aa # list \<Longrightarrow>
       \<not> (aa < A \<and> foldr max list 0 < A) \<Longrightarrow>
       \<not> foldr max (fold (@) l (aa # list)) 0 < A"
proof(induct "enumerate_gexp_inputs_list a")
  case Nil
  then show ?case
    by simp
next
  case (Cons a x)
  then show ?case
    apply simp
    apply (simp only: not_less foldr_conv_fold)
    apply clarify
    apply (simp add: fold_max_rev)
  proof -
assume a1: "aa < A \<longrightarrow> A \<le> fold max list 0"
  have f2: "\<forall>n ns. Max (set ((n::nat) # ns)) = fold max ns n"
    using Max.set_eq_fold by blast
  have f3: "\<forall>N n. infinite N \<or> N = {} \<or> Max (insert (n::nat) N) = max n (Max N)"
    by force
  have f4: "\<forall>n na nb. (max (n::nat) na < nb) = (n < nb \<and> na < nb)"
  using max_less_iff_conj by blast
  have "\<not> aa < A \<or> A \<le> fold max list 0"
    using a1 by blast
  then have "\<not> max (fold max (concat (rev l)) 0) (fold max list aa) < A"
    using f4 f3 f2 by (metis (no_types) List.finite_set fold_simps(1) list.set(2) not_le set_empty)
  then have "\<not> fold max (fold (@) l (aa # list)) 0 < A"
    using f3 f2 by (metis List.finite_set fold_append fold_append_concat_rev list.set(2) list.simps(3) o_apply set_empty)
  then show "A \<le> fold max (fold (@) l (aa # list)) 0"
    by (meson not_le)
qed
qed

lemma aux1: "fold (@) (G) (aa # list) \<noteq> [] \<Longrightarrow>
       foldr max (fold (@) (G) (aa # list)) 0 < A \<Longrightarrow>
       aa < A \<Longrightarrow>
       foldr max list 0 < A \<Longrightarrow>
       fold (@) (G) [] \<noteq> [] \<Longrightarrow>
       foldr max (fold (@) (G) []) 0 < (A::nat)"
  by (metis List.finite_set Max.set_eq_fold Max_insert append_Nil2 fold_append_concat_rev foldr_append foldr_conv_fold list.set(2) max_less_iff_conj set_empty set_rev)

lemma fold_concat_simp: "
f a \<noteq> [] \<Longrightarrow>
fold (@) (map f G) [] \<noteq> [] \<Longrightarrow>
fold (@) (map f G) (f a) \<noteq> []
"
  by (simp add: fold_append_concat_rev)

lemma fold_foldr: "foldr max (fold (@) (map f G) (f a)) 0 = foldr max (fold (@) (map f (a#G)) []) 0"
  by simp

lemma contradiction_1: "
foldr max (fold (@) (map f G) (f a)) 0 < A \<Longrightarrow>
f a \<noteq> [] \<Longrightarrow>
foldr max (f a) 0 < A \<Longrightarrow>
fold (@) (map f G) [] \<noteq> [] \<Longrightarrow>
\<not>A \<le> foldr max (fold (@) (map f G) []) (0::nat)
"
  by (metis (no_types, lifting) List.finite_set Max.set_eq_fold Max_insert append_Nil2 fold_append_concat_rev foldr_append foldr_conv_fold list.set(2) max_less_iff_conj not_le set_empty set_rev)

lemma max_input_enum: "\<forall>a\<in>set (enumerate_inputs_list t). a < Arity t \<Longrightarrow>  \<forall>a\<in>set (fold (@) (map enumerate_gexp_inputs_list (Guard t)) []). a < Arity t"
  by (simp add: enumerate_inputs_list_def)

lemma apply_guards_swap: "apply_guards G (join_ir i r) \<Longrightarrow>
       \<forall>x\<in>set G. enumerate_gexp_regs x = {} \<Longrightarrow>
       fold (@) (map enumerate_gexp_inputs_list G) [] = [] \<Longrightarrow>
       apply_guards G (join_ir i' r')"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    apply (simp add: apply_guards_cons)
    by (metis Nil_is_append_conv enumerate_gexp_regs_list fold_append_concat_rev no_variables_list_gval set_empty)
qed

lemma remove_outputs_updates: "\<forall>a\<in>set (fold (@) (map enumerate_gexp_inputs_list (Guard t)) []) \<union>
           (set (fold (@) (map enumerate_aexp_inputs_list (Outputs t)) []) \<union>
            set (fold (@) (map (\<lambda>(uu, y). enumerate_aexp_inputs_list y) (Updates t)) [])).
          a < Arity t \<Longrightarrow> \<forall>a\<in>set (fold (@) (map enumerate_gexp_inputs_list (Guard t)) []). a < Arity t"
  by simp

(* apply_guards_take *)
lemma test2: "enumerate_gexp_regs g = {} \<Longrightarrow>
       enumerate_gexp_inputs_list g = [] \<Longrightarrow>
       A \<le> length i \<Longrightarrow>
       gval g (join_ir i ra) = gval g (join_ir (take A i) r)"
proof(induct g)
  case (Bc x)
then show ?case
  by (simp add: no_variables_list_gval)
next
  case (Eq x1a x2)
  then show ?case
    by (metis enumerate_gexp_regs_list no_variables_list_gval set_empty)
next
  case (Gt x1a x2)
  then show ?case
    by (metis enumerate_gexp_regs_list no_variables_list_gval set_empty)
next
  case (Nor g1 g2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (metis enumerate_gexp_regs_list no_variables_list_gval set_empty)
qed

lemma test_aux_aux:
"enumerate_aexp_regs g = {} \<Longrightarrow>
enumerate_aexp_inputs_list g = [] \<Longrightarrow>
A \<le> length i \<Longrightarrow>
aval g (join_ir i ra) = aval g (join_ir (take A i) r)"
proof(induct g)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus g1 g2)
  then show ?case
    by simp
next
  case (Minus g1 g2)
  then show ?case
    by simp
qed

lemma test_aux_aux_2: "x1 < A \<Longrightarrow> A \<le> length i \<Longrightarrow> x = vname.I x1 \<Longrightarrow> input2state i x1 = input2state (take A i) x1"
proof(induct i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a i)
  then show ?case
    by (simp add: input2state_nth)
qed

lemma test_aux:
"enumerate_aexp_regs g = {} \<Longrightarrow>
enumerate_aexp_inputs_list g \<noteq> [] \<Longrightarrow>
\<forall>a \<in> set (enumerate_aexp_inputs_list g). a < A \<Longrightarrow>
A \<le> length i \<Longrightarrow>
aval g (join_ir i ra) = aval g (join_ir (take A i) r)"
proof(induct g)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     defer
     apply simp
    apply (simp add: join_ir_def)
    using test_aux_aux_2 by blast
next
  case (Plus g1 g2)
  then show ?case
    apply simp
    by (metis test_aux_aux)
next
  case (Minus g1 g2)
  then show ?case
    apply simp
    by (metis test_aux_aux)
qed

lemma test: "enumerate_gexp_regs g = {} \<Longrightarrow>
       enumerate_gexp_inputs_list g \<noteq> [] \<Longrightarrow>
      \<forall>a \<in> set (enumerate_gexp_inputs_list g). a < A \<Longrightarrow>
       A \<le> length i \<Longrightarrow>
       gval g (join_ir i ra) = gval g (join_ir (take A i) r)"
proof(induct g)
  case (Bc x)
then show ?case
  by simp
next
  case (Eq x1a x2)
  then show ?case
    apply simp
    apply standard
     apply (metis Un_iff test_aux test_aux_aux)
    by (metis Un_iff test_aux test_aux_aux)
next
  case (Gt x1a x2)
  then show ?case
    apply (simp add: ValueGt_def)
    by (metis Un_iff test_aux test_aux_aux)
next
  case (Nor g1 g2)
  then show ?case
    apply (simp add: maybe_not_eq)
    by (metis test2)
next
  case (Null x)
  then show ?case
    apply simp
    apply standard
     apply (metis test_aux)
    by (metis test_aux)
qed

lemma apply_guards_take: "apply_guards G (join_ir i ra) \<Longrightarrow>
       \<forall>x\<in>set G. enumerate_gexp_regs x = {} \<Longrightarrow>
       fold (@) (map enumerate_gexp_inputs_list G) [] \<noteq> [] \<Longrightarrow>
      \<forall>a \<in> set (fold (@) (map enumerate_gexp_inputs_list G) []). a < A \<Longrightarrow>
       A \<le> length i \<Longrightarrow>
       apply_guards G (join_ir (take A i) r)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    apply (simp add: apply_guards_cons del: fold.simps)
    apply (case_tac "enumerate_gexp_inputs_list a = []")
     apply simp
    using test2
     apply metis
    apply standard
     apply (metis Un_iff fold_append_concat_rev fold_simps(2) set_append test)
    by (metis Un_iff apply_guards_swap fold_append_concat_rev fold_simps(2) set_append)
qed
(* End apply_guards_take *)

(* apply_guards_pad *)
lemma test2_pad: "enumerate_gexp_regs g = {} \<Longrightarrow>
       enumerate_gexp_inputs_list g = [] \<Longrightarrow>
       A > length i \<Longrightarrow>
       gval g (join_ir i ra) = gval g (join_ir (i@i') r)"
proof(induct g)
  case (Bc x)
then show ?case
  by (simp add: no_variables_list_gval)
next
  case (Eq x1a x2)
  then show ?case
    by (metis enumerate_gexp_regs_list no_variables_list_gval set_empty)
next
  case (Gt x1a x2)
  then show ?case
    by (metis enumerate_gexp_regs_list no_variables_list_gval set_empty)
next
  case (Nor g1 g2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (metis enumerate_gexp_regs_list no_variables_list_gval set_empty)
qed

lemma test_aux_aux_pad:
"enumerate_aexp_regs g = {} \<Longrightarrow>
enumerate_aexp_inputs_list g = [] \<Longrightarrow>
A < length i \<Longrightarrow>
aval g (join_ir i ra) = aval g (join_ir (i@i') r)"
proof(induct g)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
    by auto
next
  case (Plus g1 g2)
  then show ?case
    by simp
next
  case (Minus g1 g2)
  then show ?case
    by simp
qed

lemma input2state_eq_or_none:
  "x1 < A \<Longrightarrow>
  length i < A \<Longrightarrow>
  x = vname.I x1 \<Longrightarrow>
  input2state i x1 = input2state (i @ i') x1 \<or> input2state i x1 = None"
  apply (case_tac "x1 < length i")
   apply (simp add: input2state_nth nth_append)
  by (simp add: input2state_out_of_bounds)

lemma test_aux_pad:
"enumerate_aexp_regs g = {} \<Longrightarrow>
enumerate_aexp_inputs_list g \<noteq> [] \<Longrightarrow>
\<forall>a \<in> set (enumerate_aexp_inputs_list g). a < A \<Longrightarrow>
A > length i \<Longrightarrow>
aval g (join_ir i ra) = aval g (join_ir (i@i') r) \<or> aval g (join_ir i ra) = None"
proof(induct g)
case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     defer
     apply simp
    by (simp add: join_ir_def input2state_eq_or_none)
next
  case (Plus g1 g2)
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) aval.simps(3) take_eq_Nil test_aux_aux value_plus.simps(2) value_plus.simps(4) zero_le)
next
  case (Minus g1 g2)
  then show ?case
    apply simp
    by (metis (no_types, hide_lams) take_eq_Nil test_aux_aux value_minus.simps(2) value_minus.simps(4) zero_le)
qed

lemma medial_subset:
  "length i = Arity t \<Longrightarrow>
  Arity t = Arity t' \<Longrightarrow>
  set (Guard t') \<subseteq> set (Guard t) \<Longrightarrow>
  can_take_transition t i r \<Longrightarrow>
  can_take_transition t' i r"
  by (simp add: can_take_transition_def can_take_def apply_guards_subset)

definition d2r :: "datastate \<Rightarrow> registers" where
  "d2r d = (\<lambda>r. d (R r))"

lemma d2r_keeps_regs_same [simp]: "d2r c r = c (R r)"
  by (simp add: d2r_def)

definition posterior_separate :: "nat \<Rightarrow> gexp list \<Rightarrow> update_function list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior_separate a g u i r = (if can_take a g i r then Some (apply_updates u (join_ir i r) r) else None)"

definition posterior :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior t i r = posterior_separate (Arity t) (Guard t) (Updates t) i r"

definition r2d :: "registers \<Rightarrow> datastate" where
  "r2d regs = (\<lambda>i. case i of R r \<Rightarrow> regs r | _ \<Rightarrow> None)"

definition subsumes :: "transition \<Rightarrow> registers \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes t2 r t1 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                       (\<forall>p1 p2 i. posterior_separate (Arity t2) ((Guard t2)@(Guard t1)) (Updates t2) i r = Some p2 \<and>
                                  posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1 \<longrightarrow>
                                  (\<forall>P r'. (p1 r' = None) \<or> (P (p2 r') \<longrightarrow> P (p1 r')))) \<and>
                       (\<forall>p1 p2 i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1 \<longrightarrow> (\<forall>r. p1 r \<noteq> None \<longrightarrow>  p2 r \<noteq> None))
                      )"

lemma subsumption: 
  "(Label t1 = Label t2 \<and> Arity t1 = Arity t2) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<Longrightarrow>
   (\<forall>p1 p2 i. posterior_separate (Arity t2) ((Guard t2)@(Guard t1)) (Updates t2) i r = Some p2 \<and>
                                  posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1 \<longrightarrow>
                                  (\<forall>P r'. (p1 r' = None) \<or> (P (p2 r') \<longrightarrow> P (p1 r')))) \<Longrightarrow>
   (\<forall>p1 p2 i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1 \<longrightarrow> (\<forall>r. p1 r \<noteq> None \<longrightarrow>  p2 r \<noteq> None)) \<Longrightarrow>
   subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma bad_guards: "\<exists>i. can_take_transition t1 i r \<and> \<not> can_take_transition t2 i r \<Longrightarrow> \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma inconsistent_updates: "\<exists>p1 p2. (\<exists>i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1) \<and> (\<exists>r. (\<exists>y. p1 r = Some y) \<and> p2 r = None) \<Longrightarrow>
 \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma inconsistent_updates2: "\<exists>p1 p2.
       (\<exists>i. posterior_separate (Arity t2) (Guard t2 @ Guard t1) (Updates t2) i r = Some p2 \<and>
            posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1) \<and>
       (\<exists>P r'. P (p2 r') \<and> (\<exists>y. p1 r' = Some y) \<and> \<not> P (p1 r')) \<Longrightarrow>
    \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma bad_outputs: "\<exists>i. can_take_transition t1 i r \<and> apply_outputs (Outputs t1) (join_ir i r) \<noteq> apply_outputs (Outputs t2) (join_ir i r) \<Longrightarrow>
 \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma transition_subsumes_self: "subsumes t c t"
  apply (simp add: subsumes_def)
  using posterior_separate_def by auto

primrec posterior_sequence :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> registers option" where
  "posterior_sequence _ _ r [] = Some r" |
  "posterior_sequence e s r (a#t) = (case step e s r (fst a) (snd a) of
                                            None \<Rightarrow> None |
                                            Some (_, s', _, r') \<Rightarrow> posterior_sequence e s' r' t
                                         )"

abbreviation anterior_context :: "transition_matrix \<Rightarrow> trace \<Rightarrow> registers option" where
  "anterior_context e t \<equiv> posterior_sequence e 0 <> t"

lemma posterior_sequence_accepts: "\<forall>s d. posterior_sequence e s d t = Some ca \<longrightarrow> accepts e s d t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply simp
     apply (case_tac "step e s d (fst a) (snd a)")
     apply simp
    apply (case_tac aa)
    apply simp
    apply (rule accepts.step)
     apply simp
    by simp
qed

lemma anterior_context_accepts: "\<exists>c. anterior_context e p = Some c \<Longrightarrow> accepts_trace e p"
  using posterior_sequence_accepts
  by auto

lemma accepts_gives_context: "\<forall>s d. accepts e s d t \<longrightarrow> (\<exists>c. posterior_sequence e s d t = Some c)"
proof(induct t)
case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply simp
     apply (case_tac "step e s d (fst a) (snd a)")
     apply simp
     apply (simp add: conditions_inaccepts)
    apply simp
    apply (case_tac aa)
    apply simp
    using inaccepts_future_inaccepts by blast
qed

lemma accepts_trace_gives_context: "accepts_trace e p \<Longrightarrow> (\<exists>c. anterior_context e p = Some c)"
  using accepts_gives_context by auto

lemma accepts_trace_anterior_not_none: "accepts_trace e p \<Longrightarrow> anterior_context e p \<noteq> None"
  using accepts_trace_gives_context by blast

lemma mutually_exclusive_not_apply_guards:
  "\<not> satisfiable (fold gAnd (G1 @ G2) (Bc True)) \<Longrightarrow>
   apply_guards G1 (join_ir i c) \<Longrightarrow>
   \<not> apply_guards G2 (join_ir i c)"
  apply (simp only: fold_apply_guards satisfiable_def)
  apply (simp add: apply_guards_def)
  by blast

lemma "\<exists>i. can_take_transition t1 i c \<Longrightarrow>
       \<not>satisfiable (fold gAnd ((Guard t1)@(Guard t2)) (Bc True)) \<Longrightarrow>
       \<not> subsumes t2 c t1"
  apply (simp add: subsumes_def del: fold_append)
  apply standard
  apply standard
  apply (rule disjI1)
  apply clarify
  apply (rule_tac x=i in exI)
  by (simp add: can_take_transition_def can_take_def mutually_exclusive_not_apply_guards)

end
