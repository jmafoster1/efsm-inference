theory Least_Upper_Bound
  imports "../Inference"
begin

fun literal_args :: "gexp \<Rightarrow> bool" where
  "literal_args (Bc v) = False" |
  "literal_args (Eq (V _) (L _)) = True" |
  "literal_args (In _ _) = True" |
  "literal_args (Eq _ _) = False" |
  "literal_args (Lt va v) = False" |
  "literal_args (Null v) = False" |
  "literal_args (Nor v va) = (literal_args v \<and> literal_args va)"

definition "all_literal_args t = (\<forall>g \<in> set (Guard t). literal_args g)"

fun merge_in_eq :: "vname \<Rightarrow> value \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "merge_in_eq v l [] = [Eq (V v) (L l)]" |
  "merge_in_eq v l ((Eq (V v') (L l'))#t) = (if v = v' then (In v (remdups [l, l']))#t else (Eq (V v') (L l'))#(merge_in_eq v l t))" |
  "merge_in_eq v l ((In v' l')#t) = (if v = v' then (In v (remdups (l#l')))#t else (In v' l')#(merge_in_eq v l t))" |
  "merge_in_eq v l (h#t) = h#(merge_in_eq v l t)"

fun merge_in_in :: "vname \<Rightarrow> value list \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "merge_in_in v l [] = [In v l]" |
  "merge_in_in v l ((Eq (V v') (L l'))#t) = (if v = v' then (In v (remdups (l'#l)))#t else (Eq (V v') (L l'))#(merge_in_in v l t))" |
  "merge_in_in v l ((In v' l')#t) = (if v = v' then (In v (remdups (l@l')))#t else (In v' l')#(merge_in_in v l t))" |
  "merge_in_in v l (h#t) = h#(merge_in_in v l t)"

primrec merge_guards :: "gexp list \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "merge_guards [] g2 = g2" |
  "merge_guards (h#t) g2 = (case h of 
      Eq (V v) (L l) \<Rightarrow> merge_guards t (merge_in_eq v l g2) |
      In v l \<Rightarrow> merge_guards t (merge_in_in v l g2)
  )"

definition lob_aux :: "transition \<Rightarrow> transition \<Rightarrow> transition option" where
  "lob_aux t1 t2 = (if Outputs t1 = Outputs t2 \<and> Updates t1 = Updates t2 \<and> all_literal_args t1 \<and> all_literal_args t2 then
      Some \<lparr>Label = Label t1, Arity = Arity t1, Guard = merge_guards (Guard t1) (Guard t2), Outputs = Outputs t1, Updates = Updates t1\<rparr>
     else None)"

fun lob :: update_modifier where
  "lob t1ID t2ID s new old _ = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID) in
     case lob_aux t1 t2 of
       None \<Rightarrow> None |
       Some lob_t \<Rightarrow> 
      Some (replace (drop_transitions new {|t2ID|}) t1ID lob_t)
   )"

fun has_corresponding :: "gexp \<Rightarrow> gexp list \<Rightarrow> bool" where
  "has_corresponding g [] = False" |
  "has_corresponding (Eq (V v) (L l)) ((Eq (V v') (L l'))#t) = (if v = v' \<and> l = l' then True else has_corresponding (Eq (V v) (L l)) t)" |
  "has_corresponding (In v' l') ((Eq (V v) (L l))#t) = (if v = v' \<and> l \<in> set l' then True else has_corresponding (In v' l') t)" |
  "has_corresponding (In v l) ((In v' l')#t) = (if v = v' \<and> set l' \<subseteq> set l then True else has_corresponding (In v l) t)" |
  "has_corresponding g (h#t) = has_corresponding g t"

lemma no_corresponding_bc: "\<not>has_corresponding (Bc x1) G1"
  apply (induct G1)
  by auto

lemma no_corresponding_gt: "\<not>has_corresponding (Gt x1 y1) G1"
  apply (induct G1)
  by auto

lemma no_corresponding_nor: "\<not>has_corresponding (Nor x1 y1) G1"
  apply (induct G1)
  by auto

lemma no_corresponding_null: "\<not>has_corresponding (Null x1) G1"
  apply (induct G1)
  by auto

lemma has_corresponding_eq: "has_corresponding (Eq x21 x22) G1 \<Longrightarrow> (Eq x21 x22) \<in> set G1"
proof(induct G1)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G1)
  then show ?case
    apply (cases a)
         apply simp
        apply (case_tac "x21a")
           apply simp
          apply (case_tac "x22a")
             apply clarify
             apply simp
             apply (case_tac "x21")
                apply simp
               apply (case_tac "x22")
                  apply (metis has_corresponding.simps(2))
    by auto
qed

lemma has_corresponding_In: "has_corresponding (In v l) G1 \<Longrightarrow> (\<exists>l'. (In v l') \<in> set G1 \<and> set l' \<subseteq> set l) \<or> (\<exists>l' \<in> set l. (Eq (V v) (L l')) \<in> set G1)"
proof(induct G1)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G1)
  then show ?case
    apply (cases a)
         apply simp
        defer
        apply simp
       apply simp
    defer
      apply simp
     apply simp
     apply (case_tac x21)
        apply simp
       apply (case_tac x22)
          apply fastforce
         apply simp+
    by metis
qed

lemma gval_each_one: "g \<in> set G \<Longrightarrow> apply_guards G s \<Longrightarrow> gval g s = true"
  using apply_guards_cons apply_guards_rearrange by blast

lemma has_corresponding_apply_guards:
  "\<forall>g\<in>set G2. has_corresponding g G1 \<Longrightarrow>
   apply_guards G1 (join_ir i c) \<Longrightarrow>
   apply_guards G2 (join_ir i c)"
proof(induct G2)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G2)
  then show ?case
    apply (cases a)
         apply (simp add: no_corresponding_bc)
        defer
        apply (simp add: no_corresponding_gt)
       apply (simp add: no_corresponding_null)
      defer
      apply (simp add: no_corresponding_nor)
     apply (simp add: apply_guards_cons apply_guards_def)
     apply clarify
    using has_corresponding_eq
     apply (metis apply_guards(7) trilean.distinct(1) value_eq_def)
    apply (simp add: apply_guards_cons)
    apply clarify
    apply simp
    apply (case_tac "(\<exists>l'. In x51 l' \<in> set G1 \<and> set l' \<subseteq> set x52)")
     apply clarify
     apply (case_tac "gval (In x51 l') (join_ir i c)")
       apply simp
       apply (case_tac "join_ir i c x51 \<in> Some ` set l'")
    apply auto[1]
       apply simp
    using gval_each_one apply fastforce
    using gval_each_one apply fastforce
    apply (case_tac "(\<exists>l' \<in> set x52. (Eq (V x51) (L l')) \<in> set G1)")
     defer
    using has_corresponding_In apply blast
    apply clarify
    apply (case_tac "gval (Eq (V x51) (L l')) (join_ir i c)")
      apply simp
    using image_iff apply fastforce
    using gval_each_one apply fastforce
    using gval_each_one by fastforce
qed


lemma correspondence_subsumption: 
  "Label t1 = Label t2 \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   Outputs t1 = Outputs t2 \<Longrightarrow>
   Updates t1 = Updates t2 \<Longrightarrow>
   \<forall>g \<in> set (Guard t2). has_corresponding g (Guard t1) \<Longrightarrow>
   subsumes t2 c t1"
  apply (rule subsumption)
      apply simp
     apply (simp add: can_take_transition_def can_take_def)
     apply clarify
  apply (simp add: has_corresponding_apply_guards)
    apply simp
  using posterior_separate_def apply auto[1]
  using posterior_def posterior_separate_def by auto

definition "is_lob t1 t2 = (
  Label t1 = Label t2 \<and>
  Arity t1 = Arity t2 \<and>
  Outputs t1 = Outputs t2 \<and>
  Updates t1 = Updates t2 \<and>
  (\<forall>g \<in> set (Guard t2). has_corresponding g (Guard t1)))"

lemma is_lob_direct_subsumption:
  "is_lob t1 t2 \<Longrightarrow> directly_subsumes e1 e2 s s' t2 t1"
  apply (rule subsumes_in_all_contexts_directly_subsumes)
  by (simp add: is_lob_def correspondence_subsumption)

fun has_distinguishing :: "gexp \<Rightarrow> gexp list \<Rightarrow> bool" where
  "has_distinguishing g [] = False" |
  "has_distinguishing (Eq (V v) (L l)) ((Eq (V v') (L l'))#t) = (if v = v' \<and> l \<noteq> l' then True else has_distinguishing (Eq (V v) (L l)) t)" |
  "has_distinguishing (In (I v') l') ((Eq (V (I v)) (L l))#t) = (if v = v' \<and> l \<notin> set l' then True else has_distinguishing (In (I v') l') t)" |
  "has_distinguishing (In (I v) l) ((In (I v') l')#t) = (if v = v' \<and> set l' \<supset> set l then True else has_distinguishing (In (I v) l) t)" |
  "has_distinguishing g (h#t) = has_distinguishing g t"

lemma has_distinguishing: "has_distinguishing g G \<Longrightarrow> (\<exists>v l. g = (Eq (V v) (L l))) \<or> (\<exists>v l. g = In v l)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (cases g)
         apply simp
        apply (case_tac x21)
           apply simp
          apply (case_tac x22)
    by auto
qed

lemma has_distinguishing_Eq: "has_distinguishing (Eq (V v) (L l)) G \<Longrightarrow> \<exists>l'. (Eq (V v) (L l')) \<in> set G \<and> l \<noteq> l'"
proof (induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (cases a)
         apply simp
        apply (case_tac x21)
           apply simp
          apply (case_tac x22)
             apply (metis has_distinguishing.simps(2) list.set_intros(1) list.set_intros(2))
    by auto
qed

lemma ex_mutex: "Eq (V v) (L l) \<in> set G1 \<Longrightarrow>
       Eq (V v) (L l') \<in> set G2 \<Longrightarrow>
       l \<noteq> l' \<Longrightarrow>
       apply_guards G1 s \<Longrightarrow>
       \<not> apply_guards G2 s"
  apply (simp add: apply_guards_def Bex_def)
  apply (rule_tac x="Eq (V v) (L l')" in exI)
  by auto

lemma has_distinguishing_In: 
  "has_distinguishing (In v l) G \<Longrightarrow>
   (\<exists>l' i. v = I i \<and> Eq (V v) (L l') \<in> set G \<and> l' \<notin> set l) \<or> (\<exists>l' i. v = I i \<and> In v l' \<in> set G \<and> set l' \<supset> set l)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (case_tac v)
     apply simp
     apply (cases a)
          apply simp
         apply (case_tac x21)
            apply simp
           apply (case_tac x22)
              apply (case_tac x2)
               apply fastforce
              apply simp+
      apply (case_tac x51)
       apply simp
       apply metis
    by auto
qed

lemma Eq_apply_guards: 
  "Eq (V v) (L l) \<in> set G1 \<Longrightarrow>
   apply_guards G1 s \<Longrightarrow>
   s v = Some l"
  apply (simp add: apply_guards_rearrange)
  apply (simp add: apply_guards_cons)
  using trilean.distinct(1) by presburger

lemma In_neq_apply_guards:
  "In v l \<in> set G2 \<Longrightarrow>
   Eq (V v) (L l') \<in> set G1 \<Longrightarrow>
   l' \<notin> set l \<Longrightarrow>
   apply_guards G1 s \<Longrightarrow>
   \<not>apply_guards G2 s"
proof(induct G1)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G1)
  then show ?case
    apply (simp add: apply_guards_def Bex_def)
    apply (rule_tac x="In v l" in exI)
    using Eq_apply_guards[of v l' "a#G1" s]
    by (simp add: Cons.prems(4) image_iff)
qed

lemma In_apply_guards: "In v l \<in> set G1 \<Longrightarrow> apply_guards G1 s \<Longrightarrow> \<exists>v' \<in> set l. s v = Some v'"
  apply (simp add: apply_guards_rearrange)
  apply (simp add: apply_guards_cons)
  by (meson image_iff trilean.simps(2))

lemma input_not_constrained_aval_swap_inputs:
  "\<not> aexp_constrains a (V (I v)) \<Longrightarrow>
   aval a (join_ir i c) = aval a (join_ir (i[v := x]) c)"
proof(induct a)
  case (L x)
  then show ?case
    by simp
next
  case (V x)
  then show ?case
    apply (cases x)
     apply (metis aexp_constrains.simps(2) aval.simps(2) input2state_nth input2state_out_of_bounds join_ir_def length_list_update not_le nth_list_update_neq vname.simps(5))
    by (simp add: join_ir_def)
next
  case (Plus a1 a2)
  then show ?case
    by simp
next
  case (Minus a1 a2)
  then show ?case
    by simp
qed

lemma input_not_constrained_gval_swap_inputs:
  "\<not> gexp_constrains a (V (I v)) \<Longrightarrow>
   gval a (join_ir i c) = gval a (join_ir (i[v := x]) c)"
proof(induct a)
  case (Bc x)
  then show ?case
    by (metis (full_types) apply_guards(4) apply_guards(5))
next
  case (Eq x1a x2)
  then show ?case
    using input_not_constrained_aval_swap_inputs by auto
next
  case (Gt x1a x2)
  then show ?case
    using input_not_constrained_aval_swap_inputs by auto
next
  case (Null x)
  then show ?case
    using input_not_constrained_aval_swap_inputs by auto
next
  case (In x1a x2)
  then show ?case
    apply simp
    by (metis (full_types) aexp.inject(2) aexp_constrains.simps(2) aval.simps(2) input_not_constrained_aval_swap_inputs)
next
  case (Nor a1 a2)
  then show ?case
    by simp
qed

lemma test_aux: "\<forall>g\<in>set (removeAll (In (I v) l) G1). \<not> gexp_constrains g (V (I v)) \<Longrightarrow>
      apply_guards G1 (join_ir i c) \<Longrightarrow>
      x \<in> set l \<Longrightarrow>
      apply_guards G1 (join_ir (i[v := x]) c)"
proof(induct G1)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G1)
  then show ?case
    apply (simp only: apply_guards_cons)
    apply (case_tac "a = In (I v) l")
     apply (simp add: join_ir_def)
     apply (metis in_these_eq input2state_nth input2state_out_of_bounds length_list_update not_le_imp_less nth_list_update_eq these_image_Some_eq trilean.distinct(1))
    using input_not_constrained_gval_swap_inputs by auto
qed

lemma test:
  assumes
    p1: "In (I v) l \<in> set G2" and
    p2: "In (I v) l' \<in> set G1" and
    p3: "x \<in> set l'" and
    p4: "x \<notin> set l" and
    p5: "apply_guards G1 (join_ir i c)" and
    p6: "length i = a" and
    p7: "\<forall>g \<in> set (removeAll (In (I v) l') G1). \<not> gexp_constrains g (V (I v))"
  shows "\<exists>i. length i = a \<and> apply_guards G1 (join_ir i c) \<and> (length i = a \<longrightarrow> \<not> apply_guards G2 (join_ir i c))"
  apply (rule_tac x="list_update i v x" in exI)
  apply standard
   apply (simp add: p6)
  apply standard
  using p3 p5 p7 test_aux apply blast
  using p1 p4
  apply (simp add: apply_guards_rearrange)
  apply (simp add: apply_guards_cons join_ir_def)
  by (metis None_notin_image_Some in_these_eq input2state_not_None input2state_nth length_list_update nth_list_update_eq these_image_Some_eq)

definition get_Ins :: "gexp list \<Rightarrow> (nat \<times> value list) list" where
  "get_Ins G = map (\<lambda>g. case g of (In (I v) l) \<Rightarrow> (v, l)) (filter (\<lambda>g. case g of (In (I _) _ ) \<Rightarrow> True | _ \<Rightarrow> False) G)"

lemma get_Ins_Cons_equiv: "\<nexists>v l. a = In (I v) l \<Longrightarrow> get_Ins (a # G) = get_Ins G"
  apply (simp add: get_Ins_def)
  apply (cases a)
       apply simp+
   apply (metis (full_types) vname.exhaust vname.simps(6))
  by simp

lemma Ball_Cons: "(\<forall>x \<in> set (a#l). P x) = (P a \<and> (\<forall>x \<in> set l. P x))"
  by simp

lemma In_in_get_Ins: "(In (I v) l \<in> set G) = ((v, l) \<in> set (get_Ins G))"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: get_Ins_def)
next
  case (Cons a G)
  then show ?case
    apply (simp add: get_Ins_def)
    apply (cases a)
         apply simp+
     apply (case_tac x51)
    by auto
qed

definition "check_get_Ins G = (\<forall>(v, l') \<in> set (get_Ins G). \<forall>g \<in> set (removeAll (In (I v) l') G). \<not> gexp_constrains g (V (I v)))"

lemma no_Ins: "[] = get_Ins G \<Longrightarrow> set G - {In (I i) l} = set G"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (cases a)
         apply (simp add: get_Ins_Cons_equiv insert_Diff_if)+
     apply (case_tac x51)
      apply simp
      apply (metis In_in_get_Ins equals0D list.set(1) list.set_intros(1))
     apply (simp add: get_Ins_Cons_equiv)
    by (simp add: get_Ins_Cons_equiv insert_Diff_if)
qed

lemma test2: "In (I i) l \<in> set (Guard t2) \<Longrightarrow>
       In (I i) l' \<in> set (Guard t1) \<Longrightarrow>
       length ia = Arity t1 \<Longrightarrow>
       apply_guards (Guard t1) (join_ir ia c) \<Longrightarrow>
       x \<in> set l' \<Longrightarrow>
       x \<notin> set l \<Longrightarrow>
       \<forall>(v, l')\<in>insert (0, []) (set (get_Ins (Guard t1))). \<forall>g\<in>set (removeAll (In (I v) l') (Guard t1)). \<not> gexp_constrains g (V (I v)) \<Longrightarrow>
       Arity t1 = Arity t2 \<Longrightarrow>
       \<exists>i. length i = Arity t2 \<and> apply_guards (Guard t1) (join_ir i c) \<and> (length i = Arity t2 \<longrightarrow> \<not> apply_guards (Guard t2) (join_ir i c))"
  using test[of i l "Guard t2" l' "Guard t1" x ia  c "Arity t2"]
  apply simp
  apply (case_tac "\<forall>g\<in>set (Guard t1) - {In (I i) l'}. \<not> gexp_constrains g (V (I i))")
   apply simp
  apply simp
  using In_in_get_Ins by blast

lemma distinguishing_subsumption:
  assumes
    p1: "\<exists>g \<in> set (Guard t2). has_distinguishing g (Guard t1)" and
    p2: "Arity t1 = Arity t2" and
    p3: "\<exists>i. can_take_transition t1 i c" and
    p4: "(\<forall>(v, l') \<in> insert (0, []) (set (get_Ins (Guard t1))). \<forall>g \<in> set (removeAll (In (I v) l') (Guard t1)). \<not> gexp_constrains g (V (I v)))"
  shows
   "\<not> subsumes t2 c t1"
proof-
  show ?thesis
    apply (rule bad_guards)
    apply (simp add: can_take_transition_def can_take_def p2)
    apply (insert p1, simp add: Bex_def)
    apply (erule exE)
    apply (case_tac "\<exists>v l. x = (Eq (V v) (L l))")
     apply (metis can_take_def can_take_transition_def ex_mutex p2 p3 has_distinguishing_Eq)
    apply (case_tac "\<exists>v l. x = In v l")
     defer
    using has_distinguishing apply blast
    apply clarify
    apply (case_tac "\<exists>l' i. v = I i \<and> Eq (V v) (L l') \<in> set (Guard t1) \<and> l' \<notin> set l")
     apply (metis In_neq_apply_guards can_take_def can_take_transition_def p2 p3)
    apply (case_tac "(\<exists>l' i. v = I i \<and> In v l' \<in> set (Guard t1) \<and> set l' \<supset> set l)")
     defer
    using has_distinguishing_In apply blast
    apply simp
    apply (erule conjE)
    apply (erule exE)+
    apply (erule conjE)
    apply (insert p3, simp only: can_take_transition_def can_take_def)
    apply (case_tac "\<exists>x. x \<in> set l' \<and> x \<notin> set l")
    apply (erule exE)+
    apply (erule conjE)+
    apply (insert p4 p2)
    using test2
     apply blast
    by auto
qed

definition "lob_distinguished t1 t2 = (
(\<exists>g \<in> set (Guard t2). has_distinguishing g (Guard t1)) \<and>
Arity t1 = Arity t2 \<and>
(\<forall>(v, l') \<in> insert (0, []) (set (get_Ins (Guard t1))). \<forall>g \<in> set (removeAll (In (I v) l') (Guard t1)). \<not> gexp_constrains g (V (I v))))"

lemma must_be_another:
  "1 < size (fset_of_list b) \<Longrightarrow>
   x \<in> set b \<Longrightarrow>
   \<exists>x' \<in> set b. x \<noteq> x'"
proof(induct b)
  case Nil
  then show ?case
    by simp
next
  case (Cons a b)
  then show ?case
    apply (simp add: Bex_def)
    by (metis List.finite_set One_nat_def card.insert card_gt_0_iff card_mono fset_of_list.rep_eq insert_absorb le_0_eq less_nat_zero_code less_numeral_extra(4) not_less_iff_gr_or_eq set_empty2 subsetI)
qed

lemma another_swap_inputs:
  "apply_guards G (join_ir i c) \<Longrightarrow>
  filter (\<lambda>g. gexp_constrains g (V (I a))) G = [In (I a) b] \<Longrightarrow>
  xa \<in> set b \<Longrightarrow>
  apply_guards G (join_ir (i[a := xa]) c)"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons g G)
  then show ?case
    apply (simp add: apply_guards_cons)
    apply (case_tac "gexp_constrains g (V (I a))")
     defer
    using input_not_constrained_gval_swap_inputs apply auto[1]
     apply simp
    apply (case_tac "join_ir i c (I a) \<in> Some ` set b")
     defer
     apply simp
    apply simp
    apply clarify
    apply standard
    using apply_guards_def input_not_constrained_gval_swap_inputs
     apply (simp add: filter_empty_conv)
    by (simp add: input2state_not_None input2state_nth join_ir_def)
qed

lemma lob_distinguished_2_not_subsumes:
  "\<exists>(i, l) \<in> set (get_Ins (Guard t2)). filter (\<lambda>g. gexp_constrains g (V (I i))) (Guard t2) = [(In (I i) l)] \<and>
    (\<exists>l' \<in> set l. i < Arity t1 \<and> Eq (V (I i)) (L l') \<in> set (Guard t1) \<and> size (fset_of_list l) > 1) \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   \<exists>i. can_take_transition t2 i c \<Longrightarrow>
   \<not> subsumes t1 c t2"
  apply (rule bad_guards)
  apply simp
  apply (simp add: can_take_def can_take_transition_def Bex_def)
  apply clarify
  apply (case_tac "\<exists>x' \<in> set b. x \<noteq> x'")
   defer
   apply (simp add: must_be_another)
  apply (simp add: Bex_def)
  apply (erule exE)
  apply (rule_tac x="list_update i a xa" in exI)
  apply simp
  apply standard
   apply (simp add: another_swap_inputs)
  by (metis Eq_apply_guards input2state_nth join_ir_def length_list_update nth_list_update_eq option.inject vname.simps(5))

definition "lob_distinguished_2 t1 t2 =
  (\<exists>(i, l) \<in> set (get_Ins (Guard t2)). filter (\<lambda>g. gexp_constrains g (V (I i))) (Guard t2) = [(In (I i) l)] \<and>
    (\<exists>l' \<in> set l. i < Arity t1 \<and> Eq (V (I i)) (L l') \<in> set (Guard t1) \<and> size (fset_of_list l) > 1) \<and>
  Arity t1 = Arity t2)"

lemma lob_distinguished_3_not_subsumes:
  "\<exists>(i, l) \<in> set (get_Ins (Guard t2)). filter (\<lambda>g. gexp_constrains g (V (I i))) (Guard t2) = [(In (I i) l)] \<and>
    (\<exists>(i', l') \<in> set (get_Ins (Guard t1)). i = i' \<and> set l' \<subset> set l) \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   \<exists>i. can_take_transition t2 i c \<Longrightarrow>
   \<not> subsumes t1 c t2"
  apply (rule bad_guards)
  apply simp
  apply (simp add: can_take_def can_take_transition_def Bex_def)
  apply (erule exE)+
  apply (erule conjE)+
  apply (erule exE)+
  apply (erule conjE)+
  apply (case_tac "\<exists>x. x \<in> set b \<and> x \<notin> set ba")
   defer
  apply auto[1]
  apply (erule exE)+
  apply (erule conjE)+
  apply (rule_tac x="list_update i a x" in exI)
  apply simp
  apply standard
  using another_swap_inputs apply blast
  by (metis In_apply_guards In_in_get_Ins input2state_not_None input2state_nth join_ir_def nth_list_update_eq option.distinct(1) option.inject vname.simps(5))


definition "lob_distinguished_3 t1 t2 = (\<exists>(i, l) \<in> set (get_Ins (Guard t2)). filter (\<lambda>g. gexp_constrains g (V (I i))) (Guard t2) = [(In (I i) l)] \<and>
    (\<exists>(i', l') \<in> set (get_Ins (Guard t1)). i = i' \<and> set l' \<subset> set l) \<and>
   Arity t1 = Arity t2)"

(*definition "t1 = \<lparr>
  Label = STR ''openat'',
  Arity = 5,
  Guard = [
            In (I 0) [Str ''AT_FDCWD''],
            In (I 1) [Str ''/lib/x86_6'', Str ''/proc/file''],
            In (I 2) [Str ''O_''],
            In (I 3) [Str ''RDONLY''],
            In (I 4) [Str ''O_CLOEXEC'']
          ], Outputs = [L (Num 3)],
  Updates = []\<rparr>"

definition "t2 = \<lparr>
  Label = STR ''openat'',
  Arity = 5,
  Guard = [
            In (I 0) [Str ''AT_FDCWD''],
            In (I 1) [Str ''/lib/x86_6'', Str ''/proc/file'', Str ''/usr/share''],
            In (I 2) [Str ''O_''],
            In (I 3) [Str ''RDONLY''],
            In (I 4) [Str ''O_CLOEXEC'']
          ], Outputs = [L (Num 3)],
  Updates = []\<rparr>"

lemma "\<not> subsumes t1 c t2"
  apply (rule lob_distinguished_3_not_subsumes)
  apply (simp add: Bex_def)
    apply (rule_tac x=1 in exI)
    apply (rule_tac x="[Str ''/lib/x86_6'', Str ''/proc/file'', Str ''/usr/share'']" in exI)
    apply standard
     apply (simp add: t2_def get_Ins_def)
    apply standard
     apply (simp add: t2_def)
    apply (rule_tac x="[Str ''/lib/x86_6'', Str ''/proc/file'']" in exI)
    apply standard
     apply (simp add: t1_def get_Ins_def)
    apply (simp add: Str_def)
  oops*)


end