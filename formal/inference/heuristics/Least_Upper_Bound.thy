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

fun merge_in :: "vname \<Rightarrow> value \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "merge_in v l [] = [Eq (V v) (L l)]" |
  "merge_in v l ((Eq (V v') (L l'))#t) = (if v = v' then (In v (remdups [l, l']))#t else (Eq (V v') (L l'))#(merge_in v l t))" |
  "merge_in v l ((In v' l')#t) = (if v = v' then (In v (remdups (l#l')))#t else (In v' l')#(merge_in v l t))" |
  "merge_in v l (h#t) = h#(merge_in v l t)"

primrec merge_guards :: "gexp list \<Rightarrow> gexp list \<Rightarrow> gexp list" where
  "merge_guards [] g2 = g2" |
  "merge_guards (h#t) g2 = (case h of (Eq (V v) (L l)) \<Rightarrow> merge_guards t (merge_in v l g2))"

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


lemma correspondence_subsumption: "Label t1 = Label t2 \<Longrightarrow>
       Arity t1 = Arity t2 \<Longrightarrow>
       Outputs t1 = Outputs t2 \<Longrightarrow>
       Updates t1 = Updates t2 \<Longrightarrow>
       all_literal_args t1 \<Longrightarrow>
       all_literal_args t2 \<Longrightarrow>
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

end