theory Medial_Medial
imports Contexts
begin

lemma make_lt_expand:  "make_lt |`| (cp |\<union>| ca2) = (make_lt |`| cp) |\<union>| (make_lt |`| ca2)"
  by (simp add: fimage_funion)

lemma make_gt_expand:  "make_gt |`| (cp |\<union>| ca2) = (make_gt |`| cp) |\<union>| (make_gt |`| ca2)"
  by (simp add: fimage_funion)

lemma make_gt_twice: "make_gt (make_gt x) = make_gt x"
  apply (induct x)
  by auto

lemma make_lt_twice: "make_lt (make_lt x) = make_lt x"
  apply(induct x)
  by auto

lemma fimage_make_lt_twice: "make_lt |`| make_lt |`| cp = make_lt |`| cp"
proof(induct cp)
  case empty
  then show ?case
    by simp
next
  case (insert x cp)
  then show ?case
    by (simp add: make_lt_twice)
qed

lemma union_make_lt: "ca2 |\<union>| make_lt |`| (cp |\<union>| ca2) |\<union>|
         make_lt |`| (cp |\<union>| (ca2 |\<union>| make_lt |`| (cp |\<union>| ca2))) =
         ca2 |\<union>| make_lt |`| (cp |\<union>| ca2)"
  apply (simp only: make_lt_expand)
  apply (simp only: fimage_make_lt_twice)
  by auto

lemma make_gt_make_lt: "make_gt (make_lt xb) = make_lt (make_gt xb)"
proof(induct xb)
case Undef
  then show ?case by simp
next
  case (Bc x)
  then show ?case by simp
next
  case (Eq x)
  then show ?case by simp
next
  case (Lt x)
  then show ?case by simp
next
  case (Gt x)
  then show ?case by simp
next
  case (Not xb)
  then show ?case by simp
next
  case (And xb1 xb2)
  then show ?case by simp
qed

lemma double_map: "map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) G)) =
                   map (\<lambda>(x, y). (not |`| y)) (filter (\<lambda>(a, uu). a = r) G)"
proof(induct G)
  case Nil
  then show ?case by simp
next
  case (Cons a G)
  then show ?case
    apply simp
    apply (cases a)
    by simp
qed

lemma fold_split_induct: "fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) (gs@[g])))) {||} =
       fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) gs))) {||} |\<union>|
       fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) [g]))) {||}"
  apply simp
  apply (cases g)
  apply simp
  apply (case_tac "a = r")
  by auto

lemma fold_split:"
       fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) (G1 @ G2)))) {||} =
       fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) G1))) {||} |\<union>|
       fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) G2))) {||}"
proof(induct G2 rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc a G2)
  then show ?case
    using fold_split_induct
    by auto
qed

lemma subset_consistency: "\<forall>r. c' r |\<subseteq>| c r \<Longrightarrow> consistent c \<Longrightarrow> consistent c'"
  apply (simp add: consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)
  by auto

lemma consistent_medial_idempotence: "consistent (medial (medial c t) t) \<Longrightarrow> consistent (medial c t)"
  by (metis anterior_subset_medial subset_consistency)

lemma medial_preserves_existing_elements: "x |\<in>| c r \<Longrightarrow> x |\<in>| medial c G r "
  using anterior_subset_medial by blast

lemma apply_updates: "consistent (medial c G) \<Longrightarrow>
       \<not> constrains_an_input r \<Longrightarrow>
       fBall (Contexts.apply_updates (medial c G) (medial c G) U r) (\<lambda>c. cval c r i = true) \<Longrightarrow>
       Contexts.apply_updates (medial c G) c U r \<noteq> {|Undef|} \<Longrightarrow>
       x |\<in>| Contexts.apply_updates (medial c G) c U r \<Longrightarrow> cval x r i = true"
proof(induct U)
  case Nil
  then show ?case
    using consistent_def medial_preserves_existing_elements by auto
next
  case (Cons a U)
  then show ?case
    apply (cases a)
    apply simp
    apply (case_tac b)
       apply simp
       apply (case_tac "r = V aa")
        apply simp+
      apply (case_tac "r = V aa")
       apply auto[1]
      apply simp+
     apply (case_tac "r = V aa")
      apply simp+
    apply (case_tac "r = V aa")
    by auto
qed

(* If we can prove that medial (medial c t) t = medial t which it really should do *)
lemma "medial (medial c (Guard t)) (Guard t) = medial c (Guard t) \<Longrightarrow> subsumes c t t"
proof-
  assume medial_idempotent: "medial (medial c (Guard t)) (Guard t) = medial c (Guard t)"
  show ?thesis
    apply (simp add: subsumes_def)
    apply (simp add: posterior_def medial_idempotent Let_def remove_input_constraints_def)
    apply clarify
    by (simp add: apply_updates)
qed

lemma fold_union_append: "fold (|\<union>|) (x@y) {||} = (fold (|\<union>|) x {||}) |\<union>| (fold (|\<union>|) y {||})"
  by (metis ffUnion_funion_distrib fold_union_ffUnion fset_of_list_append)

lemma "medial (medial c G) G x |\<subseteq>| medial c G x"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: medial_def List.maps_def pairs2context_def)
next
  case (Cons a G)
  then show ?case
    apply (simp only: medial_def)
    apply (simp only: pairs2context_def)
    apply (simp only: funion_fsubset_iff)
    apply standard
     apply simp
    apply (simp only: maps_simps(1))
    apply (simp only: filter_append)
    apply (simp only: map_append)
    apply (simp only: fold_union_append)
    apply (simp only: funion_fsubset_iff)
    apply simp
    apply standard
qed

lemma "medial (medial c G) G = medial c G"
  apply (rule ext)
  apply standard
   prefer 2
   apply (simp add: anterior_subset_medial)



end