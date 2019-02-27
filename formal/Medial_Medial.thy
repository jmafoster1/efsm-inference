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

lemma aux: "(\<lambda>r. c r |\<union>| fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (guard2pairs c G))) {||} |\<union>|
         fold (|\<union>|)
          (map snd
            (filter (\<lambda>(a, uu). a = r)
              (guard2pairs (\<lambda>r. c r |\<union>| fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (guard2pairs c G))) {||})
                G)))
          {||}) =
    (\<lambda>r. c r |\<union>| fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (guard2pairs c G))) {||})"
proof(induct G)
case (Bc x)
  then show ?case
    apply (case_tac x)
    by auto
next
case (Eq a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
      apply (induct a2)
      by auto
  next
    case (V x)
    then show ?case
    proof(induct a2)
      case (L x)
      then show ?case by simp
    next
      case (V v)
      then show ?case
        apply simp
        apply (case_tac "v = x")
         apply simp
         apply (rule ext)
         apply auto[1]
        apply simp
        apply (rule ext)
        by auto
    next
      case (Plus a21 a22)
      then show ?case
        apply (case_tac "a21 = a22")
         apply simp
         apply (rule ext)
         apply auto[1]
        apply simp
        apply (rule ext)
        by auto
    next
      case (Minus a21 a22)
      then show ?case
        apply simp
        apply (rule ext)
        by auto
    qed
  next
    case (Plus a11 a12)
    then show ?case
    proof(induct a2)
      case (L x)
      then show ?case
        apply (case_tac "a11 = a12")
         apply simp
        apply (rule ext)
        by auto
    next
      case (V x)
      then show ?case
        apply (case_tac "a11 = a12")
         apply simp
         apply (rule ext)
         apply auto[1]
        apply simp
        apply (rule ext)
        by auto
    next
      case (Plus a21 a22)
      then show ?case
        apply (case_tac "a11 = a12")
         apply (case_tac "a21 = a22")
          apply simp
          apply (case_tac "a22 = a12")
           apply simp
           apply (rule ext)
           apply auto[1]
          apply simp
        apply (rule ext)
          apply auto[1]
         apply simp
        apply (case_tac "a12 = a22")
        apply simp
        apply (rule ext)
        apply auto[1]
        apply simp
        apply (rule ext)
         apply auto[1]
         apply (case_tac "a21 = a22")
         apply simp
         apply (case_tac "a22 = a12")
          apply simp
          apply (rule ext)
          apply auto[1]
        apply simp
        apply (rule ext)
         apply auto[1]
        apply simp
        apply (case_tac "a22 = a12")
        apply simp
        apply (case_tac "a21 = a11")
        apply simp
          apply (rule ext)
          apply auto[1]
        apply simp
        apply (rule ext)
        apply auto[1]
        apply simp
        apply (case_tac "a22 = a11")
        apply simp
        apply (case_tac "a21 = a12")
        apply simp
        apply (rule ext)
        apply auto[1]
        apply simp
         apply (rule ext)
         apply auto[1]
        apply simp
        apply (rule ext)
        by auto
    next
      case (Minus a21 a22)
      then show ?case
        apply (case_tac "a11 = a12")
         apply simp
         apply (rule ext)
         apply auto[1]
        apply simp
        apply (rule ext)
        by auto
    qed
  next
    case (Minus a11 a12)
    then show ?case
    proof(induct a2)
      case (L x)
      then show ?case
        by simp
    next
      case (V x)
      then show ?case
        apply simp
        apply (rule ext)
        by auto
    next
      case (Plus a21 a22)
      then show ?case
        apply (case_tac "a21 = a22")
         apply simp
         apply (rule ext)
         apply auto[1]
        apply simp
        apply (rule ext)
        by auto
    next
      case (Minus a21 a22)
      then show ?case
        apply simp
        apply (case_tac "a21 = a11")
         apply simp
         apply (case_tac "a22 = a12")
          apply simp
          apply (rule ext)
          apply simp
         apply simp
        apply (rule ext)
         apply auto[1]
        apply simp
        apply (rule ext)
        by auto
    qed
  qed
next
case (Gt a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
    proof(induct a2)
      case (L v)
      then show ?case
        by simp
    next
      case (V v)
      then show ?case
        by simp
    next
      case (Plus a21 a22)
      then show ?case
        by simp
    next
      case (Minus a21 a22)
      then show ?case
        by simp
    qed
  next
    case (V x)
    then show ?case
    proof(induct a2)
      case (L x)
      then show ?case
        by simp
    next
      case (V v)
      then show ?case
        by simp
    next
      case (Plus a21 a22)
      then show ?case
        by simp
    next
      case (Minus a21 a22)
      then show ?case
        by simp
    qed
  next
    case (Plus a11 a12)
    then show ?case
    proof(induct a2)
      case (L x)
      then show ?case
        by simp
    next
      case (V x)
      then show ?case
        by simp
    next
      case (Plus a21 a22)
      then show ?case
        apply (case_tac "a11 = a12")
         apply (case_tac "a21 = a22")
          apply simp
         apply simp
        apply (case_tac "a12 = a21")
          apply simp
          apply (rule ext)
          apply simp
         apply simp
         apply (rule ext)
         apply simp
        apply (case_tac "a21 = a22")
         apply simp
         apply (case_tac "a11 = a22")
          apply simp
          apply (rule ext)
          apply simp
         apply simp
         apply (rule ext)
         apply simp
        apply simp
        apply (case_tac "a11 = a21")
         apply simp
         apply clarify
         apply (rule ext)
         apply simp
        apply simp
        apply (case_tac "a11 = a22")
         apply simp
         apply (case_tac "a12 = a21")
          apply simp
        apply (rule ext)
        apply simp
        apply clarify
          apply (simp add: fimage_funion)
          apply (simp add: comp_def make_gt_twice)
          apply auto[1]
         apply simp
         apply (rule ext)
         apply simp
        apply simp
        apply (rule ext)
        by simp
    next
      case (Minus a21 a22)
      then show ?case
        by simp
    qed
  next
    case (Minus a11 a12)
    then show ?case
    proof(induct a2)
      case (L x)
      then show ?case by simp
    next
      case (V x)
      then show ?case by simp
    next
      case (Plus a21 a22)
      then show ?case by simp
    next
      case (Minus a21 a22)
      then show ?case
        apply simp
        apply (case_tac "a11 = a21")
        apply simp
         apply clarify
         apply (rule ext)
         apply simp
        apply simp
        apply (rule ext)
        by simp
    qed
  qed
next
  case (Null x)
  then show ?case
    by simp
next
  have fold_split:  "\<forall>G1 G2 r. fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) (G1 @ G2)))) {||}
      = (fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) G1))) {||})
        |\<union>|
        (fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (map (\<lambda>(x, y). (x, not |`| y)) G2))) {||})"
  sorry
case (Nor G1 G2)
  then show ?case
    apply (simp del: fold_append map_append fset_of_list_append)
    apply (rule ext)
    apply standard
     defer
     apply simp
    apply(simp only: funion_fsubset_iff)
    apply standard
     apply simp
    apply (simp only: fold_split) 

    sorry
qed


lemma "(\<lambda>r. c r |\<union>| ffUnion (fset_of_list (map snd (filter (\<lambda>(a, uu). a = r) (guard2pairs c (Nor G1 G2)))))) =
(\<lambda>r. c r |\<union>| ffUnion (fset_of_list (map snd (filter (\<lambda>(a, uu). a = r) (guard2pairs c (Nor G1 G2))))))"
  by simp

lemma "medial (medial c t) t = medial c t"
  apply (simp add: medial_def)
  by (simp add: aux)

lemma "fold (|\<union>|)
     (map snd
       (filter (\<lambda>(a, uu). a = r)
         (guard2pairs (\<lambda>r. c r |\<union>| fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (guard2pairs c G))) {||})
           G)))
     {||} |\<subseteq>|
    c r |\<union>| fold (|\<union>|) (map snd (filter (\<lambda>(a, uu). a = r) (guard2pairs c G))) {||}"
proof(induct G)
case (Bc x)
  then show ?case
    apply (cases x)
     apply simp
    by simp
next
case (Eq x1a x2)
  then show ?case
    sorry
next
  case (Gt x1a x2)
  then show ?case sorry
next
case (Null x)
  then show ?case by simp
next
case (Nor G1 G2)
  then show ?case
    apply simp
qed

lemma "medial (medial c G) G r |\<subseteq>| medial c G r"
  apply (simp add: medial_def)

lemma subset_consistency: "\<forall>r. c' r |\<subseteq>| c r \<Longrightarrow> consistent c \<Longrightarrow> consistent c'"
  apply (simp add: consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)    
  by auto

lemma consistent_medial_medial: "consistent (medial (medial c t) t) \<Longrightarrow> consistent (medial c t)"
  by (metis anterior_subset_medial subset_consistency)

lemma medial_preserves_existing_elements: "x |\<in>| c r \<Longrightarrow> x |\<in>| medial c G r "
  using anterior_subset_medial by blast

lemma "(cval (conjoin (c r)) r s = true) = (fBall (c r) (\<lambda>c. cval c r s = true))"
proof(induct "c r")
  case empty
  then show ?case
    by (simp add: conjoin_def cval_true)
next
  have flip: "\<forall>x2 x1 c r. (finsert x1 x2 = c r) = (c r = finsert x1 x2)"
    by auto
  case (insert x1 x2)
  then show ?case
    apply (simp add: conjoin_def flip)

qed


lemma "consistent (medial (medial c G) G) \<Longrightarrow>
       fBall (Contexts.apply_updates (medial (medial c G) G) (medial c G) U r) (\<lambda>c. cval c r i = true) \<Longrightarrow>
       Contexts.apply_updates (medial c G) c U r \<noteq> {|Undef|} \<Longrightarrow>
       x |\<in>| Contexts.apply_updates (medial c G) c U r \<Longrightarrow> \<not> constrains_an_input r \<Longrightarrow> cval x r i = true"
proof(induct U)
  case Nil
  then show ?case
    apply (simp add: consistent_def)
    using medial_preserves_existing_elements by auto
next
  case (Cons a U)
  then show ?case
    apply (case_tac a)
    apply simp
    apply (case_tac b)
       apply simp
       apply (case_tac "r = V aa")
        apply simp+
       apply (case_tac "r = V aa")
       apply simp
       apply clarify
       apply simp
    using medial_preserves_existing_elements apply auto[1]
      apply simp+
     apply (case_tac "r = V aa")
      apply simp
      apply clarify
      apply simp
qed


lemma "subsumes c t t"
  apply (simp add: subsumes_def)
  apply (simp add: posterior_def Let_def)
  apply (case_tac "consistent (medial (medial c (Guard t)) (Guard t))")
   defer
   apply (simp add: cval_false)
  apply (simp add: consistent_medial_medial)
  apply clarify
  apply (simp add: remove_input_constraints_def)
  apply (case_tac "constrains_an_input r")
   apply auto[1]
  apply simp


(* If we can prove that medial (medial c t) t = medial t which it really should do *)
lemma "subsumes c t t"
  apply (simp add: subsumes_def medial_medial)
  apply (simp add: posterior_def medial_medial)
  apply (case_tac "consistent (medial c G)")
   apply (simp add: Let_def)
   defer
   apply simp
  apply (simp add: consistent_def remove_input_constraints_def)
  apply clarify
  using apply_updates by blast
end