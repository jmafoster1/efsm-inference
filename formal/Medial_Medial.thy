theory Medial_Medial
imports Contexts
begin

lemma make_lt_expand:  "make_lt |`| (cp |\<union>| ca2) = (make_lt |`| cp) |\<union>| (make_lt |`| ca2)"
  by (simp add: fimage_funion)

lemma make_lt_twice: "make_lt (make_lt x) = make_lt x"
proof(induct x)
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
  case (Not x)
  then show ?case
    by simp
next
case (And x1 x2)
  then show ?case
    by simp
qed

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

lemma "pairs2context
     (flatten (guard2pairs (pairs2context (flatten (guard2pairs c G) []) c) G) [])
     (pairs2context (flatten (guard2pairs c G) []) c) =
    pairs2context (flatten (guard2pairs c G) []) c"
proof(induct G)
case (Bc x)
  then show ?case
    apply (case_tac x)
     apply simp
    apply (rule ext)
    by simp
next
  case (Eq a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
    proof(induct a2)
      case (L v)
      then show ?case
        apply (rule ext)
        by simp
    next
      case (V x)
      then show ?case
        apply (rule ext)
        by simp
    next
      case (Plus a21 a22)
      then show ?case
        apply simp
        apply (rule ext)
        by simp
    next
      case (Minus a21 a22)
      then show ?case
        apply simp
        apply (rule ext)
        by simp
    qed
  next
    case (V x)
    then show ?case
    proof(induct a2)
      case (L v)
      then show ?case
        apply (rule ext)
        by simp
    next
      case (V v)
      then show ?case
        apply (rule ext)
        by simp
    next
      case (Plus a21 a22)
      then show ?case
        apply (case_tac "a21 = a22")
         apply simp
         apply (rule ext)
         apply simp
        apply simp
        apply (rule ext)
        by simp
    next
      case (Minus a21 a22)
      then show ?case
        apply simp
        apply (rule ext)
        by simp
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
         apply simp
        apply simp
        apply (rule ext)
        by simp
    next
      case (V x)
      then show ?case
        apply (case_tac "a11 = a12")
         apply simp
         apply (rule ext)
         apply simp
        apply simp
        apply (rule ext)
        by simp
    next
      case (Plus a21 a22)
      then show ?case
        apply (case_tac "a11 = a12")
         apply (case_tac "a21 = a22")
          apply simp
          apply (case_tac "a22 = a12")
           apply simp
           apply (rule ext)
           apply simp
          apply simp
          apply (rule ext)
          apply simp
         apply simp
         apply (case_tac "a12 = a21")
          apply simp
          apply (rule ext)
          apply auto[1]
         apply simp
         apply (rule ext)
         apply auto[1]
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
        apply (case_tac "a11 = a22")
         apply simp
         apply (case_tac "a12 = a21")
          apply simp
          apply (rule ext)
          apply auto[1]
         apply simp
         apply (rule ext)
         apply auto[1]
        apply simp
        apply (case_tac "a11 = a21")
         apply simp
         apply (case_tac "a12 = a22")
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
         apply simp
        apply simp
        apply (rule ext)
        by simp
    qed
  next
    case (Minus a11 a12)
    then show ?case
    proof(induct a2)
      case (L x)
      then show ?case
        apply simp
        apply (rule ext)
        by simp
    next
      case (V x)
      then show ?case
        apply simp
        apply (rule ext)
        by simp
    next
      case (Plus a21 a22)
      then show ?case
        apply (case_tac "a21 = a22")
         apply simp
         apply (rule ext)
         apply simp
        apply simp
        apply (rule ext)
        by simp
    next
      case (Minus a21 a22)
      then show ?case
        apply simp
        apply (case_tac "a11 = a21")
         apply simp
         apply (case_tac "a12 = a22")
          apply simp
          apply (rule ext)
          apply simp
         apply simp
         apply (rule ext)
         apply simp
        apply simp
        apply (rule ext)
        by simp
    qed
  qed
next
  case (Gt a1 a2)
  then show ?case
  proof(induct a1)
    case (L x)
    then show ?case
    proof(induct a2)
      case (L y)
      then show ?case
        apply (case_tac x)
         apply (case_tac y)
          apply simp
          apply (case_tac "x1 = x1a")
           apply simp
           apply (rule ext)
           apply simp
          apply simp
          apply (rule ext)
          apply simp
         apply simp
         apply (rule ext)
         apply simp
        apply simp
        apply safe
         apply (rule ext)
         apply simp
        apply (rule ext)
        by simp
    next
      case (V x)
      then show ?case
        apply simp
        apply (rule ext)
        by simp
    next
      case (Plus a21 a22)
      then show ?case
        apply simp
        apply (rule ext)
        by simp
    next
      case (Minus a21 a22)
      then show ?case
        apply simp
        apply (rule ext)
        by simp
    qed
  next
    case (V x)
    then show ?case
      apply simp
      apply (case_tac "a2 = V x")
       apply simp
       apply (rule ext)
       apply simp
      apply simp
      apply (rule ext)
      by simp
  next
    case (Plus a11 a12)
    then show ?case
      apply (case_tac "a11 = a12")
       apply simp
       apply (case_tac "Plus a12 a12 = a2")
        apply simp
        apply (rule ext)
        apply simp
       apply simp
       apply (rule ext)
       apply simp
      apply simp
      apply (case_tac "Plus a12 a11 = a2")
       apply simp
       apply (case_tac "Plus a11 a12 = a2")
        apply simp
        apply (rule ext)
        apply simp
       apply simp
       apply (rule ext)
       apply (simp add: union_make_lt)
      apply simp
      apply (case_tac "Plus a11 a12 = a2")
       apply simp
       apply (rule ext)
       apply simp
      apply simp
      apply (rule ext)
      by simp
  next
    case (Minus a11 a12)
    then show ?case
      apply simp
      apply (case_tac "Minus a11 a12 = a2")
       apply simp
       apply (rule ext)
       apply simp
      apply simp
      apply (rule ext)
      by simp
  qed
next
  case (Nor G1 G2)
  then show ?case
    apply simp
    apply (rule ext)
    
next
  case (Null x)
  then show ?case
    apply simp
    apply (rule ext)
    by simp
qed
      

lemma "medial (medial c t) t = medial c t"
  apply (simp add: medial_def)

end