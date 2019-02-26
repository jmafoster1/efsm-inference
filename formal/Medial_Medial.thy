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

lemma "x |\<notin>| ffUnion (snd |`| ffilter (\<lambda>(a, uu). a = r) (ffUnion (guard2pairs c |`| G))) \<Longrightarrow>
           x |\<in>|
           ffUnion
            (snd |`|
             ffilter (\<lambda>(a, uu). a = r)
              (ffUnion (guard2pairs (\<lambda>r. c r |\<union>| ffUnion (snd |`| ffilter (\<lambda>(a, uu). a = r) (ffUnion (guard2pairs c |`| G)))) |`| G))) \<Longrightarrow>
           ffUnion
            (snd |`|
             ffilter (\<lambda>(a, uu). a = r)
              (ffUnion (guard2pairs (\<lambda>r. c r |\<union>| ffUnion (snd |`| ffilter (\<lambda>(a, uu). a = r) (ffUnion (guard2pairs c |`| G)))) |`| G))) |\<subseteq>|
           c r"
  oops



lemma "medial (medial c G) G = medial c G"
  apply (simp add: medial_def)
  apply (rule ext)
  apply safe
  apply standard
   apply simp
  oops

end