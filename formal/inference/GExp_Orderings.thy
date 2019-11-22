theory GExp_Orderings
imports "../EFSM/GExp" "~~/src/HOL/Library/List_Lexorder"
begin

(* datatype vname = I nat | R nat *)
(* datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Nor gexp gexp | Null vname *)

instantiation aexp :: "linorder" begin
fun less_aexpr :: "aexp \<Rightarrow> aexp \<Rightarrow> bool"  where
  "less_aexpr (L l1) (L l2) = (l1 < l2)" |
  "less_aexpr (L l1) (V v2) = True" |
  "less_aexpr (L l1) (Plus e1 e2) = True" |
  "less_aexpr (L l1) (Minus e1 e2) = True" |
  "less_aexpr (L l1) (Times e1 e2) = True" |

  "less_aexpr (V v1) (L l1) = False" |
  "less_aexpr (V v1) (V v2) = (v1 < v2)" |
  "less_aexpr (V v1) (Plus e1 e2) = True" |
  "less_aexpr (V v1) (Minus e1 e2) = True" |
  "less_aexpr (V v1) (Times e1 e2) = True" |

  "less_aexpr (Plus e1 e2) (L l2) = False" |
  "less_aexpr (Plus e1 e2) (V v2) = False" |
  "less_aexpr (Plus e1 e2) (Plus e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))" |
  "less_aexpr (Plus e1 e2) (Minus e1' e2') = True" |
  "less_aexpr (Plus e1 e2) (Times e1' e2') = True" |

  "less_aexpr (Minus e1 e2) (L l2) = False" |
  "less_aexpr (Minus e1 e2) (V v2) = False" |
  "less_aexpr (Minus e1 e2) (Plus e1' e2') = False" |
  "less_aexpr (Minus e1 e2) (Minus e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))" |
  "less_aexpr (Minus e1 e2) (Times e1' e2') = True" |

  "less_aexpr (Times e1 e2) (L l2) = False" |
  "less_aexpr (Times e1 e2) (V v2) = False" |
  "less_aexpr (Times e1 e2) (Plus e1' e2') = False" |
  "less_aexpr (Times e1 e2) (Minus e1' e2') = False" |
  "less_aexpr (Times e1 e2) (Times e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))"

  definition less_eq_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool"
    where "less_eq_aexp e1 e2 \<equiv> (less_aexpr e1 e2) \<or> (e1 = e2)"

  definition less_aexp :: " aexp \<Rightarrow> aexp \<Rightarrow> bool"
    where "less_aexp e1 e2 \<equiv> less_aexpr e1 e2"

  lemma aexp_antisym: "less_aexpr x y = (\<not>(less_aexpr y x) \<and> (x \<noteq> y))"
    by (induction x y rule: less_aexpr.induct) auto

lemma aexp_trans: "less_aexpr x y \<Longrightarrow> less_aexpr y z \<Longrightarrow> less_aexpr x z"
  proof (induction x y arbitrary: z rule: less_aexpr.induct)
    case (1 l1 l2)
    then show ?case by (cases z, auto)
  next
    case (2 l1 v2)
    then show ?case by (cases z, auto)
  next
    case (3 l1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (4 l1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (5 l1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (6 v1 l1)
    then show ?case by (cases z, auto)
  next
    case (7 v1 v2)
    then show ?case by (cases z, auto)
  next
    case (8 v1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (9 v1 e1 e2)
  then show ?case by (cases z, auto)
  next
  case (10 v1 e1 e2)
    then show ?case by (cases z, auto)
  next
    case (11 e1 e2 l2)
    then show ?case by (cases z, auto)
  next
    case (12 e1 e2 v2)
    then show ?case by (cases z, auto)
  next
    case (13 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (14 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (15 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (16 e1 e2 l2)
    then show ?case by (cases z, auto)
  next
    case (17 e1 e2 v2)
    then show ?case by (cases z, auto)
  next
  case (18 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
  case (19 e1 e2 e1' e2')
  then show ?case by (cases z, auto)
  next
    case (20 e1 e2 e1' e2')
  then show ?case by (cases z, auto)
  next
    case (21 e1 e2 l2)
  then show ?case by (cases z, auto)
  next
    case (22 e1 e2 v2)
    then show ?case by (cases z, auto)
  next
    case (23 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  next
    case (24 e1 e2 e1' e2')
  then show ?case by (cases z, auto)
  next
    case (25 e1 e2 e1' e2')
    then show ?case by (cases z, auto)
  qed

  instance proof
    fix x y :: aexp
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
       using aexp_antisym less_eq_aexp_def less_aexp_def by metis
  next
    fix x :: aexp
    show "(x \<le> x)"
      by (simp add: less_eq_aexp_def)
  next
    fix x y z :: aexp
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using aexp_trans by (metis less_eq_aexp_def)
  next
    fix x y :: aexp
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      unfolding less_eq_aexp_def using aexp_antisym by blast
  next
    fix x y :: aexp
    show "x \<le> y \<or> y \<le> x"
      unfolding less_eq_aexp_def using aexp_antisym by blast
  qed
end

(* datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Null aexp | In vname "value list" | Nor gexp gexp *)

instantiation gexp :: "linorder" begin
fun less_gexpr :: "gexp \<Rightarrow> gexp \<Rightarrow> bool"  where
  "less_gexpr (Bc b1) (Bc b2) = (b1 < b2)" |
  "less_gexpr (Bc b1) _ = True" |

  "less_gexpr (Eq e1 e2) (Bc b2) = False" |
  "less_gexpr (Eq e1 e2) (Eq e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))" |
  "less_gexpr (Eq e1 e2) _ = True" |

  "less_gexpr (Gt e1 e2) (Bc b2) = False" |
  "less_gexpr (Gt e1 e2) (Eq e1' e2') = False" |
  "less_gexpr (Gt e1 e2) (Gt e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))" |
  "less_gexpr (Gt e1 e2) _ = True" |

  "less_gexpr (Null v) (Bc b2) = False" |
  "less_gexpr (Null v) (Eq e1' e2') = False" |
  "less_gexpr (Null v) (Gt e1' e2') = False" |
  "less_gexpr (Null v) (Null v') = (v < v')" |
  "less_gexpr (Null v) _ = True" |

  "less_gexpr (In vb vc) (Nor v va) = True" |
  "less_gexpr (In vb vc) (In v va) = (vb < v \<or> (vb = v \<and> vc < va))" |
  "less_gexpr (In vb vc) _ = False" |

  "less_gexpr (Nor g1 g2) (Nor g1' g2') = ((less_gexpr g1 g1') \<or> ((g1 = g1') \<and> (less_gexpr g2 g2')))" |
  "less_gexpr (Nor g1 g2) _ = False"


  definition less_eq_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool"
    where "less_eq_gexp e1 e2 \<equiv> (less_gexpr e1 e2) \<or> (e1 = e2)"

  definition less_gexp :: " gexp \<Rightarrow> gexp \<Rightarrow> bool"
    where "less_gexp e1 e2 \<equiv> less_gexpr e1 e2"

  lemma gexp_antisym: "less_gexpr x y = (\<not>(less_gexpr y x) \<and> (x \<noteq> y))"
    apply (induction x y rule: less_gexpr.induct)
                        apply auto[1]
                        apply simp+
    using aexp_antisym apply blast
                        apply simp+
    using aexp_antisym apply blast
    by auto

lemma gexp_trans: "less_gexpr x y \<Longrightarrow> less_gexpr y z \<Longrightarrow> less_gexpr x z"
proof (induction x y arbitrary: z rule: less_gexpr.induct)
case (1 b1 b2)
then show ?case 
    apply (cases z)
    by auto
next
  case ("2_1" b1 v va)
  then show ?case 
    apply (cases z)
    by auto
next
  case ("2_2" b1 v va)
  then show ?case 
    apply (cases z)
    by auto
next
  case ("2_3" b1 v)
  then show ?case 
    apply (cases z)
    by auto
next
  case ("2_4" b1 v va)
  then show ?case 
    apply (cases z)
    by auto
next
  case ("2_5" b1 v va)
  then show ?case 
    apply (cases z)
    by auto
next
  case (3 e1 e2 b2)
  then show ?case 
    apply (cases z)
    by auto
next
  case (4 e1 e2 e1' e2')
  then show ?case 
    apply (cases z)
         apply simp+
    using aexp_trans apply blast
    by auto
next
case ("5_1" e1 e2 v va)
  then show ?case 
    apply (cases z)
    by auto
next
case ("5_2" e1 e2 v)
  then show ?case 
    apply (cases z)
    by auto
next
  case ("5_3" e1 e2 v va)
  then show ?case 
    apply (cases z)
    by auto
next
  case ("5_4" e1 e2 v va)
  then show ?case 
    apply (cases z)
    by auto
next
  case (6 e1 e2 b2)
  then show ?case 
    apply (cases z)
    by auto
next
  case (7 e1 e2 e1' e2')
  then show ?case 
    apply (cases z)
    by auto
next
  case (8 e1 e2 e1' e2')
  then show ?case 
    apply (cases z)
         apply simp+
    using aexp_trans apply blast
    by auto
next
  case ("9_1" e1 e2 v)
  then show ?case 
    apply (cases z)
    by auto
next
  case ("9_2" e1 e2 v va)
  then show ?case 
    apply (cases z)
    by auto
next
  case ("9_3" e1 e2 v va)
  then show ?case 
    apply (cases z)
    by auto
next
  case (10 v b2)
  then show ?case
    apply (cases z)
    by auto
next
  case (11 v e1' e2')
  then show ?case
    apply (cases z)
    by auto
next
  case (12 v e1' e2')
  then show ?case
    apply (cases z)
    by auto
next
  case (13 v v')
  then show ?case
    apply (cases z)
    by auto
next
  case ("14_1" v va vb)
  then show ?case
    apply (cases z)
    by auto
next
  case ("14_2" v va vb)
  then show ?case
    apply (cases z)
    by auto
next
  case (15 vb vc v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (16 vb vc v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("17_1" vb vc v)
  then show ?case
    apply (cases z)
    by auto
next
  case ("17_2" vb vc v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("17_3" vb vc v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("17_4" vb vc v)
  then show ?case
    apply (cases z)
    by auto
next
  case (18 g1 g2 g1' g2')
  then show ?case
    apply (cases z)
    by auto
next
  case ("19_1" g1 g2 v)
  then show ?case 
    by simp
next
  case ("19_2" g1 g2 v va)
  then show ?case 
    by simp
next
  case ("19_3" g1 g2 v va)
  then show ?case
    by simp
next
  case ("19_4" g1 g2 v)
  then show ?case 
    by simp
next
  case ("19_5" g1 g2 v va)
  then show ?case
    by simp
qed
                        

  instance proof
    fix x y :: gexp
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
       using gexp_antisym less_eq_gexp_def less_gexp_def by metis
  next
    fix x :: gexp
    show "(x \<le> x)"
      by (simp add: less_eq_gexp_def)
  next
    fix x y z :: gexp
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using gexp_trans by (metis less_eq_gexp_def)
  next
    fix x y :: gexp
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      unfolding less_eq_gexp_def using gexp_antisym by blast
  next
    fix x y :: gexp
    show "x \<le> y \<or> y \<le> x"
      unfolding less_eq_gexp_def using gexp_antisym by blast
  qed
end

end
