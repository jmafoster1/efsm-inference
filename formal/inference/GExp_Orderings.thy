theory GExp_Orderings
imports "../OPred" "../GExp" "~~/src/HOL/Library/List_Lexorder"
begin

(* datatype vname = I nat | R nat *)
(* datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Nor gexp gexp | Null vname *)

instantiation aexp :: "linorder" begin
fun less_aexpr :: "aexp \<Rightarrow> aexp \<Rightarrow> bool"  where
  "less_aexpr (L l1) (L l2) = (l1 < l2)" |
  "less_aexpr (L l1) (V v2) = True" |
  "less_aexpr (L l1) (Plus e1 e2) = True" |
  "less_aexpr (L l1) (Minus e1 e2) = True" |

  "less_aexpr (V v1) (L l1) = False" |
  "less_aexpr (V v1) (V v2) = (v1 < v2)" |
  "less_aexpr (V v1) (Plus e1 e2) = True" |
  "less_aexpr (V v1) (Minus e1 e2) = True" |

  "less_aexpr (Plus e1 e2) (L l2) = False" |
  "less_aexpr (Plus e1 e2) (V v2) = False" |
  "less_aexpr (Plus e1 e2) (Plus e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))" |
  "less_aexpr (Plus e1 e2) (Minus e1' e2') = True" |

  "less_aexpr (Minus e1 e2) (L l2) = False" |
  "less_aexpr (Minus e1 e2) (V v2) = False" |
  "less_aexpr (Minus e1 e2) (Plus e1' e2') = False" |
  "less_aexpr (Minus e1 e2) (Minus e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))"

  definition less_eq_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool"
    where "less_eq_aexp e1 e2 \<equiv> (less_aexpr e1 e2) \<or> (e1 = e2)"

  definition less_aexp :: " aexp \<Rightarrow> aexp \<Rightarrow> bool"
    where "less_aexp e1 e2 \<equiv> less_aexpr e1 e2"

  lemma aexp_antisym: "less_aexpr x y = (\<not>(less_aexpr y x) \<and> (x \<noteq> y))"
    by (induction x y rule: less_aexpr.induct) auto


  lemma aexp_trans: "less_aexpr x y \<Longrightarrow> less_aexpr y z \<Longrightarrow> less_aexpr x z"
  proof (induction x y arbitrary: z rule: less_aexpr.induct)
    case (1 l1 l2)
    then show ?case
      by (cases z) auto
  next
    case (2 l1 v2)
    then show ?case
      by (cases z) auto
  next
    case (3 l1 e1 e2)
    then show ?case
      by (cases z) auto
  next
    case (4 l1 e1 e2)
    then show ?case
      by (cases z) auto
  next
    case (5 v1 l1)
    then show ?case
      by (cases z) auto
  next
    case (6 v1 v2)
    then show ?case
      by (cases z) auto
  next
    case (7 v1 e1 e2)
    then show ?case
      by (cases z) auto
  next
    case (8 v1 e1 e2)
    then show ?case
      by (cases z) auto
  next
  case (9 e1 e2 l2)
    then show ?case
      by (cases z) auto
  next
  case (10 e1 e2 v2)
  then show ?case
      by (cases z) auto
  next
    case (11 e1 e2 e1' e2')
    then show ?case
      by (cases z) auto
  next
    case (12 e1 e2 e1' e2')
    then show ?case
      by (cases z) auto
  next
    case (13 e1 e2 l2)
    then show ?case
      by (cases z) auto
  next
    case (14 e1 e2 v2)
    then show ?case
      by (cases z) auto
  next
    case (15 e1 e2 e1' e2')
    then show ?case
      by (cases z) auto
  next
    case (16 e1 e2 e1' e2')
    then show ?case
      by (cases z) auto
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

instantiation opred :: linorder begin
fun less_opred :: "opred \<Rightarrow> opred \<Rightarrow> bool" where
  "less_opred (opred.Bc b1) (opred.Bc b2) = (b1 < b2)" |
  "less_opred (opred.Bc b1) _ = True" |

  "less_opred (opred.Eq e2) (opred.Bc b2) = False" |
  "less_opred (opred.Eq e2) (opred.Eq e2') = (less_aexpr e2 e2')" |
  "less_opred (opred.Eq e2) _ = True" |

  "less_opred (opred.Gt e2) (opred.Bc b2) = False" |
  "less_opred (opred.Gt e2) (opred.Eq e2') = False" |
  "less_opred (opred.Gt e2) (opred.Gt e2') = (less_aexpr e2 e2')" |
  "less_opred (opred.Gt e2) _ = True" |

  "less_opred (opred.Null) (opred.Bc b2) = False" |
  "less_opred (opred.Null) (opred.Eq e2') = False" |
  "less_opred (opred.Null) (opred.Gt e2') = False" |
  "less_opred (opred.Null) (opred.Null) = False" |
  "less_opred (opred.Null) _ = True" |

  "less_opred (opred.In vc) (opred.Nor v va) = True" |
  "less_opred (opred.In vc) (opred.In va) = (vc < va)" |
  "less_opred (opred.In vc) _ = False" |

  "less_opred (opred.Nor g1 g2) (opred.Nor g1' g2') = ((less_opred g1 g1') \<or> ((g1 = g1') \<and> (less_opred g2 g2')))" |
  "less_opred (opred.Nor g1 g2) _ = False"

definition less_eq_opred :: "opred \<Rightarrow> opred \<Rightarrow> bool" where
  "less_eq_opred p1 p2 \<equiv> p1 < p2 \<or> p1 = p2"

lemma opred_first: "((x::opred) < y) = (x \<le> y \<and> \<not> y \<le> x)"
  apply (induct x y rule: less_opred.induct)
                      apply (simp_all add: less_eq_opred_def)
      apply auto[1]
  using aexp_antisym apply blast
  using aexp_antisym apply blast
  by auto

lemma opred_reflexive: "(x::opred) \<le> x"
  by (simp add: less_eq_opred_def)

lemma opred_antisym: "(x::opred) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  using opred_first less_eq_opred_def by blast

lemma opred_linear: "(x::opred) \<le> y \<or> y \<le> x"
  apply (induct x y rule: less_opred.induct)
                      apply (simp_all add: less_eq_opred_def)
      apply auto[1]
  using aexp_antisym apply blast
  using aexp_antisym apply blast
  by auto

lemma opred_trans: "(x::opred) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
proof (induct x y arbitrary: z rule: less_opred.induct)
case (1 b1 b2)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("2_1" b1 v)
then show ?case using less_eq_opred_def by (cases z, auto)
next
case ("2_2" b1 v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("2_3" b1)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("2_4" b1 v)
then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("2_5" b1 v va)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (3 e2 b2)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (4 e2 e2')
  then show ?case
    by (metis (full_types) opred_linear aexp_trans enumerate_strings.cases less_eq_opred_def less_opred.simps(10) less_opred.simps(2) less_opred.simps(28) less_opred.simps(33) less_opred.simps(8) less_opred.simps(9) opred_first)
next
  case ("5_1" e2 v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("5_2" e2)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("5_3" e2 v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("5_4" e2 v va)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (6 e2 b2)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (7 e2 e2')
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (8 e2 e2')
  then show ?case using less_eq_opred_def
  proof -
    obtain vvs :: "opred \<Rightarrow> value list" where
      f1: "\<forall>x0. (\<exists>v1. x0 = opred.In v1) = (x0 = opred.In (vvs x0))"
      by moura
    obtain zz :: "opred \<Rightarrow> opred" and zza :: "opred \<Rightarrow> opred" where
      f2: "\<forall>x0. (\<exists>v1 v2. x0 = opred.Nor v1 v2) = (x0 = opred.Nor (zz x0) (zza x0))"
      by moura
    obtain aa :: "opred \<Rightarrow> aexp" where
      f3: "\<forall>x0. (\<exists>v1. x0 = opred.Gt v1) = (x0 = opred.Gt (aa x0))"
      by moura
    obtain aaa :: "opred \<Rightarrow> aexp" where
      "\<forall>x0. (\<exists>v1. x0 = opred.Eq v1) = (x0 = opred.Eq (aaa x0))"
      by moura
    then obtain bb :: "opred \<Rightarrow> bool" where
      f4: "z = opred.Bc (bb z) \<or> z = opred.Eq (aaa z) \<or> z = opred.Gt (aa z) \<or> z = opred.Null \<or> z = opred.Nor (zz z) (zza z) \<or> z = opred.In (vvs z)"
      using f3 f2 f1 by (meson enumerate_strings.cases)
    { assume "opred.Bc True \<noteq> z"
      { assume "z \<noteq> opred.Bc (bb z) \<and> z \<noteq> opred.Eq (aaa z)"
        moreover
        { assume "z = opred.Gt (aa z)"
          then have "opred.Gt e2' < z \<longrightarrow> (opred.Gt e2 < z \<or> opred.Gt e2 = z) \<or> opred.Gt e2 \<le> z"
            by (metis "8.prems"(1) aexp_trans less_eq_opred_def less_opred.simps(15)) }
        ultimately have "opred.Gt e2' < z \<longrightarrow> opred.Gt e2 \<le> z"
          using f4 by (metis (no_types) less_eq_opred_def less_opred.simps(16) less_opred.simps(17) less_opred.simps(18)) }
      then have "opred.Gt e2' < z \<longrightarrow> opred.Gt e2 \<le> z"
        by (metis less_opred.simps(13) less_opred.simps(14)) }
    then show ?thesis
      by (metis "8.prems"(1) "8.prems"(2) less_eq_opred_def less_opred.simps(13))
  qed
next
  case ("9_1" e2)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("9_2" e2 v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("9_3" e2 v va)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (10 b2)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (11 e2')
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (12 e2')
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case 13
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("14_1" v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("14_2" v va)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (15 vc v va)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (16 vc va)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("17_1" vc v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("17_2" vc v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("17_3" vc v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("17_4" vc)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case (18 g1 g2 g1' g2')
  then show ?case using less_eq_opred_def
    apply (cases z)
         apply simp+
    using opred_first by blast
next
  case ("19_1" g1 g2 v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("19_2" g1 g2 v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("19_3" g1 g2 v)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("19_4" g1 g2)
  then show ?case using less_eq_opred_def by (cases z, auto)
next
  case ("19_5" g1 g2 v)
  then show ?case using less_eq_opred_def by (cases z, auto)
qed

instance
  apply standard
      apply (simp add: opred_first)
     apply (simp add: opred_reflexive)
  using opred_trans apply blast
   apply (simp add: opred_antisym)
  by (simp add: opred_linear)
end

end
