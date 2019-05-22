theory GExp_Orderings
imports "efsm.GExp"
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

instantiation gexp :: "linorder" begin
fun less_gexpr :: "gexp \<Rightarrow> gexp \<Rightarrow> bool"  where
  "less_gexpr (Bc b1) (Bc b2) = (b1 < b2)" |
  "less_gexpr (Bc b1) (Eq e1 e2) = True" |
  "less_gexpr (Bc b1) (Gt e1 e2) = True" |
  "less_gexpr (Bc b1) (Nor g1 g2) = True" |
  "less_gexpr (Bc b1) (Null v) = True" |

  "less_gexpr (Eq e1 e2) (Bc b2) = False" |
  "less_gexpr (Eq e1 e2) (Eq e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))" |
  "less_gexpr (Eq e1 e2) (Gt e1' e2') = True" |
  "less_gexpr (Eq e1 e2) (Nor g1 g2) = True" |
  "less_gexpr (Eq e1 e2) (Null v) = True" |

  "less_gexpr (Gt e1 e2) (Bc b2) = False" |
  "less_gexpr (Gt e1 e2) (Eq e1' e2') = False" |
  "less_gexpr (Gt e1 e2) (Gt e1' e2') = ((less_aexpr e1 e1') \<or> ((e1 = e1') \<and> (less_aexpr e2 e2')))" |
  "less_gexpr (Gt e1 e2) (Nor g1 g2) = True" |
  "less_gexpr (Gt e1 e2) (Null v) = True" |

  "less_gexpr (Nor g1 g2) (Bc b2) = False" |
  "less_gexpr (Nor g1 g2) (Eq e1' e2') = False" |
  "less_gexpr (Nor g1 g2) (Gt e1' e2') = False" |
  "less_gexpr (Nor g1 g2) (Nor g1' g2') = ((less_gexpr g1 g1') \<or> ((g1 = g1') \<and> (less_gexpr g2 g2')))" |
  "less_gexpr (Nor g1 g2) (Null v) = True" |

  "less_gexpr (Null v) (Bc b2) = False" |
  "less_gexpr (Null v) (Eq e1' e2') = False" |
  "less_gexpr (Null v) (Gt e1' e2') = False" |
  "less_gexpr (Null v) (Nor g1' g2') = False" |
  "less_gexpr (Null v) (Null v') = (v < v')"

  definition less_eq_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool"
    where "less_eq_gexp e1 e2 \<equiv> (less_gexpr e1 e2) \<or> (e1 = e2)"

  definition less_gexp :: " gexp \<Rightarrow> gexp \<Rightarrow> bool"
    where "less_gexp e1 e2 \<equiv> less_gexpr e1 e2"

  lemma gexp_antisym: "less_gexpr x y = (\<not>(less_gexpr y x) \<and> (x \<noteq> y))"
  proof (induction x y rule: less_gexpr.induct)
    case (1 b1 b2)
    then show ?case
      by auto
    next
      case (2 b1 e1 e2)
      then show ?case
        by simp
    next
      case (3 b1 e1 e2)
      then show ?case
        by simp
    next
      case (4 b1 g1 g2)
      then show ?case
        by simp
    next
      case (5 b1 v)
      then show ?case
        by simp
    next
      case (6 e1 e2 b2)
      then show ?case
        by simp
    next
      case (7 e1 e2 e1' e2')
      then show ?case
        by (metis aexp_antisym less_gexpr.simps(7))
    next
      case (8 e1 e2 e1' e2')
      then show ?case
        by simp
    next
      case (9 e1 e2 g1 g2)
      then show ?case
        by simp
    next
      case (10 e1 e2 v)
      then show ?case
        by simp
    next
      case (11 e1 e2 b2)
      then show ?case
        by simp
    next
      case (12 e1 e2 e1' e2')
      then show ?case
        by simp
    next
      case (13 e1 e2 e1' e2')
      then show ?case
        by (metis aexp_antisym less_gexpr.simps(13))
    next
      case (14 e1 e2 g1 g2)
      then show ?case
        by simp
    next
      case (15 e1 e2 v)
      then show ?case
        by simp
    next
      case (16 g1 g2 b2)
      then show ?case
        by simp
    next
      case (17 g1 g2 e1' e2')
      then show ?case
        by simp
    next
      case (18 g1 g2 e1' e2')
      then show ?case
        by simp
    next
      case (19 g1 g2 g1' g2')
      then show ?case
        by auto
    next
      case (20 g1 g2 v)
      then show ?case
        by simp
    next
      case (21 v b2)
      then show ?case
        by simp
    next
      case (22 v e1' e2')
      then show ?case
        by simp
    next
      case (23 v e1' e2')
      then show ?case
        by simp
    next
      case (24 v g1' g2')
      then show ?case
        by simp
    next
      case (25 v v')
      then show ?case
        by auto
    qed


  lemma gexp_trans: "less_gexpr x y \<Longrightarrow> less_gexpr y z \<Longrightarrow> less_gexpr x z"
  proof (induction x y arbitrary: z rule: less_gexpr.induct)
    case (1 b1 b2)
    then show ?case
      by (cases z) auto
    next
      case (2 b1 e1 e2)
      then show ?case
      by (cases z) auto
    next
      case (3 b1 e1 e2)
      then show ?case
      by (cases z) auto
    next
      case (4 b1 g1 g2)
      then show ?case
      by (cases z) auto
    next
      case (5 b1 v)
      then show ?case
      by (cases z) auto
    next
      case (6 e1 e2 b2)
      then show ?case
      by (cases z) auto
    next
      case (7 e1 e2 e1' e2')
      then show ?case
      proof -
        have f1: "\<forall>g. (\<exists>b. g = Bc b) \<or> (\<exists>a aa. g = Eq a aa) \<or> (\<exists>a aa. g = Gt a aa) \<or> (\<exists>ga gb. g = Nor ga gb) \<or> (\<exists>v. g = Null v)"
          by (meson gexp.exhaust)
        obtain aa :: "gexp \<Rightarrow> aexp" and aaa :: "gexp \<Rightarrow> aexp" where
          f2: "\<forall>x0. (\<exists>v1 v2. x0 = Eq v1 v2) = (x0 = Eq (aa x0) (aaa x0))"
          by moura
        have "z = Eq (aa z) (aaa z) \<longrightarrow> less_aexpr e1 e1' \<or> less_gexpr (Eq e1 e2) z"
          by (metis (full_types) "7.prems"(1) "7.prems"(2) aexp_trans less_gexpr.simps(7))
        then have "z = Eq (aa z) (aaa z) \<longrightarrow> less_gexpr (Eq e1 e2) z"
          by (metis "7.prems"(2) aexp_trans less_gexpr.simps(7))
        then show ?thesis
          using f2 f1 by (metis (no_types) "7.prems"(2) less_gexpr.simps(10) less_gexpr.simps(6) less_gexpr.simps(8) less_gexpr.simps(9))
      qed
    next
      case (8 e1 e2 e1' e2')
      then show ?case
        by (metis gexp.exhaust gexp_antisym less_gexpr.simps(10) less_gexpr.simps(11) less_gexpr.simps(17) less_gexpr.simps(8))
    next
      case (9 e1 e2 g1 g2)
    then show ?case
      by (metis gexp.exhaust gexp_antisym less_gexpr.simps(10) less_gexpr.simps(4) less_gexpr.simps(8) less_gexpr.simps(9))
    next
      case (10 e1 e2 v)
      then show ?case
        by (metis gexp.exhaust gexp_antisym less_gexpr.simps(10) less_gexpr.simps(21) less_gexpr.simps(8) less_gexpr.simps(9))
    next
      case (11 e1 e2 b2)
      then show ?case
        by simp
    next
      case (12 e1 e2 e1' e2')
      then show ?case
        by simp
    next
      case (13 e1 e2 e1' e2')
      then show ?case
      proof (cases z)
        case (Bc x1)
        then show ?thesis
          using "13.prems"(2) by auto
      next
        case (Eq x21 x22)
        then show ?thesis
          using "13.prems"(2) by auto
      next
        case (Gt x31 x32)
        then show ?thesis
          using "13.prems"(1) "13.prems"(2) aexp_trans by auto
      next
        case (Nor x41 x42)
        then show ?thesis
          by simp
      next
        case (Null x5)
        then show ?thesis
          by simp
      qed
    next
      case (14 e1 e2 g1 g2)
      then show ?case
        by (metis gexp.exhaust gexp_antisym less_gexpr.simps(14) less_gexpr.simps(15) less_gexpr.simps(4) less_gexpr.simps(9))
    next
      case (15 e1 e2 v)
      then show ?case
        by (metis gexp.exhaust gexp_antisym less_gexpr.simps(10) less_gexpr.simps(14) less_gexpr.simps(15) less_gexpr.simps(21))
    next
      case (16 g1 g2 b2)
      then show ?case
        by simp
    next
      case (17 g1 g2 e1' e2')
      then show ?case
        by simp
    next
      case (18 g1 g2 e1' e2')
      then show ?case
        by simp
    next
      case (19 g1 g2 g1' g2')
      then show ?case
      proof -
        have f1: "\<forall>g. (\<exists>b. g = Bc b) \<or> (\<exists>a aa. g = Eq a aa) \<or> (\<exists>a aa. g = Gt a aa) \<or> (\<exists>ga gb. g = Nor ga gb) \<or> (\<exists>v. g = Null v)"
          by (meson gexp.exhaust)
        obtain gg :: "gexp \<Rightarrow> gexp" and gga :: "gexp \<Rightarrow> gexp" where
          f2: "\<forall>x0. (\<exists>v1 v2. x0 = Nor v1 v2) = (x0 = Nor (gg x0) (gga x0))"
          by moura
        obtain aa :: "gexp \<Rightarrow> aexp" and aaa :: "gexp \<Rightarrow> aexp" where
          f3: "\<forall>x0. (\<exists>v1 v2. x0 = Eq v1 v2) = (x0 = Eq (aa x0) (aaa x0))"
          by moura
        have "z \<noteq> Eq (aa z) (aaa z)"
          by (metis (no_types) "19.prems"(2) less_gexpr.simps(17))
        then obtain vv :: "gexp \<Rightarrow> aexp" where
          "z = Null (vv z) \<or> z = Nor (gg z) (gga z)"
          using f3 f2 f1 by (metis (no_types) "19.prems"(2) less_gexpr.simps(16) less_gexpr.simps(18))
        then show ?thesis
          by (metis "19.IH"(1) "19.IH"(2) "19.prems"(1) "19.prems"(2) less_gexpr.simps(19) less_gexpr.simps(20))
      qed
    next
      case (20 g1 g2 v)
      then show ?case
        by (metis gexp.exhaust gexp_antisym less_gexpr.simps(10) less_gexpr.simps(15) less_gexpr.simps(24) less_gexpr.simps(5))
    next
      case (21 v b2)
      then show ?case
        by simp
    next
      case (22 v e1' e2')
    then show ?case
      by simp
    next
      case (23 v e1' e2')
      then show ?case
        by simp
    next
      case (24 v g1' g2')
      then show ?case
        by simp
    next
      case (25 v v')
      then show ?case
        by (metis dual_order.strict_trans gexp.exhaust less_gexpr.simps(21) less_gexpr.simps(22) less_gexpr.simps(23) less_gexpr.simps(24) less_gexpr.simps(25))
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
