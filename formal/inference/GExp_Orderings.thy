theory GExp_Orderings
imports "../EFSM/GExp" "~~/src/HOL/Library/List_Lexorder"
begin

(* datatype vname = I nat | R nat *)
(* datatype gexp_o = Bc bool | Eq aexp_o aexp_o | Gt aexp_o aexp_o | Nor gexp_o gexp_o | Null vname *)

instantiation aexp_o :: "linorder" begin
fun less_aexp_o :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> bool"  where
  "less_aexp_o (aexp_o.L l1) (aexp_o.L l2) = (l1 < l2)" |
  "less_aexp_o (aexp_o.L l1) (aexp_o.V v2) = True" |
  "less_aexp_o (aexp_o.L l1) (Plus e1 e2) = True" |
  "less_aexp_o (aexp_o.L l1) (Minus e1 e2) = True" |
  "less_aexp_o (aexp_o.L l1) (Times e1 e2) = True" |

  "less_aexp_o (aexp_o.V v1) (aexp_o.L l1) = False" |
  "less_aexp_o (aexp_o.V v1) (aexp_o.V v2) = (v1 < v2)" |
  "less_aexp_o (aexp_o.V v1) (Plus e1 e2) = True" |
  "less_aexp_o (aexp_o.V v1) (Minus e1 e2) = True" |
  "less_aexp_o (aexp_o.V v1) (Times e1 e2) = True" |

  "less_aexp_o (Plus e1 e2) (aexp_o.L l2) = False" |
  "less_aexp_o (Plus e1 e2) (aexp_o.V v2) = False" |
  "less_aexp_o (Plus e1 e2) (Plus e1' e2') = ((less_aexp_o e1 e1') \<or> ((e1 = e1') \<and> (less_aexp_o e2 e2')))" |
  "less_aexp_o (Plus e1 e2) (Minus e1' e2') = True" |
  "less_aexp_o (Plus e1 e2) (Times e1' e2') = True" |

  "less_aexp_o (Minus e1 e2) (aexp_o.L l2) = False" |
  "less_aexp_o (Minus e1 e2) (aexp_o.V v2) = False" |
  "less_aexp_o (Minus e1 e2) (Plus e1' e2') = False" |
  "less_aexp_o (Minus e1 e2) (Minus e1' e2') = ((less_aexp_o e1 e1') \<or> ((e1 = e1') \<and> (less_aexp_o e2 e2')))" |
  "less_aexp_o (Minus e1 e2) (Times e1' e2') = True" |

  "less_aexp_o (Times e1 e2) (aexp_o.L l2) = False" |
  "less_aexp_o (Times e1 e2) (aexp_o.V v2) = False" |
  "less_aexp_o (Times e1 e2) (Plus e1' e2') = False" |
  "less_aexp_o (Times e1 e2) (Minus e1' e2') = False" |
  "less_aexp_o (Times e1 e2) (Times e1' e2') = ((less_aexp_o e1 e1') \<or> ((e1 = e1') \<and> (less_aexp_o e2 e2')))"

  definition less_eq_aexp_o :: "aexp_o \<Rightarrow> aexp_o \<Rightarrow> bool"
    where "less_eq_aexp_o e1 e2 \<equiv> (e1 < e2) \<or> (e1 = e2)"

  lemma aexp_o_antisym: "(x::aexp_o) < y = (\<not>(y < x) \<and> (x \<noteq> y))"
    by (induction x y rule: less_aexp_o.induct) auto

lemma aexp_o_trans: "(x::aexp_o) < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  proof (induction x y arbitrary: z rule: less_aexp_o.induct)
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
    fix x y z :: aexp_o
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      by (metis aexp_o_antisym less_eq_aexp_o_def)
    show "(x \<le> x)"
      by (simp add: less_eq_aexp_o_def)
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using aexp_o_trans by (metis less_eq_aexp_o_def)
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      unfolding less_eq_aexp_o_def using aexp_o_antisym by blast
    show "x \<le> y \<or> y \<le> x"
      unfolding less_eq_aexp_o_def using aexp_o_antisym by blast
  qed
end

instantiation gexp_o :: "linorder" begin
fun less_gexp_o :: "gexp_o \<Rightarrow> gexp_o \<Rightarrow> bool"  where
  "less_gexp_o (Bc b1) (Bc b2) = (b1 < b2)" |
  "less_gexp_o (Bc b1) _ = True" |

  "less_gexp_o (Eq e1 e2) (Bc b2) = False" |
  "less_gexp_o (Eq e1 e2) (Eq e1' e2') = ((e1 < e1') \<or> ((e1 = e1') \<and> (e2 < e2')))" |
  "less_gexp_o (Eq e1 e2) _ = True" |

  "less_gexp_o (Gt e1 e2) (Bc b2) = False" |
  "less_gexp_o (Gt e1 e2) (Eq e1' e2') = False" |
  "less_gexp_o (Gt e1 e2) (Gt e1' e2') = ((e1 < e1') \<or> ((e1 = e1') \<and> (e2 < e2')))" |
  "less_gexp_o (Gt e1 e2) _ = True" |

  "less_gexp_o (In vb vc) (Nor v va) = True" |
  "less_gexp_o (In vb vc) (In v va) = (vb < v \<or> (vb = v \<and> vc < va))" |
  "less_gexp_o (In vb vc) _ = False" |

  "less_gexp_o (Nor g1 g2) (Nor g1' g2') = ((less_gexp_o g1 g1') \<or> ((g1 = g1') \<and> (less_gexp_o g2 g2')))" |
  "less_gexp_o (Nor g1 g2) _ = False"

definition less_eq_gexp_o :: "gexp_o \<Rightarrow> gexp_o \<Rightarrow> bool"
  where "less_eq_gexp_o e1 e2 \<equiv> (e1 < e2) \<or> (e1 = e2)"

lemma gexp_o_antisym: "(x::gexp_o) < y = (\<not>(y < x) \<and> (x \<noteq> y))"
    apply (induction x y rule: less_gexp_o.induct)
                        apply auto[1]
                        apply simp+
    using aexp_o_antisym apply blast
                        apply simp+
    using aexp_o_antisym apply blast
    by auto

lemma gexp_o_trans: "(x::gexp_o) < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
proof (induction x y arbitrary: z rule: less_gexp_o.induct)
case (1 b1 b2)
  then show ?case
    by (cases z, auto)
next
  case ("2_1" b1 v va)
  then show ?case
    by (cases z, auto)
next
  case ("2_2" b1 v va)
  then show ?case 
    by (cases z, auto)
next
  case ("2_3" b1 v va)
  then show ?case 
    by (cases z, auto)
next
  case ("2_4" b1 v va)
  then show ?case 
    by (cases z, auto)
next
  case (3 e1 e2 b2)
  then show ?case 
    by (cases z, auto)
next
  case (4 e1 e2 e1' e2')
  then show ?case 
    by (cases z, auto)
next
  case ("5_1" e1 e2 v va)
  then show ?case 
    by (cases z, auto)
next
  case ("5_2" e1 e2 v va)
  then show ?case 
    by (cases z, auto)
next
  case ("5_3" e1 e2 v va)
  then show ?case  
    by (cases z, auto)
next
  case (6 e1 e2 b2)
  then show ?case  
    by (cases z, auto)
next
  case (7 e1 e2 e1' e2')
  then show ?case  
    by (cases z, auto)
next
  case (8 e1 e2 e1' e2')
  then show ?case  
    by (cases z, auto)
next
  case ("9_1" e1 e2 v va)
  then show ?case  
    by (cases z, auto)
next
  case ("9_2" e1 e2 v va)
  then show ?case  
    by (cases z, auto)
next
  case (10 vb vc v va)
  then show ?case  
    by (cases z, auto)
next
  case (11 vb vc v va)
  then show ?case  
    by (cases z, auto)
next
  case ("12_1" vb vc v)
  then show ?case  
    by (cases z, auto)
next
  case ("12_2" vb vc v va)
  then show ?case  
    by (cases z, auto)
next
  case ("12_3" vb vc v va)
  then show ?case  
    by (cases z, auto)
next
  case (13 g1 g2 g1' g2')
  then show ?case
    by (cases z, auto)
next
  case ("14_1" g1 g2 v)
  then show ?case  
    by (cases z, auto)
next
  case ("14_2" g1 g2 v va)
  then show ?case
    by simp
next
  case ("14_3" g1 g2 v va)
  then show ?case
    by simp
next
  case ("14_4" g1 g2 v va)
  then show ?case
    by simp
qed

instance proof
  fix x y z :: gexp_o
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (metis gexp_o_antisym less_eq_gexp_o_def)
  show "(x \<le> x)"
    by (simp add: less_eq_gexp_o_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis less_eq_gexp_o_def gexp_o_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_gexp_o_def using gexp_o_antisym by blast
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_gexp_o_def using gexp_o_antisym by blast
qed
end

instantiation gexp :: linorder begin

context includes gexp.lifting begin
lift_definition less_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" is less.
lift_definition less_eq_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" is less_eq.
end

instance
  apply standard
  using less_eq_gexp.rep_eq less_gexp.rep_eq apply auto[1]
     apply (simp add: less_eq_gexp.rep_eq)
  using less_eq_gexp.rep_eq apply auto[1]
   apply (simp add: gexp_inject less_eq_gexp.rep_eq)
  using less_eq_gexp.rep_eq by auto
end

instantiation aexp :: linorder begin

context includes gexp.lifting begin
lift_definition less_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" is less.
lift_definition less_eq_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" is less_eq.
end

instance
  apply standard
  using less_aexp.rep_eq less_eq_aexp.rep_eq apply auto[1]
     apply (simp add: less_eq_aexp.rep_eq)
  using less_eq_aexp.rep_eq apply auto[1]
   apply (simp add: aexp_inject less_eq_aexp.rep_eq)
  using less_eq_aexp.rep_eq by auto
end

instantiation gexp :: equal begin
context includes gexp.lifting begin
lift_definition equal_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" is "\<lambda>g1 g2. g1 \<le> g2 \<and> g2 \<le> g1".
end

instance
  apply standard
  apply (simp add: equal_gexp_def)
  using gexp_inject by auto
end

instantiation aexp :: equal begin
context includes aexp.lifting begin
lift_definition equal_aexp :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" is "\<lambda>g1 g2. g1 \<le> g2 \<and> g2 \<le> g1".
end

instance
  apply standard
  apply (simp add: equal_aexp_def)
  using aexp_inject by auto
end

end
