subsection {* Guard Expressions *}
text{*
This theory defines the guard language of EFSMs which can be translated directly to and from
contexts. This is similar to boolean expressions from IMP \cite{fixme}. Boolean values true and
false respectively represent the guards which are always and never satisfied. Guards may test
for (in)equivalence of two arithmetic expressions or be connected using nor logic into compound
expressions. Additionally, a guard may also test to see if a particular variable is null. This is
useful if an EFSM transition is intended only to initialise a register.  We also define syntax hacks
for the relations less than, less than or equal to, greater than or equal to, and not equal to as
well as the expression of logical conjunction, disjunction, and negation in terms of nor logic.
*}

theory GExp
imports AExp Option_Logic "Show.Show_Instances"
begin
datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Nor gexp gexp | Null vname

instantiation gexp :: "show" begin
fun shows_prec_gexp :: "nat \<Rightarrow> gexp \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_prec_gexp n (Bc i) c = shows_prec n i c" |
  "shows_prec_gexp n (Eq v va) c = ''(''@(shows_prec n v '''')@''=''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Gt v va) c = ''Gt(''@(shows_prec n v '''')@''>''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Nor v va) c = ''Nor(''@(shows_prec n v '''')@'' ''@(shows_prec n va '''')@'')''@c" |
  "shows_prec_gexp n (Null v) c = ''NULL(''@(shows_prec n v '''')@'')''@c"

fun shows_list_gexp :: "gexp list \<Rightarrow> char list \<Rightarrow> char list" where
  "shows_list_gexp [] l = l" |
  "shows_list_gexp [u] l = shows_prec 0 u l" |
  "shows_list_gexp (h#t) l = (shows_prec 0 h '''')@'',''@(shows_list_gexp t l)"

lemma shows_prec_cases:  "shows_prec p (x::gexp) (r @ s) = shows_prec p x r @ s"
  proof (cases x)
    case (Bc x1)
    then show ?thesis by (simp add: shows_prec_append)
  next
    case (Eq x21 x22)
    then show ?thesis by (simp add: shows_prec_append)
  next
    case (Gt x31 x32)
    then show ?thesis by (simp add: shows_prec_append)
  next
    case (Nor x41 x42)
    then show ?thesis by simp
  next
    case (Null x5)
    then show ?thesis
      by simp
  qed

instance proof
  fix x::gexp
  fix p r s
  show "shows_prec p x (r @ s) = shows_prec p x r @ s"
    by (simp add: shows_prec_cases)
next
  fix xs::"gexp list"
  fix p r s
  show "shows_list xs (r @ s) = shows_list xs r @ s"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
    proof (induct xs)
      case Nil
      then show ?case
        by (simp add: shows_prec_cases)
    next
      case (Cons a xs)
      then show ?case
        by simp
    qed
  qed
qed
end

lemma show_g_not_empty: "show (g::gexp) \<noteq> ''''"
proof (cases g)
case (Bc x1)
  then show ?thesis
    apply (cases x1)
     apply (simp add: shows_string_def shows_prec_bool_def)
    by (simp add: shows_string_def shows_prec_bool_def)
next
  case (Eq x21 x22)
  then show ?thesis by simp
next
  case (Gt x31 x32)
  then show ?thesis by simp
next
  case (Nor x41 x42)
  then show ?thesis by simp
next
  case (Null x5)
  then show ?thesis by simp
qed

lemma deterministic_show_bool: "(show (a::gexp) = show (g::gexp)) \<Longrightarrow> (a = g)"
  oops

syntax (xsymbols)
  Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "=" 60*)
  Gt :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix ">" 60*)

fun gval :: "gexp \<Rightarrow> datastate \<Rightarrow> bool option" where
  "gval (Bc b) _ = Some b" |
  "gval (Gt a\<^sub>1 a\<^sub>2) s = ValueGt (aval a\<^sub>1 s) (aval a\<^sub>2 s)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) s = Some (aval a\<^sub>1 s = aval a\<^sub>2 s)" |
  "gval (Nor a\<^sub>1 a\<^sub>2) s = (case (gval a\<^sub>1 s, gval a\<^sub>2 s) of
    (Some x, Some y) \<Rightarrow> Some (\<not> (x \<or> y)) |
    _ \<Rightarrow> None
  )" |
  "gval (Null v) s = Some (s v = None)"

definition gNot :: "gexp \<Rightarrow> gexp"  where
  "gNot g \<equiv> Nor g g"

definition gOr :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" (*infix "\<or>" 60*) where
  "gOr v va \<equiv> Nor (Nor v va) (Nor v va)"

definition gAnd :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" (*infix "\<and>" 60*) where
  "gAnd v va \<equiv> Nor (Nor v v) (Nor va va)"

lemma inj_gAnd: "inj gAnd"
  apply (simp add: inj_def)
  apply clarify
  by (metis gAnd_def gexp.inject(4))

lemma gAnd_determinism: "(gAnd x y = gAnd x' y') = (x = x' \<and> y = y')"
proof
  show "gAnd x y = gAnd x' y' \<Longrightarrow> x = x' \<and> y = y'"
    by (simp add: gAnd_def)
next
  show "x = x' \<and> y = y' \<Longrightarrow> gAnd x y = gAnd x' y' "
    by simp
qed

definition Lt :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "<" 60*) where
  "Lt a b \<equiv> Gt b a"

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<le>" 60*) where
  "Le v va \<equiv> gNot (Gt v va)"

definition Ge :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<ge>" 60*) where
  "Ge v va \<equiv> gNot (Lt v va)"

definition Ne :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<noteq>" 60*) where
  "Ne v va \<equiv> gNot (Eq v va)"

lemma or_equiv: "gval (gOr x y) r = maybe_or (gval x r) (gval y r)"
  apply (simp add: gOr_def)
  apply (cases "gval x r")
   apply (cases "gval y r")
    apply simp
   apply simp
  apply (cases "gval y r")
   apply simp
  by simp

lemma not_equiv: "maybe_not (gval x s) = gval (gNot x) s"
  apply (simp add: gNot_def)
  apply (cases "gval x s")
   apply simp
  by simp

lemma nor_equiv: "gval (gNot (gOr a b)) s = gval (Nor a b) s"
  by (simp add: option.case_eq_if gOr_def gNot_def)

definition satisfiable :: "gexp \<Rightarrow> bool" where
  "satisfiable g \<equiv> (\<exists>s. gval g s = Some True)"

lemma not_satisfiable_gt_string: "\<not> satisfiable (Gt v (L (Str s)))"
  by (simp add: satisfiable_def)

definition gexp_valid :: "gexp \<Rightarrow> bool" where
  "gexp_valid g \<equiv> (\<forall>s. gval g s = Some True)"

definition gexp_equiv :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "gexp_equiv a b \<equiv> \<forall>s. gval a s = gval b s"

lemma gexp_equiv_reflexive: "gexp_equiv x x"
  by (simp add: gexp_equiv_def)

lemma gexp_equiv_symmetric: "gexp_equiv x y \<Longrightarrow> gexp_equiv y x"
  by (simp add: gexp_equiv_def)

lemma gexp_equiv_transitive: "gexp_equiv x y \<and> gexp_equiv y z \<Longrightarrow> gexp_equiv x z"
  by (simp add: gexp_equiv_def)

lemma gval_subst: "gexp_equiv x y \<Longrightarrow> P (gval x s) \<Longrightarrow> P (gval y s)"
  by (simp add: gexp_equiv_def)

lemma gexp_equiv_satisfiable: "gexp_equiv x y \<Longrightarrow> satisfiable x = satisfiable y"
  by (simp add: gexp_equiv_def satisfiable_def)

lemma gAnd_reflexivity: "gexp_equiv (gAnd x x) x"
  apply (simp add: gexp_equiv_def gAnd_def)
  apply (rule allI)
  apply (case_tac "gval x s")
   apply simp
  by simp

lemma gAnd_zero: "gexp_equiv (gAnd (Bc True) x) x"
  apply (simp add: gexp_equiv_def gAnd_def)
  apply (rule allI)
  apply (case_tac "gval x s")
  by simp_all

lemma gAnd_symmetry: "gexp_equiv (gAnd x y) (gAnd y x)"
  apply (simp add: gexp_equiv_def gAnd_def)
  apply (rule allI)
  apply (case_tac "gval y s")
   apply (case_tac "gval x s")
    apply simp
   apply simp
  apply (case_tac "gval x s")
   apply simp
  by auto

lemma satisfiable_gAnd_self: "satisfiable (gAnd x x) = satisfiable x"
  by (simp add: gAnd_reflexivity gexp_equiv_satisfiable)

definition mutually_exclusive :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "mutually_exclusive x y = (\<forall>i. (gval x i = Some True \<longrightarrow> gval y i \<noteq> Some True) \<and>
                                 (gval y i = Some True \<longrightarrow> gval x i \<noteq> Some True))"

lemma mutually_exclusive_unsatisfiable_conj: "mutually_exclusive x y = (\<not> satisfiable (gAnd x y))"
  apply (simp add: mutually_exclusive_def satisfiable_def gAnd_def)
  apply safe
    apply (case_tac "gval x s")
     apply simp
    apply (case_tac "gval y s")
     apply simp
    apply simp
   apply (metis (mono_tags, lifting) option.simps(5))
  by (metis (mono_tags, lifting) option.simps(5))

lemma unsatisfiable_conj_mutually_exclusive: "\<not> satisfiable (gAnd x y) = mutually_exclusive x y"
  by (simp add: mutually_exclusive_unsatisfiable_conj)

lemma mutually_exclusive_reflexive: "satisfiable x \<Longrightarrow> \<not> mutually_exclusive x x"
  by (simp add: mutually_exclusive_def satisfiable_def)

lemma mutually_exclusive_symmetric: "mutually_exclusive x y \<Longrightarrow> mutually_exclusive y x"
  by (simp add: mutually_exclusive_def)

lemma not_mutually_exclusive_true: "satisfiable x = (\<not> mutually_exclusive x (Bc True))"
  by (simp add: mutually_exclusive_def satisfiable_def)

lemma show_gexp_determinism: "show (g1::gexp) = show (g2::gexp) \<Longrightarrow> g1 = g2"
  sorry

definition conjoin :: "gexp list \<Rightarrow> gexp" where
  "conjoin x = foldl (\<lambda>h. gAnd h) (Bc True) x"

lemma "foldr gAnd x (Bc True) = foldr gAnd y (Bc True) \<Longrightarrow> x = y"
proof (induct x)
  case Nil
  then show ?case
  proof (induct y)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a y)
    then show ?case
      by (simp add: gAnd_def)
  qed
next
  case (Cons x xs)
  then show ?case
  proof (induct y)
    case Nil
    then show ?case
      by (simp add: gAnd_def)
  next
    case (Cons y ys)
    then show ?case
      apply simp
      apply safe
       apply (simp add: gAnd_determinism)
      apply (simp add: gAnd_def)
      sorry
  qed
qed

lemma contra: "x \<noteq> y \<Longrightarrow> foldl gAnd (Bc True) x \<noteq> foldl gAnd (Bc True) y"
proof (induct x)
  case Nil
  then show ?case
    apply simp
    by (metis append_butlast_last_id foldl_Cons foldl_Nil foldl_append gAnd_def gexp.distinct(5))
next
  case (Cons a x)
  then show ?case
  proof (induct y)
    case Nil
    then show ?case
    by (metis append_butlast_last_id foldl_Cons foldl_Nil foldl_append gAnd_def gexp.distinct(5))
  next
    case (Cons y ys)
    then show ?case
      apply safe
      sorry
  qed

qed

lemma expanded: "foldl gAnd (Bc True) x = foldl gAnd (Bc True) y \<Longrightarrow> x = y"
  using contra by auto

lemma inj_conjoin: "inj conjoin"
  apply (simp add: inj_def)
  apply (simp add: conjoin_def)
  apply clarify
  apply (case_tac x)
   apply simp
  sorry

lemma conjoin_determinism: "(conjoin x = conjoin y) = (x = y)"
proof
  show "conjoin x = conjoin y \<Longrightarrow> x = y"
    by (simp add: inj_conjoin inj_eq)
next
  show "x = y \<Longrightarrow> conjoin x = conjoin y"
    by simp
qed

end
