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
imports AExp Option_Logic Utils "not4afp/Show_Bool"
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

lemma string_implode_gexp_deterministic: "String.implode (show (x::gexp)) = String.implode (show (y::gexp)) \<Longrightarrow> show x = show y"
proof (induct x)
case (Bc x)
  then show ?case sorry
next
  case (Eq x1a x2)
  then show ?case sorry
next
  case (Gt x1a x2)
  then show ?case sorry
next
  case (Nor x1 x2)
  then show ?case sorry
next
  case (Null x)
  then show ?case sorry
qed

lemma show_g_not_empty: "show (g::gexp) \<noteq> ''''"
proof (cases g)
case (Bc x1)
  then show ?thesis
    apply (cases x1)
     apply (simp add: shows_string_def)
    by (simp add: shows_string_def)
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

instantiation gexp :: ord begin
definition  less_eq_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "less_eq_gexp g1 g2 \<equiv> \<forall>s. maybe_implies (gval g1 s) (gval g2 s) = Some True"

definition  less_gexp :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "less_gexp g1 g2 \<equiv> \<forall>s. maybe_implies (gval g1 s) (gval g2 s) = Some True \<and> (gval g1 s) \<noteq> (gval g2 s)"

instance proof
qed
end

abbreviation gNot :: "gexp \<Rightarrow> gexp"  where
  "gNot g \<equiv> Nor g g"

abbreviation gOr :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" (*infix "\<or>" 60*) where
  "gOr v va \<equiv> Nor (Nor v va) (Nor v va)"

abbreviation gAnd :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" (*infix "\<and>" 60*) where
  "gAnd v va \<equiv> Nor (Nor v v) (Nor va va)"

abbreviation Lt :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "<" 60*) where
  "Lt a b \<equiv> Gt b a"

abbreviation Le :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<le>" 60*) where
  "Le v va \<equiv> gNot (Gt v va)"

abbreviation Ge :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<ge>" 60*) where
  "Ge v va \<equiv> gNot (Lt v va)"

abbreviation Ne :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<noteq>" 60*) where
  "Ne v va \<equiv> gNot (Eq v va)"

lemma or_equiv: "gval (gOr x y) r = maybe_or (gval x r) (gval y r)"
  apply simp
  apply (cases "gval x r")
   apply (cases "gval y r")
    apply simp
   apply simp
  apply (cases "gval y r")
   apply simp
  by simp

lemma not_equiv: "maybe_not (gval x s) = gval (gNot x) s"
  apply simp
  apply (cases "gval x s")
   apply simp
  by simp

lemma nor_equiv: "gval (gNot (gOr a b)) s = gval (Nor a b) s"
  by (simp add: option.case_eq_if)

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
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval x s")
   apply simp
  by simp

lemma gAnd_zero: "gexp_equiv (gAnd (Bc True) x) x"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval x s")
  by simp_all

lemma gAnd_symmetry: "gexp_equiv (gAnd x y) (gAnd y x)"
  apply (simp add: gexp_equiv_def)
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
  apply (simp add: mutually_exclusive_def satisfiable_def)
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

end
