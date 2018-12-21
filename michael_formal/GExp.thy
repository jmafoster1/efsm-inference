subsection \<open>Guard Expressions\<close>
text\<open>
This theory defines the guard language of EFSMs which can be translated directly to and from
contexts. This is similar to boolean expressions from IMP \cite{fixme}. Boolean values true and
false respectively represent the guards which are always and never satisfied. Guards may test
for (in)equivalence of two arithmetic expressions or be connected using nor logic into compound
expressions. Additionally, a guard may also test to see if a particular variable is null. This is
useful if an EFSM transition is intended only to initialise a register.  We also define syntax hacks
for the relations less than, less than or equal to, greater than or equal to, and not equal to as
well as the expression of logical conjunction, disjunction, and negation in terms of nor logic.
\<close>

theory GExp
imports "efsm-exp.AExp" "efsm-exp.Option_Logic"
begin

datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Nor gexp gexp | Null vname

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

abbreviation gNot :: "gexp \<Rightarrow> gexp"  where
  "gNot g \<equiv> Nor g g"

abbreviation gOr :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" (*infix "\<or>" 60*) where
  "gOr v va \<equiv> Nor (Nor v va) (Nor v va)"

abbreviation gAnd :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" (*infix "\<and>" 60*) where
  "gAnd v va \<equiv> Nor (Nor v v) (Nor va va)"

lemma inj_gAnd: "inj gAnd"
  apply (simp add: inj_def)
  apply clarify
  by (metis  gexp.inject(4))

lemma gAnd_determinism: "(gAnd x y = gAnd x' y') = (x = x' \<and> y = y')"
proof
  show "gAnd x y = gAnd x' y' \<Longrightarrow> x = x' \<and> y = y'"
    by (simp)
next
  show "x = x' \<and> y = y' \<Longrightarrow> gAnd x y = gAnd x' y' "
    by simp
qed

abbreviation Lt :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "<" 60*) where
  "Lt a b \<equiv> Gt b a"

abbreviation Le :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<le>" 60*) where
  "Le v va \<equiv> gNot (Gt v va)"

abbreviation Ge :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<ge>" 60*) where
  "Ge v va \<equiv> gNot (Lt v va)"

abbreviation Ne :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "\<noteq>" 60*) where
  "Ne v va \<equiv> gNot (Eq v va)"

lemma or_equiv: "gval (gOr x y) r = maybe_or (gval x r) (gval y r)"
  apply (simp)
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

fun gnot :: "gexp \<Rightarrow> gexp"  where
  "gnot (Bc b) = Bc (\<not>b)" |
  "gnot (Gt a b) = Le a b" |
  "gnot a = gNot a"

lemma gnot_is_gNot: "gexp_equiv (gnot a) (gNot a)"
  unfolding gexp_equiv_def
  apply (induct_tac a)
  by auto

fun gor :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" where
  "gor (Bc False) b = b" |
  "gor b (Bc False) = b" |
  "gor a b = (if a = b then a else gOr a b)"

lemma gval_gOr_false: "gval x s = gval (gOr (Bc False) x) s"
proof (induct x)
case (Bc x)
  then show ?case by simp
next
  case (Eq x1a x2)
  then show ?case by simp
next
  case (Gt x1a x2)
  then show ?case
    apply simp
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s)")
     apply simp
    by simp
next
  case (Nor x1 x2)
  have "gval (Nor x1 x2) s = gval (gOr (Bc False) (Nor x1 x2)) s"
    apply simp
    apply (case_tac "gval x1 s")
     apply simp
    apply (case_tac "gval x2 s")
     apply simp
    by simp
  then show ?case by simp
next
  case (Null x)
  then show ?case by simp
qed

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

lemma gOr_reflexivity: "gexp_equiv (gOr x x) x"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval x s")
   apply simp
  by simp

lemma gOr_zero: "gexp_equiv (gOr (Bc False) x) x"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval x s")
  by simp_all

lemma gOr_symmetry: "gexp_equiv (gOr x y) (gOr y x)"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval y s")
   apply (case_tac "gval x s")
    apply simp
   apply simp
  apply (case_tac "gval x s")
   apply simp
  by auto

lemma gor_is_gOr: "gexp_equiv (gor a b) (gOr a b)"
  unfolding gexp_equiv_def
  apply (rule allI)
  apply (case_tac a)
      apply (case_tac b)
          apply (case_tac x1)
           apply (case_tac x1a)
            apply simp
           apply simp
          apply simp
         apply (case_tac x1)
          apply simp
         apply simp
        apply (case_tac x1)
         apply simp
        apply simp
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval x31 s) (aval x32 s)")
         apply simp
        apply simp
       apply (case_tac x1)
        apply simp
  using gor.simps(1) gval_gOr_false apply presburger
      apply (case_tac x1)
       apply simp
      apply simp
     apply clarify
     apply (case_tac b)
         apply (case_tac x1)
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
     apply simp
    apply clarify
    apply (case_tac b)
        apply (case_tac x1)
         apply simp
        apply (metis (full_types) gOr_symmetry gexp_equiv_def gor.simps(4) gval_gOr_false)
       apply simp
      apply (metis gor.simps(19) gval_gOr_false nor_equiv not_equiv)
     apply simp
    apply simp
   apply clarify
   apply (case_tac b)
       apply (case_tac x1)
        apply simp
       apply (metis (full_types) gOr_symmetry gexp_equiv_def gor.simps(5) gval_gOr_false)
      apply simp
     apply simp
  using nor_equiv apply auto[1]
   apply simp
  apply clarify
  apply (case_tac b)
      apply (case_tac x1)
  by auto

fun gand :: "gexp \<Rightarrow> gexp \<Rightarrow> gexp" where
  "gand b (Bc True) = b" |
  "gand (Bc True) b = b" |
  "gand a b = (if a = b then a else gAnd a b)"

lemma gand_bc_true[simp]: "gand (gexp.Bc True) a = a"
  apply (case_tac a)
      apply (metis gand.simps(1) gand.simps(2))
  by auto

lemma gand_is_gAnd: "gexp_equiv (gand x y) (gAnd x y)"
proof (cases x)
case (Bc x1)
  then show ?thesis
    unfolding gexp_equiv_def
    apply clarify
    apply (cases x1)
     apply (cases y)
         prefer 6
         apply (cases y)
             apply (metis (full_types) gAnd_symmetry gAnd_zero gand.simps(1) gand.simps(7) gexp_equiv_def gexp_equiv_symmetric gval_gOr_false)
            apply simp
           apply simp
          apply simp
         apply simp
        apply (metis (mono_tags, hide_lams) Bc gAnd_zero gand.simps(1) gand.simps(2) gexp.inject(1) gexp_equiv_def gval.simps(1))
       apply simp
      apply (metis (full_types) gAnd_zero gand.simps(4) gexp_equiv_def)
     apply (metis (full_types) gAnd_zero gand.simps(5) gexp_equiv_def)
    by simp
next
case (Eq x21 x22)
  then show ?thesis
    apply clarify
    apply (cases y)
        apply (case_tac x1)
         apply (metis (mono_tags, lifting) gAnd_symmetry gAnd_zero gand.simps(1) gexp_equiv_symmetric gexp_equiv_transitive)
        apply (simp add: gexp_equiv_reflexive)
       apply (simp add: gAnd_reflexivity gexp_equiv_reflexive gexp_equiv_symmetric)
      apply (simp add: gexp_equiv_reflexive)
     apply (simp add: gexp_equiv_reflexive)
    by (simp add: gexp_equiv_reflexive)
next
  case (Gt x31 x32)
  then show ?thesis
    apply clarify
    apply (cases y)
        apply (case_tac x1)
         apply (metis (mono_tags, lifting) gAnd_symmetry gAnd_zero gand.simps(1) gexp_equiv_symmetric gexp_equiv_transitive)
        apply (simp add: gexp_equiv_reflexive)
       apply (simp add: gexp_equiv_reflexive)
      apply (simp add: gAnd_reflexivity gexp_equiv_reflexive gexp_equiv_symmetric)
     apply (simp add: gexp_equiv_reflexive)
    by (simp add: gexp_equiv_reflexive)
next
  case (Nor x41 x42)
  then show ?thesis
    apply clarify
    apply (cases y)
        apply (case_tac x1)
         apply (metis (mono_tags, lifting) gAnd_symmetry gAnd_zero gand.simps(1) gexp_equiv_symmetric gexp_equiv_transitive)
        apply (simp add: gexp_equiv_reflexive)
       apply (simp add: gexp_equiv_reflexive)
      apply (simp add: gexp_equiv_reflexive)
     apply (simp add: gAnd_reflexivity gAnd_symmetry gexp_equiv_reflexive gexp_equiv_symmetric)
    by (simp add: gexp_equiv_reflexive)
next
  case (Null x5)
  then show ?thesis
    apply clarify
    apply (cases y)
        apply (case_tac x1)
         apply (metis (mono_tags, lifting) gAnd_symmetry gAnd_zero gand.simps(1) gexp_equiv_symmetric gexp_equiv_transitive)
        apply (simp add: gexp_equiv_reflexive)
       apply (simp add: gexp_equiv_reflexive)
      apply (simp add: gexp_equiv_reflexive)
     apply (simp add: gAnd_reflexivity gAnd_symmetry gexp_equiv_reflexive gexp_equiv_symmetric)
    by (simp add: gAnd_reflexivity gexp_equiv_reflexive gexp_equiv_symmetric)
qed

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
