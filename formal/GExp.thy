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
imports AExp Option_Logic
begin

(* type_synonym gexp = "(aexp \<times> cexp)" *)

(* abbreviation Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" where *)
  (* "Eq a b = (a, cexp.Eq b) *)

datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Nor gexp gexp | Null aexp

syntax (xsymbols)
  Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix "=" 60*)
  Gt :: "aexp \<Rightarrow> aexp \<Rightarrow> gexp" (*infix ">" 60*)

fun gval :: "gexp \<Rightarrow> datastate \<Rightarrow> trilean" where
  "gval (Bc True) _ = true" |
  "gval (Bc False) _ = false" |
  "gval (Gt a\<^sub>1 a\<^sub>2) s = ValueGt (aval a\<^sub>1 s) (aval a\<^sub>2 s)" |
  "gval (Eq a\<^sub>1 a\<^sub>2) s = ValueEq (aval a\<^sub>1 s) (aval a\<^sub>2 s)" |
  "gval (Nor a\<^sub>1 a\<^sub>2) s = \<not>\<^sub>? ((gval a\<^sub>1 s) \<or>\<^sub>? (gval a\<^sub>2 s))" |
  "gval (Null v) s = ValueEq (aval v s) None"

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

lemma or_equiv: "gval (gOr x y) r = (gval x r) \<or>\<^sub>? (gval y r)"
  by (simp add: maybe_double_negation maybe_or_idempotent)

lemma not_equiv: "gval (gNot x) s = \<not>\<^sub>? (gval x s)"
  by (simp add: maybe_or_idempotent)

lemma nor_equiv: "gval (gNot (gOr a b)) s = gval (Nor a b) s"
  by (metis maybe_double_negation not_equiv)

definition satisfiable :: "gexp \<Rightarrow> bool" where
  "satisfiable g \<equiv> (\<exists>s. gval g s = true)"

definition gexp_valid :: "gexp \<Rightarrow> bool" where
  "gexp_valid g \<equiv> (\<forall>s. gval g s = true)"

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
  by (simp add: gexp_equiv_def maybe_double_negation maybe_or_idempotent)

lemma gAnd_zero: "gexp_equiv (gAnd (Bc True) x) x"
  apply (simp add: gexp_equiv_def)
  apply (rule allI)
  apply (case_tac "gval x s")
  by simp_all

lemma gAnd_symmetry: "gexp_equiv (gAnd x y) (gAnd y x)"
  by (simp add: gexp_equiv_def maybe_or_commutative)

lemma satisfiable_gAnd_self: "satisfiable (gAnd x x) = satisfiable x"
  by (simp add: gAnd_reflexivity gexp_equiv_satisfiable)

definition mutually_exclusive :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "mutually_exclusive x y = (\<forall>i. (gval x i = true \<longrightarrow> gval y i \<noteq> true) \<and>
                                 (gval y i = true \<longrightarrow> gval x i \<noteq> true))"

lemma mutually_exclusive_unsatisfiable_conj: "mutually_exclusive x y = (\<not> satisfiable (gAnd x y))"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  by (metis maybe_double_negation maybe_not.simps(2) maybe_or_associative maybe_or_commutative maybe_or_idempotent maybe_or_zero)

lemma unsatisfiable_conj_mutually_exclusive: "\<not> satisfiable (gAnd x y) = mutually_exclusive x y"
  by (simp add: mutually_exclusive_unsatisfiable_conj)

lemma mutually_exclusive_reflexive: "satisfiable x \<Longrightarrow> \<not> mutually_exclusive x x"
  by (simp add: mutually_exclusive_def satisfiable_def)

lemma mutually_exclusive_symmetric: "mutually_exclusive x y \<Longrightarrow> mutually_exclusive y x"
  by (simp add: mutually_exclusive_def)

lemma not_mutually_exclusive_true: "satisfiable x = (\<not> mutually_exclusive x (Bc True))"
  by (simp add: mutually_exclusive_def satisfiable_def)

lemma gval_gAnd: "gval (gAnd g1 g2) s = (gval g1 s) \<and>\<^sub>? (gval g2 s)"
proof(induct "gval g1 s" "gval g2 s" rule: maybe_and.induct)
case 1
  then show ?case
    by (metis gval.simps(5) maybe_and_valid maybe_not.simps(3) maybe_or_valid)
next
  case "2_1"
  then show ?case
    by simp
next
  case "2_2"
  then show ?case
    by simp
next
  case 3
  then show ?case
    by simp
next
  case "4_1"
  then show ?case
    by simp
next
  case "4_2"
  then show ?case
    by simp
next
  case 5
  then show ?case
    by simp
qed

lemma gval_gAnd_True: "(gval (gAnd g1 g2) s = true) = ((gval g1 s = true) \<and> gval g2 s = true)"
  using gval_gAnd maybe_and_not_true by fastforce

declare gval.simps [simp del]

fun gexp_constrains :: "gexp \<Rightarrow> aexp \<Rightarrow> bool" where
  "gexp_constrains (gexp.Bc _) _ = False" |
  "gexp_constrains (Null a) v = aexp_constrains a v" |
  "gexp_constrains (gexp.Eq a1 a2) v = (aexp_constrains a1 v \<or> aexp_constrains a2 v)" |
  "gexp_constrains (gexp.Gt a1 a2) v = (aexp_constrains a1 v \<or> aexp_constrains a2 v)" |
  "gexp_constrains (gexp.Nor g1 g2) v = (gexp_constrains g1 v \<or> gexp_constrains g2 v)"

fun contains_bool :: "gexp \<Rightarrow> bool" where
  "contains_bool (Bc _) = True" |
  "contains_bool (Nor g1 g2) = (contains_bool g1 \<or> contains_bool g2)" |
  "contains_bool _ = False"

fun gexp_same_structure :: "gexp \<Rightarrow> gexp \<Rightarrow> bool" where
  "gexp_same_structure (gexp.Bc b) (gexp.Bc b') = (b = b')" |
  "gexp_same_structure (gexp.Eq a1 a2) (gexp.Eq a1' a2') = (aexp_same_structure a1 a1' \<and> aexp_same_structure a2 a2')" |
  "gexp_same_structure (gexp.Gt a1 a2) (gexp.Gt a1' a2') = (aexp_same_structure a1 a1' \<and> aexp_same_structure a2 a2')" |
  "gexp_same_structure (gexp.Nor g1 g2) (gexp.Nor g1' g2') = (gexp_same_structure g1 g1' \<and> gexp_same_structure g2 g2')" |
  "gexp_same_structure (gexp.Null a1) (gexp.Null a2) = aexp_same_structure a1 a2" |
  "gexp_same_structure _ _ = False"

end
