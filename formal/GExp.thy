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
imports AExp Trilean
begin

definition I :: "nat \<Rightarrow> vname" where
  "I n = vname.I (n-1)"
declare I_def [simp]
hide_const I

text_raw\<open>\snip{gexptype}{1}{2}{%\<close>
datatype gexp = Bc bool | Eq aexp aexp | Gt aexp aexp | Nor gexp gexp | Null aexp
text_raw\<open>}%endsnip\<close>

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

fun In :: "vname \<Rightarrow> value list \<Rightarrow> gexp" where
  "In a [] = Bc False" |
  "In a [v] = Eq (V a) (L v)" |
  "In a (v1#t) = gOr (Eq (V a) (L v1)) (In a t)"

lemma gval_gOr: "gval (gOr x y) r = (gval x r) \<or>\<^sub>? (gval y r)"
  by (simp add: maybe_double_negation maybe_or_idempotent)

lemma not_equiv: "gval (gNot x) s = \<not>\<^sub>? (gval x s)"
  by (simp add: maybe_or_idempotent)

lemma nor_equiv: "gval (gNot (gOr a b)) s = gval (Nor a b) s"
  by (metis maybe_double_negation not_equiv)

definition satisfiable :: "gexp \<Rightarrow> bool" where
  "satisfiable g \<equiv> (\<exists>i r. gval g (join_ir i r) = true)"

definition "satisfiable_list l = satisfiable (fold gAnd l (Bc True))"

lemma satisfiable_true: "satisfiable (Bc True)"
  by (simp add: satisfiable_def)

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
  by (simp add: add.commute gexp_equiv_def)

lemma satisfiable_gAnd_self: "satisfiable (gAnd x x) = satisfiable x"
  by (simp add: gAnd_reflexivity gexp_equiv_satisfiable)

lemma gval_gAnd: "gval (gAnd g1 g2) s = (gval g1 s) \<and>\<^sub>? (gval g2 s)"
proof(induct "gval g1 s" "gval g2 s" rule: times_trilean.induct)
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

lemma gval_foldr_true: "(gval (foldr gAnd G (Bc True)) s = true) = (\<forall>g \<in> set G. gval g s = true)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: gval.simps)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_gAnd maybe_and_true)
    by simp
qed

fun enumerate_gexp_inputs :: "gexp \<Rightarrow> nat set" where
  "enumerate_gexp_inputs (GExp.Bc _) = {}" |
  "enumerate_gexp_inputs (GExp.Null v) = enumerate_aexp_inputs v" |
  "enumerate_gexp_inputs (GExp.Eq v va) = enumerate_aexp_inputs v \<union> enumerate_aexp_inputs va" |
  "enumerate_gexp_inputs (GExp.Lt v va) = enumerate_aexp_inputs v \<union> enumerate_aexp_inputs va" |
  "enumerate_gexp_inputs (GExp.Nor v va) = enumerate_gexp_inputs v \<union> enumerate_gexp_inputs va"

fun enumerate_gexp_inputs_list :: "gexp \<Rightarrow> nat list" where
  "enumerate_gexp_inputs_list (GExp.Bc _) = []" |
  "enumerate_gexp_inputs_list (GExp.Null v) = enumerate_aexp_inputs_list v" |
  "enumerate_gexp_inputs_list (GExp.Eq v va) = enumerate_aexp_inputs_list v @ enumerate_aexp_inputs_list va" |
  "enumerate_gexp_inputs_list (GExp.Lt v va) = enumerate_aexp_inputs_list v @ enumerate_aexp_inputs_list va" |
  "enumerate_gexp_inputs_list (GExp.Nor v va) = enumerate_gexp_inputs_list v @ enumerate_gexp_inputs_list va"

lemma enumerate_gexp_inputs_list: "enumerate_gexp_inputs l = set (enumerate_gexp_inputs_list l)"
proof(induct l)
case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case 
    by (simp add: enumerate_aexp_inputs_list)
next
  case (Gt x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_inputs_list)
next
  case (Nor l1 l2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (simp add: enumerate_aexp_inputs_list)
qed

lemma set_enumerate_gexp_inputs_list: 
"set (fold (@) (map enumerate_gexp_inputs_list l) []) = (\<Union> (set (map enumerate_gexp_inputs l)))"
proof(induct l)
case Nil
  then show ?case
    by simp
next
case (Cons a l)
  then show ?case
    using enumerate_gexp_inputs_list
    by (simp add: fold_append_concat_rev inf_sup_aci(5))
qed

definition max_input :: "gexp \<Rightarrow> nat option" where
  "max_input g = (let inputs = (enumerate_gexp_inputs g) in if inputs = {} then None else Some (Max inputs))"

fun enumerate_gexp_regs :: "gexp \<Rightarrow> nat set" where
  "enumerate_gexp_regs (GExp.Bc _) = {}" |
  "enumerate_gexp_regs (GExp.Null v) = enumerate_aexp_regs v" |
  "enumerate_gexp_regs (GExp.Eq v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_gexp_regs (GExp.Lt v va) = enumerate_aexp_regs v \<union> enumerate_aexp_regs va" |
  "enumerate_gexp_regs (GExp.Nor v va) = enumerate_gexp_regs v \<union> enumerate_gexp_regs va"

fun enumerate_gexp_regs_list :: "gexp \<Rightarrow> nat list" where
  "enumerate_gexp_regs_list (GExp.Bc _) = []" |
  "enumerate_gexp_regs_list (GExp.Null v) = enumerate_aexp_regs_list v" |
  "enumerate_gexp_regs_list (GExp.Eq v va) = enumerate_aexp_regs_list v @ enumerate_aexp_regs_list va" |
  "enumerate_gexp_regs_list (GExp.Lt v va) = enumerate_aexp_regs_list v @ enumerate_aexp_regs_list va" |
  "enumerate_gexp_regs_list (GExp.Nor v va) = enumerate_gexp_regs_list v @ enumerate_gexp_regs_list va"

lemma enumerate_gexp_regs_list: "set (enumerate_gexp_regs_list l) = enumerate_gexp_regs l"
proof(induct l)
case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_regs_list)
next
  case (Gt x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_regs_list)
next
  case (Nor l1 l2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (simp add: enumerate_aexp_regs_list)
qed

definition max_reg :: "gexp \<Rightarrow> nat option" where
  "max_reg g = (let regs = (enumerate_gexp_regs g) in if regs = {} then None else Some (Max regs))"

lemma enumerate_gexp_regs_empty_reg_unconstrained: "enumerate_gexp_regs g = {} \<Longrightarrow> \<forall>r. \<not> gexp_constrains g (V (R r))"
proof(induct g)
case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_regs_empty_reg_unconstrained)
next
  case (Gt x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_regs_empty_reg_unconstrained)
next
  case (Nor g1 g2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (simp add: enumerate_aexp_regs_empty_reg_unconstrained)
qed

lemma enumerate_gexp_inputs_empty_input_unconstrained: "enumerate_gexp_inputs g = {} \<Longrightarrow> \<forall>r. \<not> gexp_constrains g (V (vname.I r))"
proof(induct g)
case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_inputs_empty_input_unconstrained)
next
  case (Gt x1a x2)
  then show ?case
    by (simp add: enumerate_aexp_inputs_empty_input_unconstrained)
next
  case (Nor g1 g2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (simp add: enumerate_aexp_inputs_empty_input_unconstrained)
qed

lemma input_unconstrained_gval_input_swap: "\<forall>r. \<not> gexp_constrains a (V (vname.I r)) \<Longrightarrow> (gval a (join_ir i r) = gval a (join_ir i' r))"
proof(induct a)
  case (Bc x)
  then show ?case
    apply (cases x)
     apply (simp add: gval.simps(1))
    by (simp add: gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    apply (simp add: gval.simps ValueEq_def)
    by (metis input_unconstrained_aval_input_swap)
next
  case (Gt x1a x2)
  then show ?case
    apply (simp add: gval.simps ValueGt_def)
    by (metis input_unconstrained_aval_input_swap)
next
  case (Nor a1 a2)
  then show ?case
    by (simp add: gval.simps(5))
next
  case (Null x)
  then show ?case
    by (metis gexp_constrains.simps(2) gval.simps(6) input_unconstrained_aval_input_swap)
qed

lemma register_unconstrained_gval_register_swap: "\<forall>r. \<not> gexp_constrains a (V (R r)) \<Longrightarrow> (gval a (join_ir i r) = gval a (join_ir i r'))"
proof(induct a)
  case (Bc x)
  then show ?case
    apply (cases x)
     apply (simp add: gval.simps(1))
    by (simp add: gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    apply (simp add: gval.simps ValueEq_def)
    by (metis input_unconstrained_aval_register_swap)
next
  case (Gt x1a x2)
  then show ?case
    apply (simp add: gval.simps ValueGt_def)
    by (metis input_unconstrained_aval_register_swap)
next
  case (Nor a1 a2)
  then show ?case
    by (simp add: gval.simps(5))
next
  case (Null x)
  then show ?case
    by (metis gexp.distinct(13) gexp.distinct(17) gexp.distinct(19) gexp.distinct(7) gexp.inject(5) gexp_constrains.simps(2) gval.elims input_unconstrained_aval_register_swap)
qed

lemma unconstrained_variable_swap_gval:
   "\<forall>r. \<not> gexp_constrains g (V (vname.I r)) \<Longrightarrow>
    \<forall>r. \<not> gexp_constrains g (V (R r)) \<Longrightarrow>
    gval g s = gval g s'"
proof(induct g)
case (Bc x)
  then show ?case
    apply (cases x)
     apply (simp add: gval.simps(1))
    by (simp add: gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis gexp_constrains.simps(3) gval.simps(4) unconstrained_variable_swap_aval)
next
  case (Gt x1a x2)
  then show ?case
    by (metis gexp_constrains.simps(4) gval.simps(3) unconstrained_variable_swap_aval)
next
  case (Nor g1 g2)
  then show ?case
    by (simp add: gval.simps(5))
next
  case (Null x)
  then show ?case
    by (metis gexp_constrains.simps(2) gval.simps(6) unconstrained_variable_swap_aval)
qed

lemma "gval (foldr gAnd G (Bc True)) s = foldr (\<and>\<^sub>?) (map (\<lambda>g. gval g s) G) true"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: gval.simps)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_gAnd)
    by simp
qed

lemma possible_to_be_in: "s \<noteq> [] \<Longrightarrow> satisfiable (In v s)"
proof(induct s)
case Nil
  then show ?case by simp
next
  case (Cons a s)
  then show ?case
    apply (case_tac s)
     apply (simp add: satisfiable_def gval.simps ValueEq_def)
     apply (case_tac v)
      apply (simp add: join_ir_def input2state_exists)
     apply (simp add: join_ir_def)
    using input2state_exists apply blast
    apply (simp add: satisfiable_def gval_gOr)
    by (metis ValueEq_def gval.simps(4) plus_trilean.simps(4) plus_trilean.simps(5) plus_trilean_commutative)
qed

end
