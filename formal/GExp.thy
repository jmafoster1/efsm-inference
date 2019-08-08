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
imports AExp Trilean Option_Lexorder
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

lemma gval_gAnd: "gval (gAnd g1 g2) s = (gval g1 s) \<and>\<^sub>? (gval g2 s)"
proof(induct "gval g1 s" "gval g2 s" rule: times_trilean.induct)
case 1
  then show ?case
    by (metis gval.simps(5) maybe_and_valid maybe_not_invalid maybe_or_invalid)
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

lemma gval_gNot: "gval (gNot x) s = \<not>\<^sub>? (gval x s)"
  by (simp add: maybe_or_idempotent)

lemma nor_equiv: "gval (gNot (gOr a b)) s = gval (Nor a b) s"
  by (metis maybe_double_negation gval_gNot)

definition satisfiable :: "gexp \<Rightarrow> bool" where
  "satisfiable g \<equiv> (\<exists>i r. gval g (join_ir i r) = true)"

lemma unsatisfiable_false: "\<not> satisfiable (Bc False)"
  by (simp add: satisfiable_def)

definition "satisfiable_list l = satisfiable (fold gAnd l (Bc True))"

lemma satisfiable_true: "satisfiable (Bc True)"
  by (simp add: satisfiable_def)

definition valid :: "gexp \<Rightarrow> bool" where
  "valid g \<equiv> (\<forall>s. gval g s = true)"

lemma valid_true: "valid (Bc True)"
  by (simp add: valid_def)

definition "valid_list l = valid (fold gAnd l (Bc True))"

lemma valid_list_all_valid: "valid_list G = (\<forall>g \<in> set G. valid g)"
proof(induct G rule: rev_induct)
case Nil
  then show ?case
    by (simp add: valid_list_def valid_def)
next
case (snoc a G)
  then show ?case
    apply (simp add: valid_list_def fold_conv_foldr valid_def del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_gAnd maybe_and_true)
    by auto
qed

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
    by simp
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

definition max_input_list :: "gexp list \<Rightarrow> nat option" where
  "max_input_list g = (fold max (map (\<lambda>g. GExp.max_input g) g) None)"

lemma max_input_list_cons: "max_input_list (a # G) = max (GExp.max_input a) (max_input_list G)"
  apply (simp add: max_input_list_def)
proof -
  have "foldr max (GExp.max_input a # rev (map_tailrec GExp.max_input G)) None = foldr max (rev (None # map_tailrec GExp.max_input G)) (GExp.max_input a)"
    by (metis (no_types) Max.set_eq_fold comp_def fold.simps(2) fold_conv_foldr foldr_conv_fold list.set(2) max.commute set_rev)
  then show "fold max (map GExp.max_input G) (max (GExp.max_input a) None) = max (GExp.max_input a) (fold max (map GExp.max_input G) None)"
    by (simp add: fold_conv_foldr map_eq_map_tailrec max.commute)
qed

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

lemma no_variables_list_gval:
  "enumerate_gexp_inputs_list g = [] \<Longrightarrow>
   enumerate_gexp_regs_list g = [] \<Longrightarrow>
   gval g s = gval g s'"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis append_is_Nil_conv enumerate_gexp_inputs_list.simps(3) enumerate_gexp_regs_list.simps(3) gval.simps(4) no_variables_list_aval)
next
  case (Gt x1a x2)
  then show ?case
    by (metis Nil_is_append_conv enumerate_gexp_inputs_list.simps(4) enumerate_gexp_regs_list.simps(4) gval.simps(3) no_variables_list_aval)
next
  case (Nor a1 a2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (metis enumerate_gexp_inputs_list.simps(2) enumerate_gexp_regs_list.simps(2) gval.simps(6) no_variables_list_aval)
qed

lemma no_variables_list_valid_or_unsat:
  "enumerate_gexp_inputs_list g = [] \<Longrightarrow>
   enumerate_gexp_regs_list g = [] \<Longrightarrow>
   valid g \<or> \<not> satisfiable g"
proof(induct g)
case (Bc x)
  then show ?case
    apply (cases x)
     apply (simp add: valid_true)
    by (simp add: unsatisfiable_false)
next
case (Eq x1a x2)
  then show ?case
    apply (simp add: valid_def satisfiable_def)
    by (metis no_variables_list_aval)
next
case (Gt x1a x2)
  then show ?case
    apply (simp add: valid_def satisfiable_def)
    by (metis no_variables_list_aval)
next
  case (Nor g1 g2)
  then show ?case
    apply (simp add: valid_def satisfiable_def)
    by (metis no_variables_list_gval)
next
  case (Null x)
  then show ?case 
    apply (simp add: valid_def satisfiable_def)
    by (metis no_variables_list_aval)
qed

lemma gval_ir_take: "A \<le> length i \<Longrightarrow>
      enumerate_gexp_regs_list a = [] \<Longrightarrow>
      enumerate_gexp_inputs_list a \<noteq> [] \<Longrightarrow>
      foldr max (enumerate_gexp_inputs_list a) 0 < A \<Longrightarrow>
      gval a (join_ir (take A i) r) = gval a (join_ir i ra)"
proof(induct a)
case (Bc x)
  then show ?case
    by simp
next
  case (Eq x1a x2)
  then show ?case
    apply simp
    apply (case_tac "enumerate_aexp_inputs_list x1a = []")
     apply simp
     apply (metis aval_ir_take no_variables_list_aval)
    apply simp
    by (metis Eq.prems(1) Eq.prems(4) List.finite_set Max.set_eq_fold Max_insert aval_ir_take fold_simps(1) foldr_conv_fold list.set(2) max.commute max_0L max_less_iff_conj no_variables_list_aval set_empty set_rev)
next
  case (Gt x1a x2)
  then show ?case
    apply simp
    apply (case_tac "enumerate_aexp_inputs_list x1a = []")
     apply simp
     apply (metis aval_ir_take no_variables_list_aval)
    apply simp
    by (metis List.finite_set Max.set_eq_fold Max_insert aval_ir_take foldr.simps(1) foldr_conv_fold id_apply list.set(2) max_less_iff_conj no_variables_list_aval set_empty set_rev)
next
  case (Nor a1 a2)
  then show ?case
    apply simp
    apply clarify
    by (metis List.finite_set Max.set_eq_fold Max_insert foldr.simps(1) foldr_conv_fold id_apply list.set(2) max_less_iff_conj no_variables_list_gval set_empty set_rev)
next
  case (Null x)
  then show ?case
    apply simp
    by (metis aval_ir_take)
qed

definition max_reg :: "gexp \<Rightarrow> nat option" where
  "max_reg g = (let regs = (enumerate_gexp_regs g) in if regs = {} then None else Some (Max regs))"

lemma max_reg_gNot: "max_reg (gNot x) = max_reg x"
  by (simp add: max_reg_def)

lemma max_reg_Eq: "max_reg (Eq a b) = max (AExp.max_reg a) (AExp.max_reg b)"
  apply (simp add: max_reg_def AExp.max_reg_def Let_def max_None max_Some_Some)
  by (metis List.finite_set Max.union enumerate_aexp_regs_list)

lemma max_reg_Gt: "max_reg (Gt a b) = max (AExp.max_reg a) (AExp.max_reg b)"
  apply (simp add: max_reg_def AExp.max_reg_def Let_def max_None max_Some_Some)
  by (metis List.finite_set Max.union enumerate_aexp_regs_list max.commute)

lemma max_reg_Nor: "max_reg (Nor a b) = max (max_reg a) (max_reg b)"
  apply (simp add: max_reg_def Let_def max_None max_Some_Some)
  by (metis List.finite_set Max.union enumerate_gexp_regs_list)

lemma max_reg_Null: "max_reg (Null a) = AExp.max_reg a"
  by (simp add: AExp.max_reg_def GExp.max_reg_def)

lemma no_reg_gval_swap_regs: "GExp.max_reg g = None \<Longrightarrow> gval g (join_ir i r) = gval g (join_ir i r')"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis gval.simps(4) max_is_None max_reg_Eq no_reg_aval_swap_regs)
next
  case (Gt x1a x2)
  then show ?case
    by (metis gval.simps(3) max_is_None max_reg_Gt no_reg_aval_swap_regs)
next
  case (Nor g1 g2)
  then show ?case
    by (simp add: max_is_None max_reg_Nor)
next
  case (Null x)
  then show ?case
    by (metis gval.simps(6) max_reg_Null no_reg_aval_swap_regs)
qed

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

lemma enumerate_gexp_regs_set_reg_unconstrained:
  "\<forall>x\<in>set G. enumerate_gexp_regs x = {} \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r))"
  by (simp add: enumerate_gexp_regs_empty_reg_unconstrained)

lemma enumerate_gexp_inputs_empty_input_unconstrained:
  "enumerate_gexp_inputs g = {} \<Longrightarrow>
   \<forall>r. \<not> gexp_constrains g (V (vname.I r))"
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

lemma enumerate_gexp_inputs_set_input_unconstrained:
  "\<forall>x\<in>set G. enumerate_gexp_inputs x = {} \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (vname.I r))"
  by (simp add: enumerate_gexp_inputs_empty_input_unconstrained)

lemma input_unconstrained_gval_input_swap:
  "\<forall>r. \<not> gexp_constrains a (V (vname.I r)) \<Longrightarrow>
  (gval a (join_ir i r) = gval a (join_ir i' r))"
proof(induct a)
  case (Bc x)
  then show ?case
    by (simp add: no_variables_list_gval)
next
  case (Eq x1a x2)
  then show ?case
    apply (simp add: ValueEq_def)
    by (metis input_unconstrained_aval_input_swap)
next
  case (Gt x1a x2)
  then show ?case
    apply (simp add: ValueGt_def)
    by (metis input_unconstrained_aval_input_swap)
next
  case (Nor a1 a2)
  then show ?case
    by simp
next
  case (Null x)
  then show ?case
    by (metis gexp_constrains.simps(2) gval.simps(6) input_unconstrained_aval_input_swap)
qed

lemma register_unconstrained_gval_register_swap: "\<forall>r. \<not> gexp_constrains a (V (R r)) \<Longrightarrow> (gval a (join_ir i r) = gval a (join_ir i r'))"
proof(induct a)
  case (Bc x)
  then show ?case
    by (simp add: no_variables_list_gval)
next
  case (Eq x1a x2)
  then show ?case
    apply (simp add: ValueEq_def)
    by (metis input_unconstrained_aval_register_swap)
next
  case (Gt x1a x2)
  then show ?case
    apply (simp add: ValueGt_def)
    by (metis input_unconstrained_aval_register_swap)
next
  case (Nor a1 a2)
  then show ?case
    by simp
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
    by (simp add: no_variables_list_gval)
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
    by simp
next
  case (Null x)
  then show ?case
    by (metis gexp_constrains.simps(2) gval.simps(6) unconstrained_variable_swap_aval)
qed

lemma gval_foldr_map_gval: "gval (foldr gAnd G (Bc True)) s = foldr (\<and>\<^sub>?) (map (\<lambda>g. gval g s) G) true"
proof(induct G)
  case Nil
  then show ?case
    by simp
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_gAnd)
    by simp
qed

lemma gval_In_cons: "gval (In v (a # as)) s = (gval (Eq (V v) (L a)) s \<or>\<^sub>? gval (In v as) s)"
  apply (cases as)
   apply (simp add: ValueEq_def)
  apply (simp add: ValueEq_def)
  by (metis maybe_double_negation maybe_or_idempotent)

lemma possible_to_be_in: "s \<noteq> [] \<Longrightarrow> satisfiable (In v s)"
proof(induct s)
case Nil
  then show ?case by simp
next
  case (Cons a s)
  then show ?case
    apply (simp add: satisfiable_def gval_In_cons)
    by (metis In.simps(1) ValueEq_def add.commute gval.simps(2) join_ir_double_exists maybe_or_idempotent plus_trilean.simps(6))
qed

lemma gAnd_commute: "gval (gAnd a b) s = gval (gAnd b a) s"
  using gval_gAnd times_trilean_commutative by auto

fun null_guard :: "gexp \<Rightarrow> bool" where
  "null_guard (Null _) = True" |
  "null_guard (Nor g1 g2) = (null_guard g1 \<or> null_guard g2)" |
  "null_guard _ = False"

definition max_reg_list :: "gexp list \<Rightarrow> nat option" where
  "max_reg_list g = (fold max (map (\<lambda>g. GExp.max_reg g) g) None)"

lemma max_reg_list_cons: "max_reg_list (a # G) = max (GExp.max_reg a) (max_reg_list G)"
  apply (simp add: max_reg_list_def)
  by (metis (no_types, lifting) List.finite_set Max.insert Max.set_eq_fold fold.simps(1) id_apply list.simps(15) max.assoc set_empty)

lemma max_reg_list_append_singleton: "max_reg_list (as@[bs]) = max (max_reg_list as) (max_reg_list [bs])"
  apply (simp add: max_reg_list_def)
  by (metis max.commute max_None_r)

lemma max_reg_list_append: "max_reg_list (as@bs) = max (max_reg_list as) (max_reg_list bs)"
proof(induct bs rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: max_reg_list_def max_None_r)
next
  case (snoc x xs)
  then show ?case
    by (metis append_assoc max.assoc max_reg_list_append_singleton)
qed

definition apply_guards :: "gexp list \<Rightarrow> datastate \<Rightarrow> bool" where
  "apply_guards G s = (\<forall>g \<in> set (map (\<lambda>g. gval g s) G). g = true)"

lemmas apply_guards = datastate apply_guards_def gval.simps ValueEq_def ValueGt_def

lemma no_reg_apply_guards_swap_regs:
  "max_reg_list G = None \<Longrightarrow>
   apply_guards G (join_ir i r) = apply_guards G (join_ir i r')"
  apply (simp add: apply_guards_def max_reg_list_def)
  by (metis in_set_conv_decomp max_is_None max_reg_list_append max_reg_list_cons max_reg_list_def no_reg_gval_swap_regs)

lemma apply_guards_singleton: "(apply_guards [g] s) = (gval g s = true)"
  by (simp add: apply_guards_def)

lemma apply_guards_empty [simp]: "apply_guards [] s"
  by (simp add: apply_guards_def)

lemma apply_guards_cons: "apply_guards (a # G) c = (gval a c = true \<and> apply_guards G c)"
  by (simp add: apply_guards_def)

lemma apply_guards_double_cons: "apply_guards (y # x # G) s = (gval (gAnd y x) s = true \<and> apply_guards G s)"
  using apply_guards_cons gval_gAnd_True by auto

lemma apply_guards_append: "apply_guards (a@a') s = (apply_guards a s \<and> apply_guards a' s)"
  apply (simp add: apply_guards_def)
  by auto

lemma apply_guards_foldr: "apply_guards G s = (gval (foldr gAnd G (Bc True)) s = true)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def)
    using apply_guards_cons gval_gAnd_True by auto
qed

lemma apply_guards_rev: "apply_guards G s = apply_guards (rev G) s"
  by (simp add: apply_guards_def)

lemma rev_apply_guards: "apply_guards (rev G) s = apply_guards G s"
  by (simp add: apply_guards_def)

lemma apply_guards_fold: "apply_guards G s = (gval (fold gAnd G (Bc True)) s = true)"
  using apply_guards_rev
  by (simp add: foldr_conv_fold apply_guards_foldr)

lemma fold_apply_guards: "(gval (fold gAnd G (Bc True)) s = true) = apply_guards G s"
  by (simp add: apply_guards_fold)

lemma foldr_apply_guards: "(gval (foldr gAnd G (Bc True)) s = true) = apply_guards G s"
  by (simp add: apply_guards_foldr)

lemma apply_guards_subset: "set g' \<subseteq> set g \<Longrightarrow> apply_guards g c \<longrightarrow> apply_guards g' c"
proof(induct g)
  case Nil
  then show ?case
    by simp
next
  case (Cons a g)
  then show ?case
    apply (simp add: apply_guards_def)
    by auto
qed

lemma apply_guards_swap: 
  "apply_guards G (join_ir i r) \<Longrightarrow>
   \<forall>x\<in>set G. enumerate_gexp_regs x = {} \<Longrightarrow>
   \<forall>x\<in>set G. enumerate_gexp_inputs x = {} \<Longrightarrow>
   apply_guards G (join_ir i' r')"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    apply (simp add: apply_guards_cons)
    by (metis enumerate_gexp_inputs_list enumerate_gexp_regs_list no_variables_list_gval set_empty)
qed

lemma valid_list_apply_guards: "valid_list G \<Longrightarrow> apply_guards G s"
  by (simp add: apply_guards_def valid_list_all_valid valid_def)

lemma apply_guards_rearrange: "x \<in> set G \<Longrightarrow> apply_guards G s = apply_guards (x#G) s"
  apply (simp add: apply_guards_def)
  by auto

lemma unconstrained_variable_swap:
  "\<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (vname.I r)) \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r)) \<Longrightarrow>
   apply_guards G s = apply_guards G s'"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    unfolding apply_guards_def
    apply simp
    by (metis unconstrained_variable_swap_gval)
qed

lemma unconstrained_variable_swap_apply_guards:
  "\<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (vname.I r)) \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r)) \<Longrightarrow>
   gval (foldr gAnd G (Bc True)) s = true \<Longrightarrow>
   apply_guards G s'"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_gAnd maybe_and_true apply_guards_cons)
    apply simp
    by (metis unconstrained_variable_swap_gval)
qed

lemma max_lt_val: "max (GExp.max_input a) (max_input_list G) = Some i \<Longrightarrow> (GExp.max_input a) \<le> Some i"
  by (metis max.cobounded1)

lemma max_input_Bc: "GExp.max_input (Bc x) = None"
  by (simp add: GExp.max_input_def)

lemma gexp_max_input_nor: "GExp.max_input (Nor g1 g2) = max (GExp.max_input g1) (GExp.max_input g2)"
  apply (simp add: GExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis List.finite_set Max.union enumerate_gexp_inputs_list max_Some_Some)

lemma max_input_Eq: "GExp.max_input (Eq a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def GExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis List.finite_set Max.union enumerate_aexp_inputs_list max_Some_Some)

lemma max_reg_list_Eq: "GExp.max_reg (Eq a1 a2) = max (AExp.max_reg a1) (AExp.max_reg a2)"
  apply (simp add: AExp.max_reg_def GExp.max_reg_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis List.finite_set Max.union enumerate_aexp_regs_list max_Some_Some)

lemma max_input_Gt: "GExp.max_input (Gt a1 a2) = max (AExp.max_input a1) (AExp.max_input a2)"
  apply (simp add: AExp.max_input_def GExp.max_input_def Let_def)
  apply safe
    apply (simp add: max_None_l)
   apply (simp add: max.commute max_None_l)
  by (metis List.finite_set Max.union enumerate_aexp_inputs_list max.commute max_Some_Some)

lemma gexp_max_input_Null: "GExp.max_input (Null x) = AExp.max_input x"
  by (simp add: AExp.max_input_def GExp.max_input_def)

lemma gval_take: "GExp.max_input g < Some a \<Longrightarrow>
    gval g (join_ir i r) = gval g (join_ir (take a i) r)"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis aval_take gval.simps(4) max_input_Eq max_less_iff_conj)
next
  case (Gt x1a x2)
  then show ?case
    by (metis aval_take gval.simps(3) max_input_Gt max_less_iff_conj)
next
  case (Nor g1 g2)
  then show ?case
    by (simp add: maybe_not_eq gexp_max_input_nor)
next
  case (Null x)
  then show ?case
    by (metis aval_take gexp_max_input_Null gval.simps(6))
qed

lemma gval_take_flip: "GExp.max_input g < Some a \<Longrightarrow>
    gval g (join_ir (take a i) r) = gval g (join_ir i r)"
  by (metis gval_take)

lemma gval_no_reg_swap_regs:
  "GExp.max_input g < Some a \<Longrightarrow>
   GExp.max_reg g = None \<Longrightarrow>
   gval g (join_ir i ra) = gval g (join_ir (take a i) r)"
proof(induct g)
case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    by (metis gval_take no_reg_gval_swap_regs)
next
  case (Gt x1a x2)
  then show ?case
    by (metis gval_take no_reg_gval_swap_regs)
next
  case (Nor g1 g2)
  then show ?case
    by (simp add: gexp_max_input_nor max_reg_Nor max_is_None)
next
  case (Null x)
  then show ?case
    by (metis gval_take no_reg_gval_swap_regs)
qed

lemma max_reg_list_none_set: "(max_reg_list G = None) = (\<forall>g \<in> set G. GExp.max_reg g = None)"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: max_reg_list_def)
next
  case (Cons a G)
  then show ?case
    by (simp add: max_reg_list_cons max_is_None)
qed

lemma gval_fold_gAnd_append_singleton:
  "gval (fold gAnd (a @ [G]) (Bc True)) s = gval (fold gAnd a (Bc True)) s \<and>\<^sub>? gval G s"
  apply (simp add: fold_conv_foldr del: foldr.simps)
  by (simp only: foldr.simps comp_def gval_gAnd times_trilean_commutative)

lemma gval_fold_rev_true:
  "gval (fold gAnd (rev G) (Bc True)) s = true \<Longrightarrow>
   gval (fold gAnd G (Bc True)) s = true"
  by (simp add: fold_conv_foldr gval_foldr_true)

lemma gval_fold_not_invalid_all_valid_contra:
  "\<exists>g \<in> set G. gval g s = invalid \<Longrightarrow>
   gval (fold gAnd G (Bc True)) s = invalid"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp only: gval_fold_gAnd_append_singleton)
    apply simp
    using maybe_and_valid by blast
qed

lemma gval_fold_not_invalid_all_valid:
  "gval (fold gAnd G (Bc True)) s \<noteq> invalid \<Longrightarrow>
   \<forall>g \<in> set G. gval g s \<noteq> invalid"
  using gval_fold_not_invalid_all_valid_contra by blast

lemma all_gval_not_false:
  "(\<forall>g \<in> set G. gval g s \<noteq> false) = (\<forall>g \<in> set G. gval g s = true) \<or> (\<exists>g \<in> set G. gval g s = invalid)"
  using trilean.exhaust by auto

lemma must_have_one_false_contra:
  "\<forall>g \<in> set G. gval g s \<noteq> false \<Longrightarrow>
   gval (fold gAnd G (Bc True)) s \<noteq> false"
  using all_gval_not_false[of G s]
  apply simp
  apply (case_tac "(\<forall>g\<in>set G. gval g s = true)")
  apply simp
  try

lemma must_have_one_false:
  "gval (fold gAnd G (Bc True)) s = false \<Longrightarrow>
   \<exists>g \<in> set G. gval g s = false"
  using must_have_one_false_contra by blast

lemma all_valid_fold: "\<forall>g \<in> set G. gval g s \<noteq> invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s \<noteq> invalid"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_gAnd)
    by (simp add: maybe_and_invalid)
qed

lemma one_false_all_valid_false: "\<exists>g\<in>set G. gval g s = false \<Longrightarrow> \<forall>g\<in>set G. gval g s \<noteq> invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s = false"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    apply (simp only: foldr.simps comp_def gval_gAnd)
    apply (case_tac "gval x s = false")
     apply simp
     apply (case_tac "gval (foldr gAnd (rev xs) (Bc True)) s")
       apply simp
      apply simp
     apply simp
    using all_valid_fold
     apply (simp add: fold_conv_foldr)
    apply simp
    by (metis maybe_not.cases times_trilean.simps(5))
qed

lemma gval_fold_rev_false: "gval (fold gAnd (rev G) (Bc True)) s = false \<Longrightarrow> gval (fold gAnd G (Bc True)) s = false"
  using must_have_one_false[of "rev G" s]
        gval_fold_not_invalid_all_valid[of "rev G" s]
  by (simp add: one_false_all_valid_false)

lemma fold_invalid_means_one_invalid: "gval (fold gAnd G (Bc True)) s = invalid \<Longrightarrow> \<exists>g \<in> set G. gval g s = invalid"
  using all_valid_fold by blast

lemma gval_fold_rev_invalid: "gval (fold gAnd (rev G) (Bc True)) s = invalid \<Longrightarrow> gval (fold gAnd G (Bc True)) s = invalid"
  using fold_invalid_means_one_invalid[of "rev G" s]
  by (simp add: gval_fold_not_invalid_all_valid_contra)

lemma gval_fold_rev_equiv_fold: "gval (fold gAnd (rev G) (Bc True)) s =  gval (fold gAnd G (Bc True)) s"
  apply (cases "gval (fold gAnd (rev G) (Bc True)) s")
    apply (simp add: gval_fold_rev_true)
   apply (simp add: gval_fold_rev_false)
  by (simp add: gval_fold_rev_invalid)

lemma gval_fold_equiv_fold_rev: "gval (fold gAnd G (Bc True)) s = gval (fold gAnd (rev G) (Bc True)) s"
  by (simp add: gval_fold_rev_equiv_fold)

lemma gval_fold_gAnd: "gval (fold gAnd G (Bc True)) s = fold (\<and>\<^sub>?) (map (\<lambda>g. gval g s) G) true"
proof(induct G rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc a G)
  then show ?case
    apply (simp add: fold_conv_foldr del: foldr.simps)
    by (simp only: foldr.simps comp_def gval_gAnd)
qed

lemma gval_fold_equiv_gval_foldr: "gval (fold gAnd G (Bc True)) s = gval (foldr gAnd G (Bc True)) s"
proof -
  have "gval (fold gAnd G (Bc True)) s = gval (fold gAnd (rev G) (Bc True)) s"
    using gval_fold_equiv_fold_rev by force
then show ?thesis
by (simp add: foldr_conv_fold)
qed

lemma gval_foldr_equiv_gval_fold: "gval (foldr gAnd G (Bc True)) s = gval (fold gAnd G (Bc True)) s"
  by (simp add: gval_fold_equiv_gval_foldr)

end
