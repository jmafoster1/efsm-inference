section\<open>Subsumption and Generalisation\<close>
text\<open>
We now define a language of constraint expressions to express restrictions on the known values of
registers which can be grouped into \emph{contexts} which are used to extend the idea of transition
subsumption \cite{lorenzoli2008} to transitions with update functions. This forms the
underpinning of an EFSM inference technique based on transition merging.
\<close>
subsection \<open>Constraint Expressions\<close>
text\<open>
This theory defines a language to express constraints on register values. Base restrictions are
undefined, unrestricted, inconsistent, equal to a value, less than a value, greater than a value.
Expressions may be combined using either negation or conjunction to form compound expressions. We
also define syntax hacks for the relations less than or equal to, greater than or equal to, and
not equal to as well as the expression of logical ``or'' in terms of negation and conjunction.
\<close>

theory CExp
  imports AExp Option_Logic GExp
begin

datatype cexp = Undef | Bc bool | Eq "value" | Lt "value" | Gt "value" | Not cexp | And cexp cexp

fun "and" :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "and (Bc True) x = x" |
  "and x (Bc True) = x" |
  "and c c' = (if c = c' then c else And c c')"

fun "not" :: "cexp \<Rightarrow> cexp" where
  "not c = (case c of
    Bc True \<Rightarrow> Bc False |
    Bc False \<Rightarrow> Bc True |
    Not x \<Rightarrow> x |
    c \<Rightarrow> Not c
  )"

abbreviation Leq :: "value \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

abbreviation Geq :: "value \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

abbreviation Neq :: "value \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> not (and (not v) (not va))"

text \<open>
This function takes two cexps and tries to apply restrictions such that the first argument is
greater than the second. The return value is a pair of the first and second inputs with their
respective increased restrictions.
\<close>
fun apply_gt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where (* This takes a LONG time to prove *)
  "apply_gt Undef v = (Bc False, v)" |
  "apply_gt v Undef = (v, Bc False)" |
  "apply_gt (Bc False) v = (Bc False, v)" |
  "apply_gt v (Bc False) = (v, Bc False)" |
  "apply_gt v (Not (Bc True)) = (v, Bc False)" |
  "apply_gt (Not (Bc True)) v = (Bc False, v)" |
  "apply_gt v (Not (Bc False)) = apply_gt v (Bc True)" |
  "apply_gt (Not (Bc False)) v = apply_gt (Bc True) v" |
  "apply_gt v (Not (Not vb)) = apply_gt v vb" |
  "apply_gt (Not (Not vb)) v = apply_gt vb v" |

  "apply_gt v (And va vb) = (and (fst (apply_gt v va)) (fst (apply_gt v vb)), and (snd (apply_gt v va)) (snd (apply_gt v vb)))" |
  "apply_gt (And va vb) v = (and (fst (apply_gt va v)) (fst (apply_gt vb v)), and (snd (apply_gt va v)) (snd (apply_gt vb v)))" |
  "apply_gt v (Not (And va vb)) = (not (and (fst (apply_gt v va)) (fst (apply_gt v vb))), not (and (snd (apply_gt v va)) (snd (apply_gt v vb))))" |
  "apply_gt (Not (And va vb)) v = (not (and (fst (apply_gt va v)) (fst (apply_gt vb v))), not (and (snd (apply_gt va v)) (snd (apply_gt vb v))))" |

  "apply_gt (Bc True) (Bc True) = (Bc True, Bc True)" |
  "apply_gt (Eq v) (Bc True)   = (Eq v, Lt v)" |
  "apply_gt (Lt v) (Bc True)   = (Lt v, Lt v)" |
  "apply_gt (Leq va) (Bc True) = (Leq va, Lt va)" |

  "apply_gt (Bc True) (Eq v) = (Gt v, Eq v)" |
  "apply_gt (Bc True) (Geq v) = (Gt v, Geq v)" |
  "apply_gt (Bc True) (Gt v) = (Gt v, Gt v)" |
  "apply_gt (Bc True) v = (Bc True, v)" |

  "apply_gt (Lt v) (Gt va) = (and (Lt v)  (Gt va), and (Gt va) (Lt v))" |
  "apply_gt v (Leq vb) = (and v (Gt vb), Leq vb)" |
  "apply_gt v (Gt va) =  (and v (Gt va), Gt va)" |
  "apply_gt v (Lt va) = (and v (Geq va), Lt va)" |
  "apply_gt (Lt v)  (Neq vb) = (Lt v,  and (Neq vb) (Lt v))" |
  "apply_gt (Leq v) (Neq vb) = (Leq v, and (Neq vb) (Lt v))" |

  "apply_gt (Eq v) va = (Eq v, and va (Lt v))" |
  "apply_gt v (Eq va) = (and v (Gt va), Eq va)" |

  "apply_gt (Lt v) (Geq va) = (and (Lt v) (Gt va), and (Geq va) (Lt v))" |
  "apply_gt v      (Geq vb) = (and v (Gt vb), Geq vb)" |
  "apply_gt v va = (v, va)"

fun apply_lt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_lt a b = (let (ca, cb) = (apply_gt b a) in (cb, ca))"

fun cexp2gexp :: "aexp \<Rightarrow> cexp \<Rightarrow>  gexp" where
  "cexp2gexp _ (Bc b) = gexp.Bc b" |
  "cexp2gexp a Undef = Null a" |
  "cexp2gexp a (Lt v) = gexp.Gt (L v) a" |
  "cexp2gexp a (Gt v) = gexp.Gt a (L v)" |
  "cexp2gexp a (Eq v) = gexp.Eq a (L v)" |
  "cexp2gexp a (Not v) = gNot (cexp2gexp a v)" |
  "cexp2gexp a (And v va) = gAnd (cexp2gexp a v) (cexp2gexp a va)"

definition cval :: "cexp \<Rightarrow> aexp \<Rightarrow> (datastate \<Rightarrow> bool option)" where
  "cval c a = gval (cexp2gexp a c)"

lemma cval_true: "cval (Bc True) a i = Some True"
  by (simp add: cval_def gval.simps)

lemma cval_false: "cval (cexp.Bc False) a i = Some False"
  by (simp add: cval_def gval.simps)

lemma cval_And_zero: "cval (And c (cexp.Bc True)) = cval c"
  apply (rule ext)
  apply (simp add: cval_def gval.simps)
  apply (rule ext)
  apply (simp only: gval_gAnd)
  by (metis gval.simps(1) maybe_and_commutative maybe_and_zero)

lemma cval_And: "cval (And x y) a s = maybe_and (cval x a s) (cval y a s)"
  apply (simp only: cval_def)
  using gval_gAnd by auto

lemma cval_And_one: "cval (And c c) = cval c"
  apply (rule ext)+
  by (simp only: cval_And maybe_and_one)

lemma and_is_And [simp]:  "cval (and x y) = cval (And x y)"
proof(induct x y rule: and.induct)
case (1 x)
  then show ?case
    apply (rule ext)+
    by (simp add: cval_def gval.simps option.case_eq_if)
next
case "2_1"
  then show ?case
    by (simp add: cval_def gval.simps)
next
case "2_2"
  then show ?case
    by (simp add: cval_def gval.simps)
next
  case ("2_3" v)
  then show ?case
    by (simp add: cval_def gval.simps)
next
  case ("2_4" v)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval.simps)
    apply (case_tac "maybe_not (MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval x xa))")
    using option.simps(4) apply fastforce
    by (simp add: maybe_negate)
next
  case ("2_5" v)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval.simps)
    apply (case_tac "maybe_not (MaybeBoolInt (\<lambda>x y. y < x) (aval x xa) (Some v))")
    using option.simps(4) apply fastforce
    by (simp add: maybe_negate)
next
  case ("2_6" v)
  then show ?case
    by (simp add: cval_And_zero)
next
  case ("2_7" v va)
  then show ?case
    by (simp add: cval_And_zero)
next
  case "3_1"
  then show ?case
    by (simp add: cval_And_one)
next
  case "3_2"
  then show ?case by simp
next
  case ("3_3" v)
  then show ?case by simp
next
  case ("3_4" v)
  then show ?case by simp
next
case ("3_5" v)
  then show ?case by simp
next
  case ("3_6" v)
  then show ?case by simp
next
  case ("3_7" v va)
  then show ?case by simp
next
  case "3_8"
  then show ?case by simp
next
  case "3_9"
  then show ?case
    by (simp add: cval_def maybe_double_negation)
next
  case ("3_10" v)
  then show ?case by simp
next
  case ("3_11" v)
  then show ?case by simp
next
  case ("3_12" v)
  then show ?case by simp
next
  case ("3_13" v)
  then show ?case by simp
next
  case ("3_14" v va)
  then show ?case by simp
next
case ("3_15" v)
  then show ?case by simp
next
case ("3_16" v)
  then show ?case by simp
next
case ("3_17" v va)
  then show ?case
    apply (rule ext)+
    apply (simp only: cval_And)
    by (simp add: cval_And option.case_eq_if)
  next
case ("3_18" v va)
  then show ?case by simp
next
  case ("3_19" v va)
  then show ?case by simp
next
  case ("3_20" v va)
  then show ?case by simp
next
  case ("3_21" v va vb)
  then show ?case by simp
next
  case ("3_22" v)
  then show ?case by simp
next
  case ("3_23" v)
  then show ?case by simp
next
  case ("3_24" v va)
  then show ?case by simp
next
  case ("3_25" v va)
  then show ?case
    apply (rule ext)+
    apply (simp only: cval_And)
    by (metis and.simps(33) cval_And cval_And_one)
next
  case ("3_26" v va)
  then show ?case by simp
next
  case ("3_27" v va)
  then show ?case by simp
next
  case ("3_28" v va vb)
  then show ?case by simp
next
  case ("3_29" v)
  then show ?case by simp
next
  case ("3_30" v)
  then show ?case by simp
next
  case ("3_31" v va)
  then show ?case by simp
next
  case ("3_32" v va)
  then show ?case by simp
next
  case ("3_33" v va)
  then show ?case
    apply (rule ext)+
    apply (simp only: cval_And)
    by (metis and.simps(41) cval_And cval_And_one)
next
  case ("3_34" v va)
  then show ?case by simp
next
  case ("3_35" v va vb)
  then show ?case by simp
next
  case ("3_36" v)
  then show ?case by simp
next
  case ("3_37" v)
  then show ?case by simp
next
  case ("3_38" v va)
  then show ?case by simp
next
  case ("3_39" v va)
  then show ?case by simp
next
  case ("3_40" v va)
  then show ?case by simp
next
  case ("3_41" v va)
  then show ?case
    apply (rule ext)+
    apply (simp only: cval_And)
    using cval_And maybe_and_one by auto
next
  case ("3_42" v va vb)
  then show ?case by simp
next
  case ("3_43" v va)
  then show ?case by simp
next
  case ("3_44" v va)
  then show ?case by simp
next
  case ("3_45" v va vb)
  then show ?case by simp
next
  case ("3_46" v va vb)
  then show ?case by simp
next
  case ("3_47" v va vb)
  then show ?case by simp
next
  case ("3_48" v va vb)
  then show ?case by simp
next
  case ("3_49" v va vb vc)
  then show ?case
    apply (rule ext)+
    apply (simp only: cval_And)
    by (metis and.simps(57) cval_And maybe_and_one)
qed

definition valid :: "cexp \<Rightarrow> bool" where (* Is cexp "c" satisfied under all "i" values? *)
  "valid c \<equiv> (\<forall> a s. cval c a s = Some True)"

definition satisfiable :: "cexp \<Rightarrow> bool" where (* Is there some value of "i" which satisfies "c"? *)
  "satisfiable c \<equiv> (\<exists> a s. cval c a s = Some True)"

fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_plus x y = (if satisfiable x \<and> satisfiable y then (if valid x \<or> valid y then Bc True else (case (x, y) of
  ((Eq v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Eq c') |
  ((Eq v), (Lt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Eq v), (Gt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Eq v), (Leq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Eq v), (Geq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Lt v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Lt v), (Lt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Lt v), (Leq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Gt v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Gt v), (Gt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Gt v), (Geq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Leq v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Leq v), (Lt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow>Lt c') |
  ((Leq v), (Leq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Geq v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Geq v), (Gt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Geq v), (Geq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Neq _), _) \<Rightarrow> Bc True |
  (_, (Neq _)) \<Rightarrow> Bc True |
  ((Not (Not v)), va) \<Rightarrow> compose_plus v va |
  (v, (Not (Not va))) \<Rightarrow> compose_plus v va |
  ((And v va), vb) \<Rightarrow> and (compose_plus v vb) (compose_plus va vb) |
  (v, (And va vb)) \<Rightarrow> and (compose_plus v va) (compose_plus v vb) |
  ((Not (And v va)), vb) \<Rightarrow> not (and (compose_plus v vb) (compose_plus va vb)) |
  (v, (Not (And va vb))) \<Rightarrow> not (and (compose_plus v va) (compose_plus v vb)) |
  _ \<Rightarrow> Bc True
  )) else Bc False)"

fun compose_minus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_minus x y = (if satisfiable x \<and> satisfiable y then (if valid x \<or> valid y then Bc True else (case (x, y) of
  ((Eq v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Eq c') |
  ((Eq v), (Lt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Eq v), (Gt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Eq v), (Leq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Eq v), (Geq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Lt v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Lt v), (Lt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Lt v), (Leq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Gt v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Gt v), (Gt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Gt v), (Geq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Leq v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Leq v), (Lt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |
  ((Leq v), (Leq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Geq v), (Eq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Geq v), (Gt va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Geq v), (Geq va)) \<Rightarrow> (case value_minus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Neq _), _) \<Rightarrow> Bc True |
  (_, (Neq _)) \<Rightarrow> Bc True |
  ((Not (Not v)), va) \<Rightarrow> compose_minus v va |
  (v, (Not (Not va))) \<Rightarrow> compose_minus v va |
  ((And v va), vb) \<Rightarrow> and (compose_minus v vb) (compose_minus va vb) |
  (v, (And va vb)) \<Rightarrow> and (compose_minus v va) (compose_minus v vb) |
  ((Not (And v va)), vb) \<Rightarrow> not (and (compose_minus v vb) (compose_minus va vb)) |
  (v, (Not (And va vb))) \<Rightarrow> not (and (compose_minus v va) (compose_minus v vb)) |
  _ \<Rightarrow> Bc True
  )) else Bc False)"

lemma valid_implies_satisfiable: "valid c \<Longrightarrow> satisfiable c"
  by (simp add: valid_def satisfiable_def)

definition cexp_equiv :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_equiv c c' \<equiv> (\<forall>a s. cval c a s = cval c' a s)"

lemma cexp_equiv_reflexive: "cexp_equiv x x"
  by (simp add: cexp_equiv_def gexp_equiv_reflexive)

lemma gNegate: "gexp_equiv (gNot g) (gexp.Bc True) = gexp_equiv g (gexp.Bc False)"
  apply (simp add: gexp_equiv_def)
  by (metis gval.simps(1) maybe_not_c option.inject)

lemma cexp_equiv_valid: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  by (simp add: valid_def cexp_equiv_def cval_def gval.simps)

lemma cval_and: "cval (and x y) a s = maybe_and (cval x a s) (cval y a s)"
  by (simp only: and_is_And cval_And)

lemma cexp_equiv_redundant_and: "cexp_equiv (and c (and c c')) (and c c')"
  apply (simp only: cexp_equiv_def cval_and)
  by (simp add: option.case_eq_if)

lemma cval_And_commutative: "cval (And x y) a s = cval (And y x) a s"
  by (simp only: cval_And maybe_and_commutative)

lemma and_symmetric: "cexp_equiv (and x y) (and y x)"
  apply (simp only: cexp_equiv_def and_is_And)
  by (simp add: cval_And_commutative)

lemma gval_and: "gval (cexp2gexp a (and c1 c2)) = gval (gAnd (cexp2gexp a c1) (cexp2gexp a c2))"
  apply (rule ext)
  apply (simp only: gval_gAnd)
  by (metis cval_and cval_def)

lemma cexp_equiv_symmetric: "cexp_equiv x y = cexp_equiv y x"
  apply (simp only: cexp_equiv_def cval_def)
  by auto

lemma cexp_equiv_transitive: "cexp_equiv x y \<Longrightarrow> cexp_equiv y z \<Longrightarrow> cexp_equiv x z"
  by (simp add: cexp_equiv_def gexp_equiv_def)

lemma gval_and_none: "gval (cexp2gexp a y) x = None \<Longrightarrow> gval (cexp2gexp a (and z y)) x = None"
  apply (simp only: gval_and gval_gAnd)
  using maybe_and_commutative by auto

lemma cval_Not: "cval (Not x) a s = maybe_not (cval x a s)"
  by (simp add: cval_def)

lemma cval_double_negation: "cval (Not (Not x)) = cval x"
  apply (rule ext)+
  by (simp only: cval_Not maybe_double_negation)

lemma valid_double_negation: "valid (Not (Not x)) = valid x"
  by (simp add: valid_def cval_double_negation)

lemma not_is_Not[simp]: "cval (not x) = cval (Not x)"
proof(induct x)
  case Undef
  then show ?case by simp
next
  case (Bc x)
  then show ?case
    apply (simp add: cval_def gval.simps)
    apply (case_tac x)
    by (simp add: gval.simps)+
next
  case (Eq x)
  then show ?case
    by simp
next
  case (Lt x)
  then show ?case
    by simp
next
  case (Gt x)
  then show ?case
    by simp
next
  case (Not x)
  then show ?case
    apply (simp only: cval_Not maybe_double_negation)
    by simp
  next
  case (And x1 x2)
  then show ?case
    by simp
qed

lemma true_not_false: "cval (Bc True) = cval (Not (Bc False))"
  apply (rule ext)+
  by (simp add: cval_Not cval_false cval_true)

lemma false_not_true: "cval (Bc False) = cval (Not (Bc True))"
  apply (rule ext)+
  by (simp add: cval_Not cval_false cval_true)

lemma satisfiable_undef: "satisfiable Undef"
  apply (simp add: satisfiable_def)
  apply (rule_tac x="V (R 1)" in exI)
  apply (rule_tac x="<>" in exI)
  by (simp add: cval_def gval.simps)

lemma invalid_undef: "\<not> valid Undef"
  apply (simp add: valid_def cval_def)
  apply (rule_tac x="V (R 1)" in exI)
  apply (rule_tac x="<R 1 := Num 5>" in exI)
  by (simp add: cval_def gval.simps)

lemma satisfiable_true: "satisfiable (Bc True)"
  by (simp add: satisfiable_def cval_def gval.simps)

lemma valid_true: "valid (Bc True)"
  by (simp add: valid_def cval_def gval.simps)

lemma unsatisfiable_false: "\<not> satisfiable (Bc False)"
  by (simp add: satisfiable_def cval_def gval.simps)

lemma invalid_false: "\<not>valid (cexp.Bc False)"
  by (simp add: valid_def cval_def gval.simps)

lemma satisfiable_eq: "satisfiable (Eq x)"
  apply (simp add: satisfiable_def cval_def gval.simps)
  using aval.simps(1) by blast

lemma invalid_eq: "\<not> valid (cexp.Eq x)"
  apply (simp add: valid_def cval_def)
  apply (rule_tac x="V (R 1)" in exI)
  apply (rule_tac x="<>" in exI)
  by (simp add: cval_def gval.simps)

lemma satisfiable_lt: "satisfiable (Lt (Num x))"
  apply (simp add: satisfiable_def cval_def gval.simps)
  by (metis (full_types) MaybeBoolInt.simps(1) aval.simps(1) lt_ex)

lemma unsatisfiable_lt: "\<not> satisfiable (Lt (Str s))"
  by (simp add: satisfiable_def cval_def gval.simps)

lemma invalid_lt: "\<not> valid (Lt x)"
  apply (simp add: valid_def cval_def)
  apply (rule_tac x="V (R 1)" in exI)
  apply (rule_tac x="<>" in exI)
  by (simp add: cval_def gval.simps)

lemma satisfiable_gt: "satisfiable (Gt (Num x4))"
  apply (simp add: satisfiable_def cval_def gval.simps)
  by (metis (full_types) MaybeBoolInt.simps(1) aval.simps(1) zless_iff_Suc_zadd)

lemma unsatisfiable_gt: "\<not> satisfiable (Gt (Str s))"
  by (simp add: satisfiable_def cval_def gval.simps)

lemma invalid_gt: "\<not> valid (cexp.Gt x5)"
  apply (simp add: valid_def cval_def)
  apply (rule_tac x="V (R 2)" in exI)
  apply (rule_tac x="<>" in exI)
  by (simp add: gval.simps)

lemma satisfiable_not_undef: "satisfiable (Not (Undef))"
  apply (simp add: satisfiable_def cval_def gval.simps)
  using aval.simps(1) by blast

lemma satisfiable_neq: "satisfiable (Neq x3)"
  apply (simp add: satisfiable_def cval_def gval.simps)
  by (metis aval.simps(1) option.inject value.simps(4))

lemma satisfiable_leq: "satisfiable (Leq (Num x))"
  apply (simp add: satisfiable_def cval_def gval.simps)
  by (metis (no_types, lifting) MaybeBoolInt.simps(1) aval.simps(1) maybe_not_c minf(4) option.discI option.sel)

lemma satisfiable_geq: "satisfiable (Geq (Num x))"
  apply (simp add: satisfiable_def cval_def gval.simps)
  by (metis (no_types, lifting) MaybeBoolInt.simps(1) aval.simps(1) maybe_not_c option.discI option.sel pinf(4))

lemma plus_num_str: "compose_plus (Eq (Str s)) (Eq (Num n)) = Bc False"
  by (simp add: valid_def satisfiable_def cval_def gval.simps)

lemma "satisfiable (Not x) \<Longrightarrow> \<not>valid x"
proof(induct x)
case Undef
  then show ?case
    by (simp add: invalid_undef satisfiable_not_undef)
next
  case (Bc x)
  then show ?case
    by (metis (full_types) CExp.satisfiable_def false_not_true invalid_false  unsatisfiable_false)
next
  case (Eq x)
  then show ?case
    by (simp add: invalid_eq)
next
  case (Lt x)
  then show ?case
    by (simp add: invalid_lt)
next
  case (Gt x)
  then show ?case
    by (simp add: invalid_gt)
next
  case (Not x)
  then show ?case
    by (metis CExp.satisfiable_def cval_Not cval_double_negation valid_def)
next
  case (And x1 x2)
  then show ?case
    using CExp.satisfiable_def cval_Not valid_def by force
qed

lemma and_x_y_undef: "and x y = Undef \<Longrightarrow> and y x = Undef"
proof (induction x)
case Undef
  then show ?case
    apply (cases y)
          prefer 2
          apply (case_tac x2)
    by simp_all
next
  case (Bc x)
  then show ?case
    apply (cases x)
     apply (cases y)
           apply simp+
    apply (cases y)
          prefer 2
          apply (case_tac x2)
    by simp_all
next
  case (Eq x)
  then show ?case
    apply (cases y)
          apply simp
         apply (case_tac x2)
          apply simp
         apply simp
    apply (metis and.simps(25) cexp.distinct(11))
    by simp_all
next
  case (Lt x)
  then show ?case
    apply (cases y)
          apply simp
         apply (case_tac x2)
          apply simp
         apply simp
        apply simp
       apply (metis and.simps(33) cexp.distinct(11))
    by simp_all
next
case (Gt x)
  then show ?case
    apply (cases y)
          apply simp
         apply (case_tac x2)
          apply simp
         apply simp
        apply simp
       apply simp
      apply (metis and.simps(41) cexp.distinct(11))
    by simp_all
next
  case (Not x)
  then show ?case
    apply (cases y)
          apply simp
         apply (case_tac x2)
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
     apply (metis and.simps(49) cexp.distinct(11))
    by simp
next
  case (And x1 x2)
  then show ?case
    apply (cases y)
          apply simp
         apply simp
         apply (case_tac x2a)
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
     apply simp
    by (metis and.simps(57) cexp.distinct(11))
qed

definition mutually_exclusive :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "mutually_exclusive x y = (\<forall>a i. (cval x i a= Some True \<longrightarrow> cval y i a \<noteq> Some True) \<and>
                                 (cval y i a = Some True \<longrightarrow> cval x i a \<noteq> Some True))"

lemma mutually_exclusive_unsatisfiable_conj: "mutually_exclusive x y = (\<not> satisfiable (And x y))"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  apply (simp only: cval_And maybe_and_true)
  by auto

lemma unsatisfiable_conj_mutually_exclusive: "\<not> satisfiable (And x y) = mutually_exclusive x y"
  by (simp add: mutually_exclusive_unsatisfiable_conj)

lemma mutually_exclusive_reflexive: "satisfiable x \<Longrightarrow> \<not> mutually_exclusive x x"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  by auto

lemma mutually_exclusive_symmetric: "mutually_exclusive x y \<Longrightarrow> mutually_exclusive y x"
  by (simp add: mutually_exclusive_def)

lemma not_mutually_exclusive_true: "satisfiable x = (\<not> mutually_exclusive x (Bc True))"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  using valid_def valid_true by blast

lemma cval_values: "(cval x i a \<noteq> Some False) = (cval x i a = Some True \<or> cval x i a = None)"
  by auto

lemma x_neq_not_x: "x \<noteq> cexp.Not x"
  apply (induct_tac x)
  by auto

lemma gval_And: "gval (cexp2gexp a (And c1 c2)) = gval (gAnd (cexp2gexp a c1) (cexp2gexp a c2))"
  apply (rule ext)
  by simp

lemma gval_not: "gval (cexp2gexp a (Not c)) = gval (gNot (cexp2gexp a c))"
  apply (rule ext)
  by simp

lemma gval_True: "gval (cexp2gexp a (cexp.Bc True)) x = Some True"
  by (simp add: gval.simps)

lemma gval_and_cexp: "gval (cexp2gexp i c1) s \<noteq> Some True \<Longrightarrow>  gval (cexp2gexp i (and c2 c1)) s \<noteq> Some True"
  apply (simp only: gval_and gval_gAnd maybe_and_not_true)
  by simp

lemma gval_and_false: "gval (cexp2gexp r (and (cexp.Bc False) c)) s \<noteq> Some True"
  apply (simp only: gval_and gval_gAnd maybe_and_true)
  by (simp add: gval.simps)

lemma gval_and_false_2: "gval (cexp2gexp uu (and x (cexp.Bc False))) s \<noteq> Some True"
  apply (simp only: gval_and gval_gAnd)
  by (metis and.simps(17) gval_and_false maybe_and_not_true)

end
