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
  "not (Bc x) = (Bc (\<not> x))" |
  "not (Not x) = x" |
  "not x = Not x"

abbreviation Leq :: "value \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

abbreviation Geq :: "value \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

abbreviation Neq :: "value \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> not (and (not v) (not va))"

fun cexp2gexp :: "aexp \<Rightarrow> cexp \<Rightarrow>  gexp" where
  "cexp2gexp _ (Bc b) = gexp.Bc b" |
  "cexp2gexp a Undef = Null a" |
  "cexp2gexp a (Lt v) = gexp.Gt (L v) a" |
  "cexp2gexp a (Gt v) = gexp.Gt a (L v)" |
  "cexp2gexp a (Eq v) = gexp.Eq a (L v)" |
  "cexp2gexp a (Not v) = gNot (cexp2gexp a v)" |
  "cexp2gexp a (And v va) = gAnd (cexp2gexp a v) (cexp2gexp a va)"

definition cval :: "cexp \<Rightarrow> aexp \<Rightarrow> (datastate \<Rightarrow> trilean)" where
  "cval c a = gval (cexp2gexp a c)"

lemma cval_true: "cval (Bc True) a i = true"
  by (simp add: cval_def gval.simps)

lemma cval_false: "cval (cexp.Bc False) a i = false"
  by (simp add: cval_def gval.simps)

lemma cval_And_zero: "cval (And c (cexp.Bc True)) = cval c"
  apply (rule ext)+
  using cval_def gAnd_symmetry gAnd_zero gexp_equiv_def by force

lemma cval_And: "cval (And x y) a s = maybe_and (cval x a s) (cval y a s)"
  apply (simp only: cval_def)
  using gval_gAnd by auto

lemma cval_And_one: "cval (And c c) = cval c"
  apply (rule ext)+
  using cval_def cval_And maybe_and_idempotent by auto

lemma cval_And_fun: "cval (And x y) = (\<lambda>r s. maybe_and (cval x r s) (cval y r s))"
  apply (rule ext)+
  by (simp only: cval_And)

lemma and_is_And :  "cval (and x y) = cval (And x y)"
proof (induct x y rule: and.induct)
  case (1 x)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd gval.simps)
    by (simp add: maybe_double_negation maybe_or_idempotent maybe_or_zero)
next
  case "2_1"
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd gval.simps(1))
    by (simp add: maybe_and_commutative maybe_and_one)
next
  case "2_2"
  then show ?case
    apply (rule ext)+
    by (simp add: cval_def gval_gAnd gval.simps(2) gval.simps(1))
next
  case ("2_3" v)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd gval.simps(1))
    by (simp add: maybe_and_commutative maybe_and_one)
next
  case ("2_4" v)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd gval.simps(1))
    by (simp add: maybe_and_commutative maybe_and_one)
next
  case ("2_5" v)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd gval.simps(1))
    by (simp add: maybe_and_commutative maybe_and_one)
next
  case ("2_6" v)
  then show ?case
    apply (rule ext)+
    by (simp add: cval_And_zero)
next
  case ("2_7" v va)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd gval.simps(1))
    by (simp add: maybe_and_commutative maybe_and_one)
next
  case "3_1"
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd)
    by (simp add: maybe_and_idempotent)
next
  case "3_2"
  then show ?case by (simp add: cval_def)
next
  case ("3_3" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_4" v)
then show ?case by (simp add: cval_def)
next
  case ("3_5" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_6" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_7" v va)
  then show ?case by (simp add: cval_def)
next
  case "3_8"
  then show ?case by (simp add: cval_def)
next
  case "3_9"
  then show ?case
    apply (rule ext)+
    by (simp add: cval_def gval_gAnd gval.simps(2))
next
  case ("3_10" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_11" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_12" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_13" v)
then show ?case by (simp add: cval_def)
next
  case ("3_14" v va)
then show ?case by (simp add: cval_def)
next
  case ("3_15" v)
then show ?case by (simp add: cval_def)
next
  case ("3_16" v)
then show ?case by (simp add: cval_def)
next
  case ("3_17" v va)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd)
    by (simp add: maybe_and_idempotent)
next
  case ("3_18" v va)
  then show ?case by (simp add: cval_def)
next
  case ("3_19" v va)
  then show ?case by (simp add: cval_def)
next
  case ("3_20" v va)
  then show ?case by (simp add: cval_def)
next
case ("3_21" v va vb)
  then show ?case by (simp add: cval_def)
next
case ("3_22" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_23" v)
then show ?case by (simp add: cval_def)
next
  case ("3_24" v va)
  then show ?case by (simp add: cval_def)
next
case ("3_25" v va)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def gval_gAnd)
    by (simp add: maybe_and_idempotent)
next
  case ("3_26" v va)
then show ?case by (simp add: cval_def)
next
  case ("3_27" v va)
then show ?case by (simp add: cval_def)
next
  case ("3_28" v va vb)
  then show ?case by (simp add: cval_def)
next
  case ("3_29" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_30" v)
  then show ?case by (simp add: cval_def)
next
case ("3_31" v va)
  then show ?case by (simp add: cval_def)
next
case ("3_32" v va)
  then show ?case by (simp add: cval_def)
next
  case ("3_33" v va)
  then show ?case
    apply (rule ext)+
    apply (simp add: cval_def)
    by (simp add: maybe_or_idempotent or_equiv)
next
  case ("3_34" v va)
  then show ?case by (simp add: cval_def)
next
  case ("3_35" v va vb)
  then show ?case by (simp add: cval_def)
next
  case ("3_36" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_37" v)
  then show ?case by (simp add: cval_def)
next
  case ("3_38" v va)
  then show ?case by (simp add: cval_def)
next
  case ("3_39" v va)
  then show ?case by (simp add: cval_def)
next
  case ("3_40" v va)
  then show ?case by (simp add: cval_def)
next
  case ("3_41" v va)
  then show ?case
    by (simp add: cval_And_one)
next
  case ("3_42" v va vb)
  then show ?case by (simp add: cval_def)
next
  case ("3_43" v va)
  then show ?case by (simp add: cval_def)
next
  case ("3_44" v va)
  then show ?case by (simp add: cval_def)
next
case ("3_45" v va vb)
  then show ?case by (simp add: cval_def)
next
  case ("3_46" v va vb)
  then show ?case by (simp add: cval_def)
next
case ("3_47" v va vb)
  then show ?case by (simp add: cval_def)
next
  case ("3_48" v va vb)
  then show ?case by (simp add: cval_def)
next
case ("3_49" v va vb vc)
  then show ?case
    by (simp add: cval_And_one)
qed

definition valid :: "cexp \<Rightarrow> bool" where (* Is cexp "c" satisfied under all "i" values? *)
  "valid c \<equiv> (\<forall> a s. cval c a s = true)"

definition satisfiable :: "cexp \<Rightarrow> bool" where (* Is there some value of "i" which satisfies "c"? *)
  "satisfiable c \<equiv> (\<exists> a s. cval c a s = true)"

fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_plus Undef b = Undef" |
  "compose_plus b Undef = Undef" |
  "compose_plus (Bc False) _ = Bc False" |
  "compose_plus _ (Bc False) = Bc False" |
  "compose_plus (Bc True) _ = Bc True" |
  "compose_plus _ (Bc True) = Bc True" |
  "compose_plus (Eq (Num x)) (Eq (Num y)) = Eq (Num (x+y))" |
  "compose_plus (Eq (Str x)) _ = Undef" |
  "compose_plus _ (Eq (Str x)) = Undef" |
  "compose_plus (Eq (Num x)) (Lt (Num y)) = Lt (Num (x+y))" |
  "compose_plus (Lt (Num y)) (Eq (Num x)) = Lt (Num (x+y))" |
  "compose_plus (Lt (Num va)) (Lt (Num vb)) = Lt (Num (va + vb))" |
  "compose_plus (Lt (Num vb)) (Gt (Num v)) = Bc True" |
  "compose_plus (Gt (Num v)) (Lt (Num vb)) = Bc True" |
  "compose_plus _ (Lt (Str y)) = Undef" |
  "compose_plus (Lt (Str y)) _ = Undef" |
  "compose_plus (Eq (Num x)) (Gt (Num y)) = Gt (Num (x+y))" |
  "compose_plus (Gt (Num y)) (Eq (Num x)) = Gt (Num (x+y))" |
  "compose_plus (Gt (Num va)) (Gt (Num vb)) = Gt (Num (va + vb))" |
  "compose_plus _ (Gt (Str y)) = Undef" |
  "compose_plus (Gt (Str y)) _ = Undef" |
  "compose_plus a (Not va) = (if (compose_plus a va) = Undef then Undef else (compose_plus a va))" |
  "compose_plus (Not va) a = (if (compose_plus va a) = Undef then Undef else (compose_plus va a))" |
  "compose_plus a (And v va) = and (compose_plus a v) (compose_plus a va)" |
  "compose_plus (And v va) a = and (compose_plus a v) (compose_plus a va)"

fun compose_minus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_minus Undef b = Undef" |
  "compose_minus b Undef = Undef" |
  "compose_minus (Bc False) _ = Bc False" |
  "compose_minus _ (Bc False) = Bc False" |
  "compose_minus (Bc True) _ = Bc True" |
  "compose_minus _ (Bc True) = Bc True" |
  "compose_minus (Eq (Num x)) (Eq (Num y)) = Eq (Num (x-y))" |
  "compose_minus (Eq (Str x)) _ = Undef" |
  "compose_minus _ (Eq (Str x)) = Undef" |
  "compose_minus (Eq (Num x)) (Lt (Num y)) = Gt (Num (x - y))" |
  "compose_minus (Lt (Num y)) (Eq (Num x)) = Lt (Num (y - x))" |
  "compose_minus (Lt (Num a)) (Lt (Num b)) = Bc True" |
  "compose_minus (Lt (Num vb)) (Gt (Num v)) = Lt (Num (vb - v))" |
  "compose_minus (Gt (Num v)) (Lt (Num vb)) = Gt (Num (v - vb))" |
  "compose_minus _ (Lt (Str y)) = Undef" |
  "compose_minus (Lt (Str y)) _ = Undef" |
  "compose_minus (Eq (Num d)) (Gt (Num b)) = Lt (Num (d - b))" |
  "compose_minus (Gt (Num b)) (Eq (Num d)) = Gt (Num (b - d))" |
  "compose_minus (Gt (Num va)) (Gt (Num vb)) = Bc True" |
  "compose_minus _ (Gt (Str y)) = Undef" |
  "compose_minus (Gt (Str y)) _ = Undef" |
  "compose_minus a (Not va) = (if (compose_minus a va) = Undef then Undef else (compose_minus a va))" |
  "compose_minus (Not va) a = (if (compose_minus va a) = Undef then Undef else (compose_minus va a))" |
  "compose_minus a (And v va) = and (compose_minus a v) (compose_minus a va)" |
  "compose_minus (And v va) a = and (compose_minus a v) (compose_minus a va)"

lemma valid_implies_satisfiable: "valid c \<Longrightarrow> satisfiable c"
  by (simp add: valid_def satisfiable_def)

definition cexp_equiv :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_equiv c c' \<equiv> (\<forall>a s. cval c a s = cval c' a s)"

lemma cexp_equiv_reflexive: "cexp_equiv x x"
  by (simp add: cexp_equiv_def gexp_equiv_reflexive)

lemma gNegate: "gexp_equiv (gNot g) (gexp.Bc True) = gexp_equiv g (gexp.Bc False)"
  by (simp add: gexp_equiv_def gval.simps(1) gval.simps(2) maybe_negate_true not_equiv)

lemma cexp_equiv_valid: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  by (simp add: valid_def cexp_equiv_def cval_def gval.simps)

lemma cval_and: "cval (and x y) a s = maybe_and (cval x a s) (cval y a s)"
  by (simp only: and_is_And cval_And)

lemma cexp_equiv_redundant_and: "cexp_equiv (and c (and c c')) (and c c')"
  apply (simp add: cexp_equiv_def cval_and)
  by (metis maybe_and_associative maybe_and_idempotent)

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

lemma cval_Not: "cval (Not x) a s = maybe_not (cval x a s)"
  by (simp add: cval_def gval.simps maybe_or_idempotent)

lemma cval_not: "cval (not x) a s = maybe_not (cval x a s)"
proof(induct x)
  case Undef
  then show ?case by (simp add: cval_Not)
next
case (Bc x)
  then show ?case
    apply (case_tac x)
     apply (simp add: cval_false cval_true)
    by (simp add: cval_false cval_true)
next
case (Eq x)
  then show ?case by (simp add: cval_Not)
next
  case (Lt x)
  then show ?case by (simp add: cval_Not)
next
  case (Gt x)
  then show ?case by (simp add: cval_Not)
next
  case (Not x)
  then show ?case
    by (simp add: cval_Not maybe_double_negation)
next
  case (And x1 x2)
  then show ?case by (simp add: cval_Not)
qed

lemma cval_double_negation: "cval (Not (Not x)) = cval x"
  apply (rule ext)+
  by (simp only: cval_Not maybe_double_negation)

lemma valid_double_negation: "valid (Not (Not x)) = valid x"
  by (simp add: valid_def cval_double_negation)

lemma not_is_Not: "cval (not x) = cval (Not x)"
  apply (rule ext)+
  by (simp add: cval_not cval_Not)

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
  by (simp add: cval_def gval.simps ValueEq_def)

lemma invalid_undef: "\<not> valid Undef"
  apply (simp add: valid_def cval_def)
  apply (rule_tac x="V (R 1)" in exI)
  apply (rule_tac x="<R 1 := Num 5>" in exI)
  by (simp add: cval_def gval.simps ValueEq_def)

lemma satisfiable_true: "satisfiable (Bc True)"
  by (simp add: satisfiable_def cval_def gval.simps)

lemma valid_true: "valid (Bc True)"
  by (simp add: valid_def cval_def gval.simps)

lemma unsatisfiable_false: "\<not> satisfiable (Bc False)"
  by (simp add: satisfiable_def cval_def gval.simps)

lemma invalid_false: "\<not>valid (cexp.Bc False)"
  by (simp add: valid_def cval_def gval.simps)

lemma satisfiable_eq: "satisfiable (Eq x)"
  apply (simp add: satisfiable_def cval_def gval.simps ValueEq_def)
  using aval.simps(1) by blast

lemma invalid_eq: "\<not> valid (cexp.Eq x)"
  apply (simp add: valid_def cval_def)
  apply (rule_tac x="V (R 1)" in exI)
  apply (rule_tac x="<>" in exI)
  by (simp add: cval_def gval.simps ValueEq_def)

lemma satisfiable_lt: "satisfiable (Lt (Num x))"
  apply (simp add: satisfiable_def cval_def gval.simps ValueGt_def)
  by (metis (full_types) MaybeBoolInt.simps(1) aval.simps(1) lt_ex)

lemma unsatisfiable_lt: "\<not> satisfiable (Lt (Str s))"
  by (simp add: satisfiable_def cval_def gval.simps ValueGt_def)

lemma invalid_lt: "\<not> valid (Lt x)"
  apply (simp add: valid_def cval_def)
  apply (rule_tac x="V (R 1)" in exI)
  apply (rule_tac x="<>" in exI)
  by (simp add: cval_def gval.simps ValueGt_def)

lemma satisfiable_gt: "satisfiable (Gt (Num x4))"
  apply (simp add: satisfiable_def cval_def gval.simps ValueGt_def)
  by (metis (full_types) MaybeBoolInt.simps(1) aval.simps(1) zless_iff_Suc_zadd)

lemma unsatisfiable_gt: "\<not> satisfiable (Gt (Str s))"
  by (simp add: satisfiable_def cval_def gval.simps ValueGt_def)

lemma invalid_gt: "\<not> valid (cexp.Gt x5)"
  apply (simp add: valid_def cval_def)
  apply (rule_tac x="V (R 2)" in exI)
  apply (rule_tac x="<>" in exI)
  by (simp add: gval.simps ValueGt_def)

lemma satisfiable_not_undef: "satisfiable (Not (Undef))"
  apply (simp add: satisfiable_def cval_def gval.simps ValueEq_def)
  using aval.simps(1) by blast

lemma satisfiable_neq: "satisfiable (Neq x3)"
  apply (simp add: satisfiable_def cval_def gval.simps ValueEq_def)
  by (metis aval.simps(1) option.inject value.simps(4))

lemma satisfiable_leq: "satisfiable (Leq (Num x))"
  apply (simp add: satisfiable_def cval_Not maybe_negate_true)
  apply (simp add: cval_def gval.simps ValueGt_def)
  by (metis MaybeBoolInt.simps(1) aval.simps(1) minf(4))

lemma satisfiable_geq: "satisfiable (Geq (Num x))"
  apply (simp add: satisfiable_def cval_Not maybe_negate_true)
  apply (simp add: cval_def gval.simps ValueGt_def)
  by (metis MaybeBoolInt.simps(1) aval.simps(1) pinf(4))

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
  apply (induct x y rule: and.induct)
                      apply simp_all
      apply (case_tac "v = va")
       apply simp+
      apply (case_tac "v = va")
      apply simp+
      apply (case_tac "v = va")
     apply simp+
      apply (case_tac "v = va")
    apply simp+
  apply (case_tac "v = vb \<and> va = vc")
  by auto

definition mutually_exclusive :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "mutually_exclusive x y = (\<forall>a i. (cval x i a= true \<longrightarrow> cval y i a \<noteq> true) \<and>
                                 (cval y i a = true \<longrightarrow> cval x i a \<noteq> true))"

lemma mutually_exclusive_unsatisfiable_conj: "mutually_exclusive x y = (\<not> satisfiable (And x y))"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  apply (simp add: cval_And)
  by (metis (no_types, lifting) maybe_and_associative maybe_and_commutative maybe_and_idempotent maybe_and_one)

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

lemma cval_values: "(cval x i a \<noteq> false) = (cval x i a = true \<or> cval x i a = invalid)"
  by (metis maybe_not.cases trilean.distinct(1) trilean.distinct(5))

lemma x_neq_not_x: "x \<noteq> cexp.Not x"
  apply (induct_tac x)
  by auto

lemma gval_And: "gval (cexp2gexp a (And c1 c2)) = gval (gAnd (cexp2gexp a c1) (cexp2gexp a c2))"
  apply (rule ext)
  by simp

lemma gval_not: "gval (cexp2gexp a (Not c)) = gval (gNot (cexp2gexp a c))"
  apply (rule ext)
  by simp

lemma gval_True: "gval (cexp2gexp a (cexp.Bc True)) x = true"
  by (simp add: gval.simps)

lemma gval_and_cexp: "gval (cexp2gexp i c1) s \<noteq> true \<Longrightarrow>  gval (cexp2gexp i (and c2 c1)) s \<noteq> true"
  apply (simp add: gval_and gval_gAnd)
  using maybe_and.elims by blast

lemma gval_and_false: "gval (cexp2gexp r (and (cexp.Bc False) c)) s \<noteq> true"
  apply (simp add: gval_and gval_gAnd gval.simps(2))
  using maybe_and.elims by blast

lemma gval_and_false_2: "gval (cexp2gexp uu (and x (cexp.Bc False))) s \<noteq> true"
  by (metis and.simps(17) gval_and_cexp gval_and_false)

lemma and_true: "and c (cexp.Bc True) = c"
  apply (case_tac c)
        apply simp
       apply (case_tac x2)
  by auto

lemma and_self: "and x x = x"
  apply (case_tac x)
        apply simp
       apply (case_tac x2)
  by auto

lemma and_false_not_undef: "and (Bc False) c \<noteq> Undef"
  apply (induct_tac c)
        apply simp
       apply (case_tac x)
  by auto

lemma and_And_false: "x \<noteq> cexp.Bc True \<and> x \<noteq> Bc False \<Longrightarrow> and (Bc False) x = And (Bc False) x"
  apply (case_tac x)
  by auto

lemma cval_And_false: "cval (And c (Bc False)) a s \<noteq> true"
  using CExp.satisfiable_def cval_And maybe_and_not_true unsatisfiable_false by auto

subsection \<open>A Linear Ordering for Constraint Expressions\<close>
text\<open>
Contexts represent constraints as a finite set of constraint expressions, the ffold operation on
fsets is a pain to use as nothing proves. It's much easier to convert to a list and use the list
fold method. In order to convert from an fset to a list, we need a linear order. We define that
ordering here.
\<close>

instantiation cexp :: linorder begin
fun less_cexp :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "(Undef < Undef) = False" |
  "(Undef < _) = True" |

  "(Bc v < Undef) = False" |
  "(Bc v < Bc va) = less v va" |
  "(Bc v < _) = True" |

  "(Eq v < Undef) = False" |
  "(Eq v < Bc va) = False" |
  "(Eq v < Eq va) = less v va" |
  "(Eq v < _) = True" |

  "(Lt v < Undef) = False" |
  "(Lt v < Bc va) = False" |
  "(Lt v < Eq va) = False" |
  "(Lt v < Lt va) = less v va" |
  "(Lt v < _) = True" |

  "(Gt v < Gt va) = less v va" |
  "(Gt v < Not va) = True" |
  "(Gt v < And va vb) = True" |
  "(Gt v < _) = False" |

  "(Not v < Not va) = less v va" |
  "(Not v < And va vb) = True" |
  "(Not v < _) = False" |

  "(And g1 g2) < (And g1' g2') = ((g1 < g1') \<or> ((g1 = g1') \<and> (g2 < g2')))" |
  "(And vv v < _) = False"

definition less_eq_cexp :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "less_eq_cexp a b = (a < b \<or> a = b)"
declare less_eq_cexp_def [simp]

lemma undef_minimal: "Undef \<noteq> z \<Longrightarrow> Undef < z"
  apply (cases z)
  by auto

lemma hard_less: "((x::cexp) < y) = (x \<le> y \<and> \<not> y \<le> x)"
  apply (induct x y rule: less_cexp.induct)
  by auto

lemma x_leq_x: "(x::cexp) \<le> x"
  apply (induct x)
  by auto

lemma x_leq_y_or_y_lex_x: "(x::cexp) \<le> y \<or> y \<le> x"
  apply (induct x y rule: less_cexp.induct)
  by auto

lemma antisymmetry: "(x::cexp) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  apply (induct x y rule: less_cexp.induct)
                      apply simp_all
      apply auto[1]
     apply auto[1]
    apply auto[1]
   apply auto[1]
  by (meson hard_less)

lemma transitivity: "(x::cexp) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
proof (induct x y arbitrary: z rule: less_cexp.induct)
case 1
  then show ?case
    by simp
next
  case ("2_1" v)
then show ?case
  using less_eq_cexp_def undef_minimal by blast
next
case ("2_2" v)
then show ?case
  using less_eq_cexp_def undef_minimal by blast
next
case ("2_3" v)
  then show ?case
  using less_eq_cexp_def undef_minimal by blast
next
  case ("2_4" v)
  then show ?case
    using less_eq_cexp_def undef_minimal by blast
next
case ("2_5" v)
  then show ?case
    using less_eq_cexp_def undef_minimal by blast
next
  case ("2_6" v va)
then show ?case
    using less_eq_cexp_def undef_minimal by blast
next
  case (3 v)
  then show ?case
    by simp
next
  case (4 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("5_1" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("5_2" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("5_3" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("5_4" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("5_5" v va vb)
  then show ?case
    apply (cases z)
    by auto
next
  case (6 v)
  then show ?case
    apply (cases z)
    by auto
next
  case (7 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (8 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("9_1" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("9_2" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("9_3" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("9_4" v va vb)
  then show ?case
    apply (cases z)
    by auto
next
  case (10 v)
  then show ?case
    apply (cases z)
    by auto
next
  case (11 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (12 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (13 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("14_1" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("14_2" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("14_3" v va vb)
  then show ?case
    apply (cases z)
    by auto
next
  case (15 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (16 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (17 v va vb)
  then show ?case
    apply (cases z)
    by auto
next
  case ("18_1" v)
  then show ?case
    apply (cases z)
    by auto
next
  case ("18_2" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("18_3" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("18_4" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (19 v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (20 v va vb)
  then show ?case
    apply (cases z)
    by auto
next
  case ("21_1" v)
  then show ?case
    apply (cases z)
    by auto
next
  case ("21_2" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("21_3" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("21_4" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("21_5" v va)
  then show ?case
    apply (cases z)
    by auto
next
  case (22 g1 g2 g1' g2')
  then show ?case
    apply simp
    apply (case_tac "And g1' g2' = z")
     apply auto[1]
    apply simp
    apply (case_tac "g1 < g1'")
     apply simp
     apply (metis cexp.exhaust hard_less less_cexp.simps(14) less_cexp.simps(28) less_cexp.simps(31) less_cexp.simps(43) less_cexp.simps(46) less_cexp.simps(49) less_cexp.simps(7) less_eq_cexp_def)
    apply simp
    apply (case_tac "g1 = g1' \<and> g2 < g2'")
     apply simp
     apply (metis cexp.exhaust hard_less less_cexp.simps(14) less_cexp.simps(28) less_cexp.simps(31) less_cexp.simps(43) less_cexp.simps(46) less_cexp.simps(49) less_cexp.simps(7) less_eq_cexp_def)
    by simp
next
  case ("23_1" vv v)
  then show ?case
    apply (cases z)
    by auto
next
  case ("23_2" vv v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("23_3" vv v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("23_4" vv v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("23_5" vv v va)
  then show ?case
    apply (cases z)
    by auto
next
  case ("23_6" vv v va)
  then show ?case
    apply (cases z)
    by auto
qed

instance
  apply standard
  using hard_less apply blast
  apply simp
  using transitivity apply blast
  using antisymmetry apply blast
  using x_leq_y_or_y_lex_x by auto
end

end
