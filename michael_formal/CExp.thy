section {* Constraint Expressions *}
(* Author: Michael Foster *)
theory CExp
  imports AExp Option_Logic
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
    Undef \<Rightarrow> Bc True |
    c \<Rightarrow> Not c
  )"

(* Less than or equal to *)
abbreviation Leq :: "value \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

(* Greater than or equal to *)
abbreviation Geq :: "value \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

(* Not equal to *)
abbreviation Neq :: "value \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

(* Logical Or in terms of And and Not*)
abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> not (and (not v) (not va))"

text {*
This function takes two cexps and tries to make the first one greater than the second one by
increasing the restriction on either the first or second argument. It returns a pair which contains
the modified first and second arguments.
*}
(* This takes a LONG time to prove *)
fun apply_gt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
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

(* Does a given value of "i" satisfy the given cexp? *)
fun cval :: "cexp \<Rightarrow> (value \<Rightarrow> bool option)" where
  "cval Undef = (\<lambda>i. Some False)" |
  "cval (Bc b) = (\<lambda>i. Some b)" |
  "cval (Eq v) = (\<lambda>i. Some (i = v))" |
  "cval (Lt v) = (\<lambda>i. ValueLt (Some i) (Some v))" |
  "cval (Gt v) = (\<lambda>i. ValueGt (Some i) (Some v))" |
  "cval (Not v) = (\<lambda>i. maybe_not (cval v i))" |
  "cval (And v va) = (\<lambda>i. maybe_and (cval v i) (cval va i))"

(* Is cexp "c" satisfied under all "i" values? *)
definition valid :: "cexp \<Rightarrow> bool" where
  "valid c \<equiv> (\<forall> i. cval c i = Some True)"

(* Is there some value of "i" which satisfies "c"? *)
definition satisfiable :: "cexp \<Rightarrow> bool" where
  "satisfiable v \<equiv> (\<exists>i. cval v i = Some True)"

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
  ((Leq v), (Lt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Lt c') |                                
  ((Leq v), (Leq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Leq c') |
  ((Geq v), (Eq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
  ((Geq v), (Gt va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Gt c') |
  ((Geq v), (Geq va)) \<Rightarrow> (case value_plus (Some v) (Some va) of None \<Rightarrow> Bc False | Some c' \<Rightarrow> Geq c') |
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

lemma and_is_And [simp]:  "cval (and x y) = cval (And x y)"
  proof (cases x)
    case Undef
    then show ?thesis
      apply (cases y)
            apply simp
           apply (case_tac x2)
      by simp_all
  next
    case (Bc x2)
    then show ?thesis
      apply (cases x2)
       apply (cases y)
             apply simp
            apply (case_tac x2a)
             apply simp
            apply simp
           apply simp
          apply (rule ext)
          apply (simp add: option.case_eq_if)
         apply (rule ext)
         apply (simp add: option.case_eq_if)
        apply (rule ext)
        apply (simp add: option.case_eq_if)
        apply (rule ext)
       apply (simp add: option.case_eq_if)
      apply (cases y)
            apply simp
           apply (case_tac x2a)
      by simp_all
  next
    case (Eq x3)
    then show ?thesis
      apply (cases y)
            apply simp
           apply (case_tac x2)
      by simp_all
  next
    case (Lt x4)
    then show ?thesis
      apply (cases y)
            apply simp
           apply (case_tac x2)
            apply simp
            apply (rule ext)
            apply (simp add: option.case_eq_if)
           apply (rule ext)
           apply (simp add: option.case_eq_if)
          apply (rule ext)
          apply (simp add: option.case_eq_if)
         apply (rule ext)
         apply (simp add: option.case_eq_if)
        apply (rule ext)
        apply (simp add: option.case_eq_if)
       apply (rule ext)
       apply (simp add: option.case_eq_if)
      by simp
  next
    case (Gt x5)
    then show ?thesis
      apply (cases y)
            apply simp
           apply (case_tac x2)
            apply simp
            apply (rule ext)
            apply (simp add: option.case_eq_if)
           apply (rule ext)
           apply (simp add: option.case_eq_if)
          apply (rule ext)
          apply (simp add: option.case_eq_if)
         apply (rule ext)
         apply (simp add: option.case_eq_if)
        apply (rule ext)
        apply (simp add: option.case_eq_if)
       apply (rule ext)
       apply (simp add: option.case_eq_if)
      by simp
  next
    case (Not x6)
    then show ?thesis
      apply (case_tac "y=Bc True")
       apply simp
       apply (rule ext)
       apply (simp add: option.case_eq_if)
      apply (cases y)
            apply simp
           apply simp
          apply simp
         apply simp
        apply simp
       apply (case_tac "x6 = x6a")
        apply (rule ext)
        apply (simp add: option.case_eq_if)
       apply simp
      by simp
  next
    case (And x71 x72)
    then show ?thesis
      apply (cases y)
            apply simp
      apply (case_tac x2)
      apply (rule ext)
        apply (simp add: option.case_eq_if)
           apply simp
          apply simp
         apply simp
        apply simp
       apply simp
      apply (case_tac "x = y")
       apply (rule ext)
       apply (simp add: option.case_eq_if)
      apply (rule ext)
      by (simp add: option.case_eq_if)
  qed
  
lemma and_true [simp]: "and x (Bc True) = x"
  proof (cases x)
  case Undef
    then show ?thesis by simp
  next
    case (Bc x2)
    then show ?thesis by (cases x2, simp_all)
  next
    case (Eq x3)
    then show ?thesis by simp
  next
  case (Lt x4)
  then show ?thesis by simp
  next
  case (Gt x5)
  then show ?thesis by simp
  next
    case (Not x6)
    then show ?thesis by simp
  next
    case (And x71 x72)
    then show ?thesis by simp
  qed

theorem not_is_Not[simp]: "cval (not x) = cval (Not x)"
  proof (cases "x")
    case (Bc x1)
    then show ?thesis
      apply (case_tac "x1 = True")
      by simp_all
  next
    case (Eq x2)
    then show ?thesis by simp_all
  next
    case (Lt x3)
    then show ?thesis by simp_all
  next
    case (Gt x4)
    then show ?thesis by simp_all
  next
    case (Not x5)
    then show ?thesis
      apply simp
      apply (rule ext)
      by (simp add: option.case_eq_if)
  next
    case (And x61 x62)
    then show ?thesis by simp_all
  next
    case (Undef)
    then show ?thesis by simp
  qed

lemma true_not_false: "cval (Bc True) = cval (Not (Bc False))"
  by simp

lemma false_not_true: "cval (Bc False) = cval (Not (Bc True))"
  by simp

lemma satisfiable_eq: "satisfiable (Eq x3)"
  by (simp add: satisfiable_def)

lemma satisfiable_neq: "satisfiable (Neq x3)"
  apply (simp add: satisfiable_def)
  apply (cases x3)
   apply (rule_tac x="Num (x1+1)" in exI)
   apply simp
  apply (rule_tac x="Str (x2@''s'')" in exI)
  by simp

lemma satisfiable_leq: "satisfiable (Leq (Num x))"
  apply (simp add: satisfiable_def)
  apply (rule_tac x="Num (x-1)" in exI)
  by simp

lemma satisfiable_geq: "satisfiable (Geq (Num x))"
  apply (simp add: satisfiable_def)
  apply (rule_tac x="Num (x+1)" in exI)
  by simp

lemma satisfiable_lt: "satisfiable (Lt (Num x4))"
  apply (simp add: satisfiable_def)
  apply (rule_tac x="Num (x4-1)" in exI)
  by simp

lemma unsatisfiable_lt: "\<not> satisfiable (Lt (Str s))"
  by (simp add: satisfiable_def)

lemma satisfiable_gt: "satisfiable (Gt (Num x4))"
  apply (simp add: satisfiable_def)
  apply (rule_tac x="Num (x4+1)" in exI)
  by simp

lemma unsatisfiable_gt: "\<not> satisfiable (Gt (Str s))"
  by (simp add: satisfiable_def)

lemma satisfiable_true: "satisfiable (Bc True)"
  by (simp add: satisfiable_def)

lemma unsatisfiable_false: "\<not> satisfiable (Bc False)"
  by (simp add: satisfiable_def)

lemma satisfiable_not_undef: "satisfiable (Not (Undef))"
  by (simp add: satisfiable_def)

lemma cval_double_negation: "cval (Not (Not v)) = cval v"
  by (metis cexp.simps(54) not.simps not_is_Not)

lemma cval_not_true: "cval (Not (Bc True)) = cval (Bc False)"
  by (simp add: satisfiable_def)

lemma cval_not_false: "cval (Not (Bc False)) = cval (Bc True)"
  by (simp add: satisfiable_def)

lemma plus_num_str: "compose_plus (Eq (Str s)) (Eq (Num n)) = Bc False"
  apply (simp add: valid_def satisfiable_def)
  by auto

(* Are cexps "c" and "c'" satisfied under the same conditions? *)
definition cexp_equiv :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_equiv c c' \<equiv> (\<forall>i. (cval c i) = (cval c' i)) \<and> (c = Undef \<longleftrightarrow> c' = Undef)"

lemma cexp_equiv_reflexive: "cexp_equiv x x"
  by (simp add: cexp_equiv_def)

lemma cexp_equiv_symmetric: "cexp_equiv x y \<Longrightarrow> cexp_equiv y x"
  by (simp add: cexp_equiv_def)

lemma cexp_equiv_transitive: "cexp_equiv x y \<Longrightarrow> cexp_equiv y z \<Longrightarrow> cexp_equiv x z"
  by (simp add: cexp_equiv_def)

lemma cexp_equiv_undef: "cexp_equiv x Undef \<Longrightarrow> x = Undef"
  by (simp add: cexp_equiv_def)

lemma cexp_equiv_subst: "cexp_equiv x y \<Longrightarrow> P (cval x i) \<Longrightarrow> P (cval y i)"
  by (simp add: cexp_equiv_def)

lemma and_symmetric: "cexp_equiv (and x y) (and y x)"
  proof (induction x)
    case Undef
    then show ?case
    proof (induction y)
      case Undef
      then show ?case by (simp add: cexp_equiv_reflexive)
    next
      case (Bc x)
      then show ?case
        apply (cases x)
         apply (simp add: cexp_equiv_reflexive)
        by (simp add: cexp_equiv_def)
    next
      case (Eq x)
      then show ?case by (simp add: cexp_equiv_def)
    next
      case (Lt x)
      then show ?case
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x)")
         apply simp
        by simp
    next
      case (Gt x)
      then show ?case
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x)")
         apply simp
        by simp
    next
      case (Not y)
      then show ?case
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "maybe_not (cval y i)")
         apply simp
        by simp
    next
      case (And y1 y2)
      then show ?case
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval y1 i")
         apply simp
        apply (case_tac "cval y2 i")
         apply simp
        by simp
    qed
  next
    case (Bc x)
    then show ?case
    proof (cases y)
      case Undef
      then show ?thesis
        apply (cases x)
        by (simp_all add: cexp_equiv_def)
    next
      case (Bc x2)
      then show ?thesis
        apply (cases x2)
         apply (cases x)
          apply (simp add: cexp_equiv_def)
         apply (simp add: cexp_equiv_def)
        apply (cases x)
        by (simp_all add: cexp_equiv_def)
    next
      case (Eq x3)
      then show ?thesis
        apply (cases x)
         apply (simp add: cexp_equiv_def)
        by (simp add: cexp_equiv_def)
    next
      case (Lt x4)
      then show ?thesis
        apply (cases x)
         apply (simp add: cexp_equiv_def)
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x4)")
        by simp_all
    next
      case (Gt x5)
      then show ?thesis
        apply (cases x)
         apply (simp add: cexp_equiv_def)
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x5)")
        by simp_all
    next
      case (Not x6)
      then show ?thesis
        apply (cases x)
         apply (simp add: cexp_equiv_def)
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x6 i")
        by simp_all
    next
      case (And x71 x72)
      then show ?thesis
        apply (cases x)
         apply (simp add: cexp_equiv_def)
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x71 i")
         apply simp
        apply (case_tac "cval x72 i")
        by simp_all
    qed
  next
    case (Eq x)
    then show ?case
    proof (cases y)
      case Undef
      then show ?thesis
        by (simp add: cexp_equiv_def)
    next
      case (Bc x2)
      then show ?thesis
        apply (cases x2)
        by (simp_all add: cexp_equiv_def)
    next
      case (Eq x3)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        by auto
    next
      case (Lt x4)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x4)")
         apply simp
        by auto
    next
      case (Gt x5)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x5)")
         apply simp
        by auto
    next
      case (Not x6)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x6 i")
        by auto
    next
      case (And x71 x72)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x71 i")
         apply simp
        apply (case_tac "cval x72 i")
        by auto
    qed
  next
    case (Lt x)
    then show ?case
    proof (cases y)
      case Undef
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x)")
        by auto
    next
      case (Bc x2)
      then show ?thesis
        apply (cases x2)
         apply (simp add: cexp_equiv_def)
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x)")
        by auto
    next
      case (Eq x3)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x)")
        by auto
    next
      case (Lt x4)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply safe
        apply (case_tac "ValueLt (Some i) (Some x)")
         apply simp
         apply (case_tac "ValueLt (Some i) (Some x4)")
          apply simp
         apply simp
        apply (case_tac "ValueLt (Some i) (Some x4)")
        by auto
    next
      case (Gt x5)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x)")
         apply simp
         apply (case_tac "ValueGt (Some i) (Some x5)")
          apply simp
         apply simp
        apply (case_tac "ValueGt (Some i) (Some x5)")
        by auto
    next
      case (Not x6)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x)")
         apply (case_tac "cval x6 i")
          apply simp
         apply simp
        apply (case_tac "cval x6 i")
        by auto
    next
      case (And x71 x72)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueLt (Some i) (Some x)")
         apply (case_tac "cval x71 i")
          apply simp
         apply (case_tac "cval x72 i")
          apply simp
         apply simp
        apply (case_tac "cval x71 i")
         apply simp
        apply (case_tac "cval x72 i")
        by auto
    qed
  next
    case (Gt x)
    then show ?case
    proof (cases y)
      case Undef
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x)")
        by auto
    next
      case (Bc x2)
      then show ?thesis
        apply (cases x2)
         apply (simp add: cexp_equiv_def)
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x)")
        by auto
    next
      case (Eq x3)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x)")
        by auto
    next
      case (Lt x4)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x)")
         apply (case_tac "ValueLt (Some i) (Some x4)")
          apply simp
         apply simp
        apply (case_tac "ValueLt (Some i) (Some x4)")
        by auto
    next
      case (Gt x5)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply safe
        apply (case_tac "ValueGt (Some i) (Some x)")
         apply (case_tac "ValueGt (Some i) (Some x5)")
          apply simp
         apply simp
        apply (case_tac "ValueGt (Some i) (Some x5)")
        by auto
    next
      case (Not x6)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x)")
         apply (case_tac "cval x6 i")
          apply simp
         apply simp
        apply (case_tac "cval x6 i")
        by auto
    next
      case (And x71 x72)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "ValueGt (Some i) (Some x)")
         apply (case_tac "cval x71 i")
          apply simp
         apply (case_tac "cval x72 i")
          apply simp
         apply simp
        apply (case_tac "cval x71 i")
         apply simp
        apply (case_tac "cval x72 i")
        by auto
    qed
  next
    case (Not x)
    then show ?case
    proof (cases y)
      case Undef
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x i")
        by auto
    next
      case (Bc x2)
      then show ?thesis
        apply (cases x2)
         apply (simp add: cexp_equiv_def)
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x i")
        by auto
    next
      case (Eq x3)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x i")
        by auto
    next
      case (Lt x4)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x i")
         apply (case_tac "ValueLt (Some i) (Some x4)")
          apply simp
         apply simp
        apply (case_tac "ValueLt (Some i) (Some x4)")
        by auto
    next
      case (Gt x5)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x i")
         apply (case_tac "ValueGt (Some i) (Some x5)")
          apply simp
         apply simp
        apply (case_tac "ValueGt (Some i) (Some x5)")
        by auto
    next
      case (Not x6)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply safe
        apply (case_tac "cval x i")
         apply (case_tac "cval x6 i")
          apply simp
         apply simp
        apply (case_tac "cval x6 i")
        by auto
    next
      case (And x71 x72)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x i")
         apply (case_tac "cval x71 i")
          apply simp
         apply (case_tac "cval x72 i")
          apply simp
         apply simp
        apply (case_tac "cval x71 i")
         apply simp
        apply (case_tac "cval x72 i")
        by auto
    qed
  next
    case (And x1 x2)
    then show ?case
    proof (cases y)
      case Undef
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x1 i")
         apply simp
        apply (case_tac "cval x2 i")
         apply simp
        by simp
    next
      case (Bc v)
      then show ?thesis
        apply (cases v)
         apply (simp add: cexp_equiv_def)
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x1 i")
        apply simp
        apply (case_tac "cval x2 i")
         apply simp
        by simp
    next
      case (Eq x3)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x1 i")
         apply simp
        apply (case_tac "cval x2 i")
        by auto
    next
      case (Lt x4)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x1 i")
         apply (case_tac "ValueLt (Some i) (Some x4)")
          apply simp
         apply simp
        apply (case_tac "ValueLt (Some i) (Some x4)")
         apply (case_tac "cval x2 i")
          apply simp
         apply simp
        apply (case_tac "cval x2 i")
        by auto
    next
      case (Gt x5)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x1 i")
         apply (case_tac "ValueGt (Some i) (Some x5)")
          apply simp
         apply simp
        apply (case_tac "ValueGt (Some i) (Some x5)")
         apply (case_tac "cval x2 i")
          apply simp
         apply simp
        apply (case_tac "cval x2 i")
        by auto
    next
      case (Not x6)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply (rule allI)
        apply (case_tac "cval x1 i")
         apply (case_tac "cval x6 i")
          apply simp
         apply simp
        apply (case_tac "cval x6 i")
         apply (case_tac "cval x2 i")
          apply simp
         apply simp
        apply (case_tac "cval x2 i")
        by auto
    next
      case (And x71 x72)
      then show ?thesis
        apply (simp add: cexp_equiv_def)
        apply safe
           apply (case_tac "cval x1 i")
            apply (case_tac "cval x71 i")
             apply simp
            apply (case_tac "cval x72 i")
             apply simp
            apply simp
           apply (case_tac "cval x2 i")
            apply (case_tac "cval x71 i")
             apply simp
            apply simp
            apply (case_tac "cval x72 i")
             apply simp
            apply simp
           apply (case_tac "cval x71 i")
            apply simp
           apply (case_tac "cval x72 i")
            apply simp
           apply auto[1]
          apply (case_tac "cval x1 i")
           apply (case_tac "cval x71 i")
            apply simp
           apply simp
           apply (case_tac "cval x72 i")
            apply simp
           apply simp
          apply (case_tac "cval x2 i")
           apply (case_tac "cval x71 i")
            apply simp
           apply (case_tac "cval x72 i")
            apply simp
           apply simp
          apply (case_tac "cval x71 i")
           apply simp
          apply (case_tac "cval x72 i")
           apply simp
          apply auto[1]
         apply (case_tac "cval x1 i")
          apply (case_tac "cval x71 i")
           apply simp
          apply (case_tac "cval x72 i")
           apply simp
          apply simp
         apply (case_tac "cval x2 i")
          apply simp
        apply (case_tac "cval x71 i")
           apply simp
          apply simp
          apply (case_tac "cval x72 i")
           apply simp
          apply simp
         apply (case_tac "cval x71 i")
          apply simp
         apply (case_tac "cval x72 i")
         apply simp
         apply auto[1]
         apply (case_tac "cval x1 i")
         apply simp
         apply (case_tac "cval x71 i")
          apply simp
         apply simp
         apply (case_tac "cval x72 i")
          apply simp
         apply simp
        apply simp
        apply (case_tac "cval x2 i")
         apply simp
         apply (case_tac "cval x71 i")
          apply simp
         apply simp
         apply (case_tac "cval x72 i")
          apply simp
         apply simp
        apply simp
        apply (case_tac "cval x71 i")
        apply simp
        apply simp
        apply (case_tac "cval x72 i")
        apply simp
        by auto
    qed
  qed

definition mutually_exclusive :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "mutually_exclusive x y = (\<forall>i. (cval x i = Some True \<longrightarrow> cval y i \<noteq> Some True) \<and>
                                 (cval y i = Some True \<longrightarrow> cval x i \<noteq> Some True))"

lemma mutually_exclusive_unsatisfiable_conj: "mutually_exclusive x y = (\<not> satisfiable (And x y))"
  apply (simp add: mutually_exclusive_def satisfiable_def)
  apply safe
    apply (case_tac "cval x i")
     apply simp
    apply (case_tac "cval y i")
     apply simp
    apply simp
   apply (metis (mono_tags, lifting) option.simps(5))
  by (metis (mono_tags, lifting) option.simps(5))

lemma unsatisfiable_conj_mutually_exclusive: "\<not> satisfiable (And x y) = mutually_exclusive x y"
  by (simp add: mutually_exclusive_unsatisfiable_conj)

lemma mutually_exclusive_reflexive: "satisfiable x \<Longrightarrow> \<not> mutually_exclusive x x"
  by (simp add: mutually_exclusive_def satisfiable_def)

lemma mutually_exclusive_symmetric: "mutually_exclusive x y \<Longrightarrow> mutually_exclusive y x"
  by (simp add: mutually_exclusive_def)

lemma not_mutually_exclusive_true: "satisfiable x = (\<not> mutually_exclusive x (Bc True))"
  by (simp add: mutually_exclusive_def satisfiable_def)

end
