theory CExp
  imports Types
begin

datatype cexp = Undef | Bc bool | Eq "value" | Lt "value" | Gt "value" | Not cexp | And cexp cexp

(* Less than or equal to *)
abbreviation Leq :: "value \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

(* Greater than or equal to *)
abbreviation Geq :: "value \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

(* Not equal to *)
abbreviation Neq :: "value \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq  v)"

(* Logical Or in terms of And and Not*)
abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> Not (And (Not v) (Not va))"

(* Does a given value of "i" satisfy the given cexp? *)
fun ceval :: "cexp \<Rightarrow> (value \<Rightarrow> bool)" where
  "ceval Undef = (\<lambda>i. False)" |
  "ceval (Bc b) = (\<lambda>i. b)" |
  "ceval (Eq v) = (\<lambda>i. i = v)" |
  "ceval (Lt v) = (\<lambda>i. case (i, v) of ((Num a), (Num b)) \<Rightarrow> a < b | _ \<Rightarrow> False)" |
  "ceval (Gt v) = (\<lambda>i. case (i, v) of ((Num a), (Num b)) \<Rightarrow> a > b | _ \<Rightarrow> False)" |
  "ceval (Not v) = (\<lambda>i. \<not>(ceval v i))" |
  "ceval (And v va) = (\<lambda>i. (ceval v i \<and> ceval va i))"

(* Are cexps "c" and "c'" satisfied under the same conditions? *)
definition cexp_equiv :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_equiv c c' \<equiv> (\<forall>i. (ceval c i) = (ceval c' i)) \<and> c = Undef \<longleftrightarrow> c' = Undef"

(* Is cexp "c" satisfied under all "i" values? *)
definition valid :: "cexp \<Rightarrow> bool" where
  "valid c \<equiv> (\<forall> i. ceval c i)"

(* Is there some value of "i" which satisfies "c"? *)
definition satisfiable :: "cexp \<Rightarrow> bool" where
  "satisfiable v \<equiv> (\<exists>i. ceval v i)"

(* Does cexp "c" simulate "c'"? *)
definition cexp_simulates :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_simulates c c' \<equiv> (\<forall>i. ceval c' i \<longrightarrow> ceval c i) \<and> c = Undef \<longrightarrow> c' = Undef"

fun "and" :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "and (Bc False) _ = Bc False" |
  "and _ (Bc False) = Bc False" |
  "and (Bc True) x = x" |
  "and x (Bc True) = x" |
  "and c c' = And c c'"

theorem and_is_And [simp]:  "ceval (and x y) = ceval (And x y)"
proof (cases x)
  case Undef
  then show ?thesis
    apply simp
    apply (cases y)
    prefer 2
    apply (case_tac x2)
    by simp_all
next
  case (Bc x2)
  then show ?thesis
    apply simp
    apply (cases x2)
     prefer 2
     apply simp
    apply (cases y)
          apply simp_all
    apply (case_tac x2a)
    by simp_all
next
  case (Eq x3)
  then show ?thesis
    apply simp
    apply (cases y)
          apply simp_all
    apply (case_tac x2)
    by simp_all
next
case (Lt x4)
  then show ?thesis
    apply simp
    apply (cases y)
          apply simp_all
    apply (case_tac x2)
    by simp_all
next
  case (Gt x5)
  then show ?thesis
    apply simp
    apply (cases y)
          apply simp_all
    apply (case_tac x2)
    by simp_all
next
  case (Not x6)
  then show ?thesis
        apply simp
    apply (cases y)
          apply simp_all
    apply (case_tac x2)
    by simp_all
next
  case (And x71 x72)
  then show ?thesis
    apply simp
    apply (cases y)
          apply simp_all
    apply (case_tac x2)
    by simp_all
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

lemma and_true_2 [simp]: "and (Bc True) x = x"
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


fun "not" :: "cexp \<Rightarrow> cexp" where
  "not c = (case c of
    Bc True \<Rightarrow> Bc False |
    Bc False \<Rightarrow> Bc True |
    Not x \<Rightarrow> x |
    Undef \<Rightarrow> Bc True |
    c \<Rightarrow> Not c
  )"

theorem not_is_Not[simp]: "ceval (not x) = ceval (Not x)"
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
    then show ?thesis by simp_all
  next
    case (And x61 x62)
    then show ?thesis by simp_all
  next
    case (Undef)
    then show ?thesis by simp
  qed

lemma "ceval (Bc True) = ceval (Not (Bc False))"
  by simp

lemma "ceval (Bc False) = ceval (Not (Bc True))"
  by simp

lemma "\<forall> i. (ceval (And (Eq (Num 1)) (Gt (Num 2)))) i = False"
  by simp

lemma "ceval (Not (Not v)) = ceval v"
  by simp

lemma "cexp_simulates (Bc True) a"
  by (simp add: cexp_simulates_def)

lemma everything_simulates_false: "\<forall>c. c \<noteq> Undef \<longrightarrow> cexp_simulates c (Bc False)"
  by (simp add: cexp_simulates_def)

lemma "a \<noteq> Undef \<longrightarrow> cexp_simulates (Bc False) a \<longrightarrow> cexp_equiv a (Bc False)"
  by (simp add: cexp_simulates_def cexp_equiv_def)

lemma "cexp_simulates (Lt (Num 10)) (Lt (Num 5))"
  by (simp add: cexp_simulates_def)

lemma simulates_symmetry: "cexp_simulates x x"
  by (simp add: cexp_simulates_def)

(*
If the second arg is always bigger than the first (e.g. if they're both literals with the first
being bigger) then just return that. If not, is there a way for the first arg to be greater than the
second arg? If so, return it. If not, return false.
*)
(* First element is greater *)
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
  "apply_gt v (Not (And va vb)) = (Not (and (fst (apply_gt v va)) (fst (apply_gt v vb))), Not (and (snd (apply_gt v va)) (snd (apply_gt v vb))))" |
  "apply_gt (Not (And va vb)) v = (Not (and (fst (apply_gt va v)) (fst (apply_gt vb v))), Not (and (snd (apply_gt va v)) (snd (apply_gt vb v))))" |

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

lemma "compose_plus (Eq (Str ''cat'')) (Eq (Num 1)) = Bc False"
  apply (simp add: valid_def satisfiable_def)
  by auto
end
