theory New_Plus
imports "efsm-exp.CExp"
begin

fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_plus Undef b = Undef" |
  "compose_plus b Undef = Undef" |
  "compose_plus (Bc v) _ = Bc v" |
  "compose_plus _ (Bc v) = Bc v" |
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

lemma compose_plus_undef: "compose_plus Undef a = Undef"
  by simp

fun compose_minus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_minus Undef b = Undef" |
  "compose_minus b Undef = Undef" |
  "compose_minus (Bc v) _ = Bc v" |
  "compose_minus _ (Bc v) = Bc v" |
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

(*fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
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
  )) else Bc False)"*)

end