theory CExp
  imports Syntax
begin

datatype cexp = Bc bool | Eq int | Lt int | Gt int | Not cexp | And cexp cexp

abbreviation Leq :: "int \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

abbreviation Geq :: "int \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

abbreviation Neq :: "int \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> Not (And (Not v) (Not va))"

fun not :: "cexp \<Rightarrow> cexp" where
  "not (Bc True) = Bc False" |
  "not (Bc False) = Bc True" |
  "not (Eq v) = Neq v" |
  "not (Gt v) = Leq v" |
  "not (Lt v) = Geq v" |
  "not (Not v) = v" |
  "not (And v va) = Not (And v va)"

fun "and" :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "and (Bc True) v = v" |
  "and v (Bc True) = v" |
  "and (Bc False) _ = Bc False" |
  "and _ (Bc False) = Bc False" |
  "and _ (Not (Bc True)) = Bc False" |
  "and v (Not (Bc False)) = v" |
  "and (Not (Bc True)) v = v" |
  "and (Not (Not v)) vb = and v vb" |
  "and v (Not (Not vb)) = and v vb" |
  "and (Eq v) (Eq va) = (if v = va then Eq v else Bc False)" |
  "and (Eq v) (Lt va) = (if v < va then Eq v else Bc False)" |
  "and (Eq v) (Gt va) = (if v > va then Eq v else Bc False)" |
  "and (Eq v) (Neq va) = (if v = va then Bc False else Eq v)" |
  "and (Eq v) (Geq vb) = (if v < vb then Bc False else Eq v)" |
  "and (Eq v) (Leq vb) = (if v > vb then Bc False else Eq v)"

fun csimp :: "cexp \<Rightarrow> cexp" where
  "csimp (Bc a) = Bc a" |
  "csimp (Eq n) = Eq n" |
  "csimp (Lt n) = Lt n" |
  "csimp (Gt n) = Gt n" |
  "csimp (Not v) = not (csimp v)" |
  "csimp (And x y) = and x y"

end