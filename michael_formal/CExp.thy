theory CExp
  imports Syntax
begin
datatype cexp = Bc bool | Eq aexp | Lt aexp | Gt aexp | Not cexp | Or cexp cexp
datatype operator = L | G | E

type_synonym constraints = "vname \<rightharpoonup> cexp"

definition get :: "vname \<Rightarrow> constraints \<Rightarrow> cexp" where
  "get v c = (case (c v) of
    None \<Rightarrow> Bc True |
    Some a \<Rightarrow> a
  )"

fun cexp_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "cexp_plus (Bc False) _ _ = Bc False" |
  "cexp_plus _ (Bc False) _ = Bc False" |
  "cexp_plus (Bc True) _ _ = Bc True" |
  "cexp_plus _ (Bc True) _ = Bc True" |
  "cexp_plus (Eq (N n)) (Eq (N n')) _ = Eq (N (n+n'))" |
  "cexp_plus (Eq (V vb)) (Eq (N n)) c = concrete vb c"

fun compound :: "operator \<Rightarrow> cexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "compound _ (Bc True) _ = Bc True" |
  "compound _ (Bc False) _ = Bc False" |
  "compound _ (Not (Bc True)) _ = (Bc False)" |
  "compound _ (Not (Bc False)) _ = (Bc True)" |
  "compound a (Not (Not va)) c = compound a va c" |
  "compound a (Not (Eq va)) _ = Bc True" |
  "compound a (Or v va) c = Or (compound a v c) (compound a va c)" |
  "compound a (Not (Or v va)) c = Not (Or (compound a v c) (compound a va c))" |

  "compound L (Lt a) _ = Lt a" |
  "compound L (Not (Lt va)) _ = Bc True" |
  "compound L (Gt a) _ = Bc True" |
  "compound L (Not (Gt va)) _ = Lt va" |
  "compound L (Eq a) _ = Lt a" |

  "compound E (Lt (V v)) c = (case (get v c) of
    Bc v \<Rightarrow> Bc v |
    Gt _ \<Rightarrow> Bc True
  )" |
  "compound E (Lt v) _ = Lt v" |
  "compound E (Not (Lt va)) _ = (Not (Lt va))" |
  "compound E (Gt v) _ = Gt v" |
  "compound E (Not (Gt va)) _ = (Not (Gt va))" |
  "compound E (Eq v) _ = Eq v" |

  "compound G (Lt a) _ = Bc True" |
  "compound G (Not (cexp.Lt va)) _ = Gt va" |
  "compound G (Gt a) _ = Gt a" |
  "compound G (Not (cexp.Gt va)) _ = Bc True" |
  "compound G (Eq a) _ = Gt a"

fun rationalise :: "cexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "rationalise (Bc a) _ = Bc a" |
  "rationalise (Not a) c = Not (rationalise a c)" |
  "rationalise (Lt (N n)) _ = Lt (N n)" |
  "rationalise (Lt (V v)) c = compound L (get v c) c" |
  "rationalise (Eq (V v)) c = compound E (get v c) c"

value "(rationalise (Eq (V ''i1'')) (map_of [(''i1'', Lt ( V ''i2'')), (''i2'', Gt (V ''i1''))]))"

fun apply_update :: "aexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "apply_update (N n) _ = Eq (N n)" |
  "apply_update (V v) c = get v c"

end