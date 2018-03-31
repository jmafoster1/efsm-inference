theory CExp
  imports Syntax
begin
datatype cexp = Bc bool | Not cexp | Lt aexp | Gt aexp | Eq aexp | Or cexp cexp
datatype operator = L | G | E

type_synonym constraints = "vname \<rightharpoonup> cexp"

definition get :: "vname \<Rightarrow> constraints \<Rightarrow> cexp" where
  "get v c = (case (c v) of
    None \<Rightarrow> Bc True |
    Some a \<Rightarrow> a
  )"

fun compound :: "operator \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compound _ (Bc True) = Bc True" |
  "compound _ (Bc False) = Bc False" |
  "compound _ (Not (Bc True)) = (Bc False)" |
  "compound _ (Not (Bc False)) = (Bc True)" |
  "compound a (Not (Not va)) = compound a va" |
  "compound a (Not (Eq va)) = Bc True" |
  "compound a (Or v va) = Or (compound a v) (compound a va)" |
  "compound a (Not (Or v va)) = Not (Or (compound a v) (compound a va))" |

  "compound L (Lt a) = Lt a" |
  "compound L (Not (Lt va)) = Bc True" |
  "compound L (Gt a) = Bc True" |
  "compound L (Not (Gt va)) = Lt va" |
  "compound L (Eq a) = Lt a" |

  "compound E (Lt v) = Lt v" |
  "compound E (Not (Lt va)) = Or (Gt va) (Eq va)" |
  "compound E (Gt v) = Gt v" |
  "compound E (Not (Gt va)) = Or (Lt va) (Eq va)" |
  "compound E (Eq v) = Eq v" |

  "compound G (Lt a) = Bc True" |
  "compound G (Not (cexp.Lt va)) = Gt va" |
  "compound G (Gt a) = Gt a" |
  "compound G (Not (cexp.Gt va)) = Bc True" |
  "compound G (Eq a) = Gt a"

fun rationalise :: "cexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "rationalise (Bc a) _ = Bc a" |
  "rationalise (Not a) c = Not (rationalise a c)" |
  "rationalise (Lt (N n)) _ = Lt (N n)" |
  "rationalise (Lt (V v)) c = compound L (get v c)" |
  "rationalise (Eq (V v)) c = compound E (get v c)"

value "(rationalise (Eq (V ''i1'')) (map_of [(''i1'', Lt ( V ''i2'')), (''i2'', Gt (V ''i1''))]))"

fun apply_update :: "aexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "apply_update (N n) _ = Eq (N n)" |
  "apply_update (V v) c = get v c"

end