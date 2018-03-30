theory CExp
  imports Syntax
begin
datatype cexp = Bc bool | Not cexp | Lt aexp | Gt aexp | Eq aexp | Or cexp cexp
datatype operator = L | G | E

type_synonym constraints = "vname \<rightharpoonup> cexp"

fun compound :: "operator \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compound _ (Bc True) = Bc True" |
  "compound _ (Bc False) = Bc False" |
  "compound _ (Not (Bc True)) = (Bc False)" |
  "compound _ (Not (Bc False)) = (Bc True)" |
  "compound a (Not (Not va)) = compound a va" |
  "compound a (cexp.Not (cexp.Eq va)) = Bc True" |
  "compound a (Or v va) = Or (compound a v) (compound a va)" |
  "compound a (Not (Or v va)) = Not (Or (compound a v) (compound a va))" |

  "compound L (Lt a) = Lt a" |
  "compound L (Gt a) = Bc True" |
  "compound L (Not (Lt va)) = Bc True" |
  "compound L (Eq a) = Lt a" |
  "compound L (cexp.Not (cexp.Gt va)) = Lt va" |

  "compound E (cexp.Not (cexp.Lt va)) = Or (Gt va) (Eq va)" |
  "compound E (cexp.Not (cexp.Gt va)) = Or (Lt va) (Eq va)" |
  "compound E (cexp.Lt v) = Lt v" |
  "compound E (cexp.Gt v) = Gt v" |
  "compound E (cexp.Eq v) = Eq v" |

  "compound G (Lt a) = Bc True" |
  "compound G (Gt a) = Gt a" |
  "compound G (Eq a) = Gt a" |
  "compound G (cexp.Not (cexp.Lt va)) = Gt va" |
  "compound G (cexp.Not (cexp.Gt va)) = Bc True"

fun rationalise :: "cexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "rationalise (Bc a) _ = Bc a" |
  "rationalise (Not a) c = Not (rationalise a c)" |
  "rationalise (Lt (N n)) _ = Lt (N n)" |
  "rationalise (Lt (V v)) c = 
  

definition get :: "vname \<Rightarrow> constraints \<Rightarrow> cexp" where
  "get v c = (case (c v) of
    None \<Rightarrow> Bc True |
    Some a \<Rightarrow> rationalise a c
  )"

fun apply_update :: "aexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "apply_update (N n) _ = Eq (N n)" |
  "apply_update (V v) c = get v c"

end