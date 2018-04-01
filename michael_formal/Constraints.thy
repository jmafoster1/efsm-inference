theory Constraints
imports Syntax

begin

datatype cexp = Bc bool | Eq int | Lt int | Gt int | Not cexp | And cexp cexp

type_synonym constraints = "vname \<Rightarrow> cexp"

abbreviation
  empty :: constraints where
  "empty \<equiv> \<lambda>x. Bc True"

abbreviation
  false :: constraints where
  "false \<equiv> \<lambda>x. Bc False"

definition update :: "constraints \<Rightarrow> vname \<Rightarrow> cexp \<Rightarrow> constraints" where
  "update m k v = (\<lambda>x. if x=k then v else m x)"

fun not :: "cexp \<Rightarrow> cexp" where
  "not (Bc True) = (Bc False)" |
  "not (Bc False) = (Bc True)" |
  "not (Not a) = a" |
  "not a = Not a"

fun compose_eq :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_eq (Bc False) _ = (Bc False)" |
  "compose_eq _ (Bc False) = (Bc False)" |
  "compose_eq (Not (Bc True)) _ = (Bc False)" |
  "compose_eq _ (Not (Bc True)) = (Bc False)" |
  "compose_eq (Bc True) _ = (Bc True)" |
  "compose_eq _ (Bc True) = (Bc True)" |
  "compose_eq (Not (Bc False)) _ = (Bc True)" |
  "compose_eq _ (Not (Bc False)) = (Bc True)" |
  "compose_eq a (Not (Not vb)) = compose_eq a vb" |
  "compose_eq (Not (Not vb)) a = compose_eq vb a" |
  "compose_eq a (And vb vc) = And (compose_eq a vb) (compose_eq a vc)" |
  "compose_eq (And vb vc) a = And (compose_eq vb a) (compose_eq vc a)" |
  "compose_eq (Not (And vb vc)) a = Not (And (compose_eq vb a) (compose_eq vc a))" |
  "compose_eq a (Not (And vb vc)) = Not (And (compose_eq a vb) (compose_eq a vc))" |

  "compose_eq (Eq v) (Eq va) = (if v = va then Eq v else Bc False)" |
  "compose_eq (Eq v) (Lt va) = (if v < va then Eq v else Bc False)" |
  "compose_eq (Eq v) (Gt va) = (if v > va then Eq v else Bc False)" |
  "compose_eq (Eq v) (Not (Eq va)) = (if v = va then Bc False else Eq v)" |
  "compose_eq (Eq v) (Not (Lt va)) = (if v \<ge> va then Eq v else Bc False)" |
  "compose_eq (Eq v) (Not (Gt va)) = (if v \<le> va then Eq v else Bc False)" |

  "compose_eq (Lt va) (Eq v) = (if v < va then Eq v else Bc False)" |
  "compose_eq (Lt v) (Lt va) = (if v < va then Lt v else Lt va)" |
  "compose_eq (Lt v) (Gt va) = (if va < v then And (Lt v) (Gt va) else Bc False)" |
  "compose_eq (Lt v) (Not (Eq vb)) = (if vb \<ge> v then Lt v else Bc False)" |
  "compose_eq (Lt v) (Not (Lt vb)) = (if vb < v then And (Lt v) (Not (Lt vb)) else Bc False)" |
  "compose_eq (Lt v) (Not (Gt vb)) = (if v < vb then Lt v else Lt vb)" |

  "compose_eq (Gt va) (Eq v) = (if v > va then Eq v else Bc False)" |
  "compose_eq (Gt va) (Lt v) = (if va < v then And (Lt v) (Gt va) else Bc False)" |
  "compose_eq (Gt v) (Gt va) = (if v > va then Gt v else Gt va)" |
  "compose_eq (Gt v) (Not (Eq vb)) = (if vb \<le> v then Gt v else And (Gt v) (Not (Eq vb)))" |
  "compose_eq (Gt v) (Not (Lt vb)) = (if v > vb then Gt v else Not (Lt vb))" |
  "compose_eq (Gt v) (Not (Gt vb)) = (if vb > v then And (Gt v) (Not (Gt vb)) else Bc False)" |

  "compose_eq (Not (Eq va)) (Eq v) = (if v = va then Bc False else Eq v)" |
  "compose_eq (Not (Eq vb)) (Not (Eq v)) = (if v = vb then Not (Eq v) else And (Not (Eq v)) (Not (Eq vb)))" |
  "compose_eq (Not (Eq vb)) (Not (Lt v)) = (if vb < v then Not (Lt v) else (if v = vb then Gt v else And (Not (Eq vb)) (Not (Lt v))))" |
  "compose_eq (Not (Eq vb)) (Not (Gt v)) = (if vb > v then Not (Gt v) else (if v = vb then Lt v else And (Not (Eq vb)) (Not (Gt v))))" |

  "compose_eq (Not (Lt va)) (Eq v) = (if v \<ge> va then Eq v else Bc False)" |
  "compose_eq (Not (Lt vb)) (Lt v) = (if vb < v then And (Lt v) (Not (Lt vb)) else Bc False)" |
  "compose_eq (Not (Lt vb)) (Gt v) = (if v > vb then Gt v else Not (Lt vb))" |
  "compose_eq (Not (Lt vb)) (Not (Eq v)) = (if v < vb then Not (Lt v) else And (Not (Lt vb)) (Not (Eq v)))"|
  "compose_eq (Not (Lt vb)) (Not (Lt v)) = (if vb > v then (Not (Lt vb)) else (Not (Lt v)))" |
  "compose_eq (Not (Lt vb)) (Not (Gt v)) = (if v > vb then And (Not (Lt vb)) (Not (Gt v)) else Bc False)" |

  "compose_eq (Not (Gt vb)) (Lt v) = (if v < vb then Lt v else Lt vb)" |
  "compose_eq (Not (Gt va)) (Eq v) = (if v \<le> va then Eq v else Bc False)" |
  "compose_eq (Not (Gt vb)) (Gt v) = (if vb > v then And (Gt v) (Not (Gt vb)) else Bc False)" |
  "compose_eq (Not (Gt vb)) (Not (Eq v)) = (if v > vb then Not (Gt vb) else And (Not (Gt vb)) (Not (Eq v)))"|
  "compose_eq (Not (Gt vb)) (Not (Lt v)) = (if v < vb then And (Not (Gt vb)) (Not (Lt v)) else Bc False)"|
  "compose_eq (Not (Gt vb)) (Not (Gt v)) = (if v > vb then Not (Gt vb) else Not (Gt v))"|

  "compose_eq (Not (Eq vb)) (Lt v) = (if vb \<ge> v then Lt v else Bc False)" |
  "compose_eq (Not (Eq vb)) (Gt v) = (if vb \<le> v then Gt v else And (Gt v) (Not (Eq vb)))"

fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_plus (Bc False) _ = Bc False" |
  "compose_plus _ (Bc False) = Bc False" |
  "compose_plus (Not (Bc True)) _ = Bc False" |
  "compose_plus _ (Not (Bc True)) = Bc False" |
  "compose_plus (Bc True) _ = Bc True" |
  "compose_plus _ (Bc True) = Bc True" |
  "compose_plus (Not (Bc False)) _ = Bc True" |
  "compose_plus _ (Not (Bc False)) = Bc True" |
  "compose_plus a (Not (Not vb)) = compose_plus a vb"|
  "compose_plus (Not (Not vb)) a = compose_plus vb a"|
  "compose_plus a (And va vb) = And (compose_plus a va) (compose_plus a vb)"|
  "compose_plus (And va vb) a = And (compose_plus va a) (compose_plus vb a)"|
  "compose_plus a (Not (And va vb)) = Not (And (compose_plus a va) (compose_plus a vb))"|
  "compose_plus (Not (And va vb)) a = Not (And (compose_plus va a) (compose_plus vb a))"|

  "compose_plus (Eq v) (Eq va) = Eq (v+va)" |
  "compose_plus (Eq v) (Lt va) = Lt (v+va)" |
  "compose_plus (Eq v) (Gt va) = Gt (v+va)" |
  "compose_plus (Eq v) (Not (Eq va)) = Bc True" |
  "compose_plus (Eq v) (Not (Lt va)) = Not (Lt (v+va))" |
  "compose_plus (Eq v) (Not (Gt va)) = Not (Gt (v+va))" |
  "compose_plus (Lt v) (Eq va) = Lt (v+va)" |
  "compose_plus (Lt v) (Lt va) = Lt (v+va)" |
  "compose_plus (Lt v) (Gt va) = Bc True" |
  "compose_plus (Lt v) (Not (Eq vb)) = Bc True" |
  "compose_plus (Lt v) (Not (Lt vb)) = Bc True" |
  "compose_plus (Lt v) (Not (Gt vb)) = Lt (v+vb)" |
  "compose_plus (Gt v) (Eq va) = Gt (v+va)" |
  "compose_plus (Gt v) (Lt va) = Bc True" |
  "compose_plus (Gt v) (Gt va) = Gt (v+va)" |
  "compose_plus (Gt v) (Not (Eq vb)) = Bc True" |
  "compose_plus (Gt v) (Not (Lt vb)) = Gt (v+vb)" |
  "compose_plus (Gt v) (Not (Gt vb)) = Bc True" |
  "compose_plus (Not (Eq vb)) _ = Bc True" |
  "compose_plus (Not (Lt vb)) (Eq va) = Not (Lt (vb+va))" |
  "compose_plus (Not (Gt vb)) (Eq va) = Not (Gt (vb+va))" |
  "compose_plus (Not (Lt vb)) (Lt va) = Bc True" |
  "compose_plus (Not (Gt vb)) (Lt va) = Lt (vb+va)" |
  "compose_plus (Not (Lt vb)) (Gt va) = Gt (va+vb)" |
  "compose_plus (Not (Gt vb)) (Gt va) = Bc True" |
  "compose_plus _ (Not (Eq v)) = Bc True" |
  "compose_plus (Not (Lt vb)) (Not (Lt v)) = Not (Lt (v+vb))" |
  "compose_plus (Not (Lt vb)) (Not (Gt v)) = Bc True" |
  "compose_plus (Not (Gt vb)) (Not (Lt v)) = Bc True" |
  "compose_plus (Not (Gt vb)) (Not (Gt v)) = Not (Gt (v+vb))"

fun apply_plus :: "constraints \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> cexp" where
  "apply_plus _ (N n) (N n') = Eq (n+n')" |
  "apply_plus c (V v) (N n) = compose_plus (c v) (Eq n)" |
  "apply_plus c (N n) (V v) = compose_plus (c v) (Eq n)" |
  "apply_plus c (V v) (V va) = compose_plus (c v) (c va)"

(*
fun apply_gt :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp"
If the second arg is always bigger than the first (e.g. if they're both literals with the first
being bigger) then just return that. If not, is there a way for the first arg to be greater than the
second arg? If so, return it. If not, return false.
*)

(*
fun apply_lt :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp"
If the second arg is always smaller than the first (e.g. if they're both literals with the first
being smaller) then just return that. If not, is there a way for the first arg to be smaller than the
second arg? If so, return it. If not, return false.
*)

fun apply_guard :: "constraints \<Rightarrow> guard \<Rightarrow> constraints" where
  "apply_guard c (gexp.Lt (N n) (N n')) = (if n < n' then c else false)" |
  "apply_guard c (gexp.Eq (N n) (N n')) = (if n = n' then c else false)" |
  "apply_guard c (gexp.Eq (V v) (N n)) = update c v (Eq n)" |
  "apply_guard c (gexp.Eq (N n) (V v)) = update c v (Eq n)" |
  "apply_guard c (gexp.Eq (V vb) (V v)) = (case ((c vb), (c v)) of
    (Bc True, Bc True) \<Rightarrow> c |
    (Bc True, a) \<Rightarrow> update c v a |
    (a, Bc True) \<Rightarrow> update c vb a |
    (a, b) \<Rightarrow> (let com = (compose_eq a b) in (update (update c vb com) v com))
  )" |
  "apply_guard c (gexp.Eq (V vb) (Plus v va)) = update c vb (apply_plus c v va)" |
  "apply_guard c (gexp.Eq (Plus v va) (V vb)) = update c vb (apply_plus c v va)" |

  "apply_guard c (gexp.Gt (N n) (N n')) = (if n > n' then c else false)" |
  "apply_guard c (gexp.Gt (V vb) (N n)) = update c vb (Gt n)" |
  "apply_guard c (gexp.Gt (V vb) (V v)) = (case ((c vb), (c v)) of
    (Bc True, Bc True) \<Rightarrow> c |
    (Bc True, a) \<Rightarrow> update c vb (get_greater a)
  )"|
  
  (*Don't phrase your guard like this!*)
  "apply_guard a (gexp.Eq (Plus vb vc) (N v)) = false" |
  "apply_guard a (gexp.Eq (Plus vb vc) (Plus v vd)) = false" |
  "apply_guard a (gexp.Eq (N va) (Plus vb vc)) = false"


fun apply_update :: "constraints \<Rightarrow> update_function \<Rightarrow> constraints" where
  "apply_update c (v, (N n)) = update c v (Eq n)"

primrec apply_guards :: "constraints \<Rightarrow> guard list \<Rightarrow> constraints" where
  "apply_guards c [] = c" |
  "apply_guards c (h#t) = apply_guards (apply_guard c h) t"

primrec apply_updates :: "constraints \<Rightarrow> update_function list \<Rightarrow> constraints" where
  "apply_updates c [] = c" |
  "apply_updates c (h#t) = apply_updates (apply_update c h) t"

definition anterior :: "constraints \<Rightarrow> transition \<Rightarrow> constraints" where
  "anterior c t = apply_updates (apply_guards c (Guard t)) (Updates t)"
end