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

abbreviation
  Leq :: "int \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

abbreviation
  Geq :: "int \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

abbreviation
  Neq :: "int \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

(* I'd like to have Not (Not v) = v *)

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
  "compose_eq (Eq v) (Neq va) = (if v = va then Bc False else Eq v)" |
  "compose_eq (Eq v) (Not (Lt va)) = (if v \<ge> va then Eq v else Bc False)" |
  "compose_eq (Eq v) (Leq va) = (if v \<le> va then Eq v else Bc False)" |

  "compose_eq (Lt va) (Eq v) = (if v < va then Eq v else Bc False)" |
  "compose_eq (Lt v) (Lt va) = (if v < va then Lt v else Lt va)" |
  "compose_eq (Lt v) (Gt va) = (if va < v then And (Lt v) (Gt va) else Bc False)" |
  "compose_eq (Lt v) (Neq vb) = (if vb \<ge> v then Lt v else Bc False)" |
  "compose_eq (Lt v) (Not (Lt vb)) = (if vb < v then And (Lt v) (Not (Lt vb)) else Bc False)" |
  "compose_eq (Lt v) (Leq vb) = (if v < vb then Lt v else Lt vb)" |

  "compose_eq (Gt va) (Eq v) = (if v > va then Eq v else Bc False)" |
  "compose_eq (Gt va) (Lt v) = (if va < v then And (Lt v) (Gt va) else Bc False)" |
  "compose_eq (Gt v) (Gt va) = (if v > va then Gt v else Gt va)" |
  "compose_eq (Gt v) (Neq vb) = (if vb \<le> v then Gt v else And (Gt v) (Neq vb))" |
  "compose_eq (Gt v) (Not (Lt vb)) = (if v > vb then Gt v else Not (Lt vb))" |
  "compose_eq (Gt v) (Leq vb) = (if vb > v then And (Gt v) (Leq vb) else Bc False)" |

  "compose_eq (Neq va) (Eq v) = (if v = va then Bc False else Eq v)" |
  "compose_eq (Neq vb) (Neq v) = (if v = vb then Neq v else And (Neq v) (Neq vb))" |
  "compose_eq (Neq vb) (Not (Lt v)) = (if vb < v then Not (Lt v) else (if v = vb then Gt v else And (Neq vb) (Not (Lt v))))" |
  "compose_eq (Neq vb) (Leq v) = (if vb > v then Leq v else (if v = vb then Lt v else And (Neq vb) (Leq v)))" |

  "compose_eq (Not (Lt va)) (Eq v) = (if v \<ge> va then Eq v else Bc False)" |
  "compose_eq (Not (Lt vb)) (Lt v) = (if vb < v then And (Lt v) (Not (Lt vb)) else Bc False)" |
  "compose_eq (Not (Lt vb)) (Gt v) = (if v > vb then Gt v else Not (Lt vb))" |
  "compose_eq (Not (Lt vb)) (Neq v) = (if v < vb then Not (Lt v) else And (Not (Lt vb)) (Neq v))"|
  "compose_eq (Not (Lt vb)) (Not (Lt v)) = (if vb > v then (Not (Lt vb)) else (Not (Lt v)))" |
  "compose_eq (Not (Lt vb)) (Leq v) = (if v > vb then And (Not (Lt vb)) (Leq v) else Bc False)" |

  "compose_eq (Leq vb) (Lt v) = (if v < vb then Lt v else Lt vb)" |
  "compose_eq (Leq va) (Eq v) = (if v \<le> va then Eq v else Bc False)" |
  "compose_eq (Leq vb) (Gt v) = (if vb > v then And (Gt v) (Leq vb) else Bc False)" |
  "compose_eq (Leq vb) (Neq v) = (if v > vb then Leq vb else And (Leq vb) (Neq v))"|
  "compose_eq (Leq vb) (Not (Lt v)) = (if v < vb then And (Leq vb) (Not (Lt v)) else Bc False)"|
  "compose_eq (Leq vb) (Leq v) = (if v > vb then Leq vb else Leq v)"|

  "compose_eq (Neq vb) (Lt v) = (if vb \<ge> v then Lt v else Bc False)" |
  "compose_eq (Neq vb) (Gt v) = (if vb \<le> v then Gt v else And (Gt v) (Neq vb))"

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
  "compose_plus (Neq vb) _ = Bc True" |
  "compose_plus _ (Neq vb) = Bc True" |

  "compose_plus (Eq v) (Eq va) = Eq (v+va)" |
  "compose_plus (Eq v) (Lt va) = Lt (v+va)" |
  "compose_plus (Eq v) (Gt va) = Gt (v+va)" |
  "compose_plus (Eq v) (Not (Lt va)) = Not (Lt (v+va))" |
  "compose_plus (Eq v) (Leq va) = Not (Gt (v+va))" |
  "compose_plus (Lt v) (Eq va) = Lt (v+va)" |
  "compose_plus (Lt v) (Lt va) = Lt (v+va)" |
  "compose_plus (Lt v) (Gt va) = Bc True" |
  "compose_plus (Lt v) (Not (Lt vb)) = Bc True" |
  "compose_plus (Lt v) (Leq vb) = Lt (v+vb)" |
  "compose_plus (Gt v) (Eq va) = Gt (v+va)" |
  "compose_plus (Gt v) (Lt va) = Bc True" |
  "compose_plus (Gt v) (Gt va) = Gt (v+va)" |
  "compose_plus (Gt v) (Not (Lt vb)) = Gt (v+vb)" |
  "compose_plus (Gt v) (Leq vb) = Bc True" |
  "compose_plus (Not (Lt vb)) (Eq va) = Not (Lt (vb+va))" |
  "compose_plus (Leq vb) (Eq va) = Not (Gt (vb+va))" |
  "compose_plus (Not (Lt vb)) (Lt va) = Bc True" |
  "compose_plus (Leq vb) (Lt va) = Lt (vb+va)" |
  "compose_plus (Not (Lt vb)) (Gt va) = Gt (va+vb)" |
  "compose_plus (Leq vb) (Gt va) = Bc True" |
  "compose_plus (Not (Lt vb)) (Not (Lt v)) = Not (Lt (v+vb))" |
  "compose_plus (Not (Lt vb)) (Leq v) = Bc True" |
  "compose_plus (Leq vb) (Not (Lt v)) = Bc True" |
  "compose_plus (Leq vb) (Leq v) = Not (Gt (v+vb))"

fun apply_plus :: "constraints \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> cexp" where
  "apply_plus _ (N n) (N n') = Eq (n+n')" |
  "apply_plus c (V v) (N n) = compose_plus (c v) (Eq n)" |
  "apply_plus c (N n) (V v) = compose_plus (c v) (Eq n)" |
  "apply_plus c (V v) (V va) = compose_plus (c v) (c va)"

fun NOT :: "cexp \<Rightarrow> cexp" where
  "NOT (Bc True) = Bc False" |
  "NOT (Bc False) = Bc True" |
  "NOT (Not v) = v" |
  "NOT a = Not a" 

(*
If the second arg is always bigger than the first (e.g. if they're both literals with the first
being bigger) then just return that. If not, is there a way for the first arg to be greater than the
second arg? If so, return it. If not, return false.
*)
(* First element is greater *)
fun apply_gt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_gt (Bc False) v = (Bc False, v)" |
  "apply_gt v (Bc False) = (v, Bc False)" |
  "apply_gt v (Not (Bc True)) = (v, Bc False)" |
  "apply_gt (Not (Bc True)) v = (Bc False, v)" |
  "apply_gt v (Not (Bc False)) = apply_gt v (Bc True)" |
  "apply_gt (Not (Bc False)) v = apply_gt (Bc True) v" |
  "apply_gt v (Not (Not vb)) = apply_gt v vb" |
  "apply_gt (Not (Not vb)) v = apply_gt vb v" |

  "apply_gt v (And va vb) = (And (fst (apply_gt v va)) (fst (apply_gt v vb)), And (snd (apply_gt v va)) (snd (apply_gt v vb)))" |
  "apply_gt (And va vb) v = (And (fst (apply_gt va v)) (fst (apply_gt vb v)), And (snd (apply_gt va v)) (snd (apply_gt vb v)))" |
  "apply_gt v (Not (And va vb)) = (Not (And (fst (apply_gt v va)) (fst (apply_gt v vb))), Not (And (snd (apply_gt v va)) (snd (apply_gt v vb))))" |
  "apply_gt (Not (And va vb)) v = (Not (And (fst (apply_gt va v)) (fst (apply_gt vb v))), Not (And (snd (apply_gt va v)) (snd (apply_gt vb v))))" |
  
  "apply_gt (Bc True) (Bc True) = (Bc True, Bc True)" |
  "apply_gt (Bc True) (Eq v) = (Gt v, Eq v)" |
  "apply_gt (Bc True) (Lt v) = (Bc True, Lt v)" |
  "apply_gt (Bc True) (Gt v) = (Gt v, Gt v)" | (* Not SUFFICIENT for greater but NECESSARY *)
  "apply_gt (Bc True) (Neq v) = (Bc True, Neq v)" |
  "apply_gt (Bc True) (Not (Lt v)) = (Gt v, Not (Lt v))" |
  "apply_gt (Bc True) (Leq v) = (Bc True, Leq v)" |
  "apply_gt (Eq v) (Bc True) = (Eq v, Lt v)" |
  "apply_gt (Eq v) (Eq va) = (if v > va then (Eq v, Eq va) else (Bc False, Bc False))" |
  "apply_gt (Eq v) (Lt va) = (if v > va then (Eq v, Lt va) else (Eq v, Lt v))" |
  "apply_gt (Eq v) (Gt va) = (if v > va then (Eq v, And (Gt va) (Lt v)) else (Bc False, Bc False))" |
  "apply_gt (Eq v) (Neq va) = (if va \<le> v then (Eq v, Lt v) else (Eq v, And (Lt v) (Neq va)))" |
  "apply_gt (Eq v) (Not (Lt va)) = (if v \<le> va then (Bc False, Bc False) else (Eq v, And (Not (Lt va)) (Lt v)))" |
  "apply_gt (Eq v) (Leq va) = (if va < v then (Eq v, (Leq va)) else (Eq v, Lt v))" |
  "apply_gt (Lt v) (Bc True) = (Lt v, Lt v)" |
  "apply_gt (Lt v) (Eq va) = (if v \<le> va then (Bc False, Bc False) else (And (Lt v) (Gt va), Eq va))" |
  "apply_gt (Lt v) (Lt va) = (if v \<le> va then (Bc False, Bc False) else (Lt v, Lt va))" |
  "apply_gt (Lt v) (Gt va) = (if v \<le> va then (Bc False, Bc False) else (And (Lt v) (Gt va), And (Gt va) (Lt v)))" |
  "apply_gt (Lt v) (Neq vb) = (if vb \<ge> v then (Lt v, Lt v) else (Lt v, And (Lt v) (Neq vb)))" |
  "apply_gt (Lt v) (Geq va) = (if v \<le> va then (Bc False, Bc False) else (And (Lt v) (Gt va), And (Lt v) (Not (Lt va))))" |
  "apply_gt (Lt v) (Leq va) = (if v \<le> va then (Bc False, Bc False) else (Lt v, Leq va))" |
  "apply_gt (Gt v) (Bc True) = (Gt v, Bc True)" |
  "apply_gt (Gt v) (Eq va) = (if v > va then (Gt v, Eq va) else (Gt va, Eq va))" |
  "apply_gt (Gt v) (Lt va) = (Gt v, Lt va)" |
  "apply_gt (Gt v) (Gt va) = (if va \<ge> v then (Gt va, Gt va) else (Gt v, Gt va))" |
  "apply_gt (Gt v) (Neq vb) = (if vb > v then (Gt v, Leq v) else (Gt v, And (Leq v) (Neq vb)))" |
  "apply_gt (Gt v) (Not (Lt va)) = (if va \<ge> v then (Gt va, Not (Lt va)) else (Gt v, Not (Lt va)))" |
  "apply_gt (Gt v) (Leq va) = (Gt v, Leq va)" |
  "apply_gt (Neq va) (Bc True) = (Neq va, Bc True)" |
  "apply_gt (Geq va) (Bc True) = (Geq va, Lt va)" |
  "apply_gt (Leq va) (Bc True) = (Leq va, Lt va)" |
  "apply_gt (Neq vb) (Eq va) = (if vb \<le> va then (Gt va, Eq va) else (And (Gt va) (Neq vb), Eq va))" |
  "apply_gt (Geq vb) (Eq va) = (if vb \<le> va then (Gt va, Eq va) else (Geq vb, Eq va))" |
  "apply_gt (Leq vb) (Eq va) = (if vb \<le> va then (Bc False, Bc False) else (And (Leq vb) (Gt va), Eq va))" |
  "apply_gt (Neq vb) (Lt va) = (Neq vb, Lt va)" |
  "apply_gt (Geq vb) (Lt va) = (Geq vb, Lt va)" |
  "apply_gt (Leq vb) (Lt va) = (if vb \<le> va then (Bc False, Bc False) else (And (Leq vb) (Geq va), Lt va))" |
  "apply_gt (Neq vb) (Gt va) = (if vb \<le> va then (Gt va, Gt va) else (And (Gt va) (Neq vb), Gt va))" |
  "apply_gt (Geq vb) (Gt va) = (if vb \<le> va then (Gt va, Gt va) else (Geq vb, Gt va))" |
  "apply_gt (Leq vb) (Gt va) = (if vb \<le> va then (Bc False, Bc False) else (And (Leq vb) (Gt va), And (Lt vb) (Gt va)))" |
  "apply_gt (Neq va) (Neq vb) = ((Neq va), (Neq vb))" |
  "apply_gt (Geq va) (Neq vb) = (Not (Lt va), Neq vb)" |
  "apply_gt (Leq va) (Neq vb) = (if vb \<ge> va then (Leq va, Lt va) else (Leq va, And (Lt va) (Neq vb)))" |
  "apply_gt (Neq va) (Geq vb) = (if va \<le> vb then (Gt vb, Geq vb) else (And (Gt vb) (Neq va), Geq vb))" |
  "apply_gt (Geq va) (Geq vb) = (if va \<le> vb then (Gt vb, Geq vb) else (Geq va, Geq vb))" |
  "apply_gt (Leq va) (Geq vb) = (if va \<le> vb then (Bc False, Bc False) else (And (Gt vb) (Leq va) , Geq vb))" |
  "apply_gt (Neq va) (Leq vb) = (Neq va, Leq vb)" |
  "apply_gt (Geq va) (Leq vb) = (Geq va, Leq vb)" |
  "apply_gt (Leq va) (Leq vb) = (if va \<le> vb then (Bc False, Bc False) else (Leq va, Leq vb))"

(*
If the second arg is always smaller than the first (e.g. if they're both literals with the first
being smaller) then just return that. If not, is there a way for the first arg to be smaller than the
second arg? If so, return it. If not, return false.
*)
(* fun apply_lt :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" *)

fun apply_guard :: "constraints \<Rightarrow> guard \<Rightarrow> constraints" where
  "apply_guard c (gexp.Lt (N n) (N n')) = (if n < n' then c else false)" |
  "apply_guard c (gexp.Not (gexp.Lt (N n) (N n'))) = (if n \<ge> n' then c else false)" |
  
"apply_guard c (gexp.Eq (N n) (N n')) = (if n = n' then c else false)" |
  "apply_guard c (gexp.Not (gexp.Eq (N n) (N n'))) = (if n \<noteq> n' then c else false)" |

  "apply_guard c (gexp.Eq (V v) (N n)) = update c v (Eq n)" |
  "apply_guard c (gexp.Not (gexp.Eq (V v) (N n))) = update c v (Neq n)" |

  "apply_guard c (gexp.Eq (N n) (V v)) = update c v (Eq n)" |
  "apply_guard c (gexp.Not (gexp.Eq (N n) (V v))) = update c v (Neq n)" |

  "apply_guard c (gexp.Eq (V vb) (V v)) = (let com = (compose_eq (c vb) (c v)) in (update (update c vb com) v com))" |
  "apply_guard c (gexp.Not (gexp.Eq (V vb) (V v))) = (case ((c vb), (c v)) of
    (Bc True, Bc True) \<Rightarrow> 
  )" |

  "apply_guard c (gexp.Eq (V vb) (Plus v va)) = update c vb (apply_plus c v va)" |
  "apply_guard c (gexp.Eq (Plus v va) (V vb)) = update c vb (apply_plus c v va)" |

  "apply_guard c (gexp.Gt (N n) (N n')) = (if n > n' then c else false)" |
  "apply_guard c (gexp.Gt (V vb) (N n)) = update c vb (Gt n)" |
  "apply_guard c (gexp.Gt (V vb) (V v)) = (case (apply_gt (c vb) (c v)) of
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (a, b) \<Rightarrow> update (update c vb a) v b
  )"|
  "apply_guard c (gexp.Gt (V vb) (Plus v vc)) = (case (apply_gt (c vb) (apply_plus c v vc)) of
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (a, _) \<Rightarrow> (update c vb a)
  )"|
  "apply_guard c (gexp.Gt (Plus v vc) (V vb)) = (case (apply_gt (apply_plus c v vc) (c vb)) of
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (a, _) \<Rightarrow> (update c vb a)
  )"|
  "apply_guard c (gexp.Gt (N n) (V vb)) = (case (apply_gt (Eq n) (c vb)) of
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (_, a) \<Rightarrow> (update c vb a)
  )" |
  "apply_guard c (gexp.Lt (V vb) (N n)) = (case (apply_gt (c vb) (Eq n)) of
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (a, _) \<Rightarrow> (update c vb a)
  )" |
  "apply_guard c (gexp.Lt (V v) (V vb)) = (case (apply_gt (c vb) (c v)) of
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (a, b) \<Rightarrow> update (update c vb a) v b
  )"|
  "apply_guard c (gexp.Lt (V vb) (Plus v vc)) = (case (apply_gt (apply_plus c v vc) (c vb)) of
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (_, a) \<Rightarrow> update c vb a
  )" |
  "apply_guard c (gexp.Lt (Plus v vc) (V vb)) = (case (apply_gt (c vb) (apply_plus c v vc)) of
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (a, _) \<Rightarrow> update c vb a
  )" |
  "apply_guard c (gexp.Lt (N va) (V vb)) = (case (apply_gt (c vb) (Eq va)) of 
    (Bc False, _) \<Rightarrow> false |
    (_, Bc False) \<Rightarrow> false |
    (a, _) \<Rightarrow> update c vb a
  )"|  
  (*Don't phrase your guard like this!*)
  "apply_guard a (gexp.Eq (Plus vb vc) (N v)) = false" |
  "apply_guard a (gexp.Eq (Plus vb vc) (Plus v vd)) = false" |
  "apply_guard a (gexp.Eq (N va) (Plus vb vc)) = false" |
  "apply_guard a (gexp.Gt (Plus vb vc) (N v)) = false" |
  "apply_guard a (gexp.Gt (Plus vb vc) (Plus v vd)) = false" |
  "apply_guard a (gexp.Gt (N va) (Plus vb vc)) = false" |
  "apply_guard a (gexp.Lt (Plus vb vc) (N v)) = false" |
  "apply_guard a (gexp.Lt (Plus vb vc) (Plus v vd)) = false" |
  "apply_guard a (gexp.Lt (N va) (Plus vb vc)) = false"


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