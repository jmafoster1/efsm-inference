theory Constraints
imports CExp

begin

type_synonym constraints = "vname \<Rightarrow> cexp"

abbreviation
  empty :: constraints where
  "empty \<equiv> \<lambda>x. Bc True"

definition update :: "constraints \<Rightarrow> vname \<Rightarrow> cexp \<Rightarrow> constraints" where
  "update m k v = (\<lambda>x. if x=k then v else m x)"

fun apply_eq :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "apply_eq v va = And v va"
  (*"apply_eq (Bc False) _ = (Bc False)" |
  "apply_eq _ (Bc False) = (Bc False)" |
  "apply_eq (Not (Bc True)) _ = (Bc False)" |
  "apply_eq _ (Not (Bc True)) = (Bc False)" |
  "apply_eq (Bc True) a = a" |
  "apply_eq a (Bc True) = a" |
  "apply_eq (Not (Bc False)) a = a" |
  "apply_eq a (Not (Bc False)) = a" |
  "apply_eq a (Not (Not vb)) = apply_eq a vb" |
  "apply_eq (Not (Not vb)) a = apply_eq vb a" |
  "apply_eq a (And vb vc) = And (apply_eq a vb) (apply_eq a vc)" |
  "apply_eq (And vb vc) a = And (apply_eq vb a) (apply_eq vc a)" |
  "apply_eq (Not (And vb vc)) a = Not (And (apply_eq vb a) (apply_eq vc a))" |
  "apply_eq a (Not (And vb vc)) = Not (And (apply_eq a vb) (apply_eq a vc))" |

  "apply_eq (Eq v) (Eq va) = (if v = va then Eq v else Bc False)" |
  "apply_eq (Eq v) (Lt va) = (if v < va then Eq v else Bc False)" |
  "apply_eq (Eq v) (Gt va) = (if v > va then Eq v else Bc False)" |
  "apply_eq (Eq v) (Neq va) = (if v \<noteq> va then Eq v else Bc False)" |
  "apply_eq (Eq v) (Geq va) = (if v \<ge> va then Eq v else Bc False)" |
  "apply_eq (Eq v) (Leq va) = (if v \<le> va then Eq v else Bc False)" |

  "apply_eq (Lt va) (Eq v) = (if v < va then Eq v else Bc False)" |
  "apply_eq (Lt v) (Lt va) = (if v < va then Lt v else Lt va)" |
  "apply_eq (Lt v) (Gt va) = (if va < v then And (Lt v) (Gt va) else Bc False)" |
  "apply_eq (Lt v) (Neq vb) = (if vb \<ge> v then Lt v else Bc False)" |
  "apply_eq (Lt v) (Geq vb) = (if vb < v then And (Lt v) (Geq vb) else Bc False)" |
  "apply_eq (Lt v) (Leq vb) = (if v < vb then Lt v else Lt vb)" |

  "apply_eq (Gt va) (Eq v) = (if v > va then Eq v else Bc False)" |
  "apply_eq (Gt va) (Lt v) = (if va < v then And (Lt v) (Gt va) else Bc False)" |
  "apply_eq (Gt v) (Gt va) = (if v > va then Gt v else Gt va)" |
  "apply_eq (Gt v) (Neq vb) = (if vb \<le> v then Gt v else And (Gt v) (Neq vb))" |
  "apply_eq (Gt v) (Geq vb) = (if v > vb then Gt v else Not (Lt vb))" |
  "apply_eq (Gt v) (Leq vb) = (if vb > v then And (Gt v) (Leq vb) else Bc False)" |

  "apply_eq (Neq va) (Eq v) = (if v = va then Bc False else Eq v)" |
  "apply_eq (Neq vb) (Neq v) = (if v = vb then Neq v else And (Neq v) (Neq vb))" |
  "apply_eq (Neq vb) (Geq v) = (if vb < v then Geq v else (if v = vb then Gt v else And (Neq vb) (Geq v)))" |
  "apply_eq (Neq vb) (Leq v) = (if vb > v then Leq v else (if v = vb then Lt v else And (Neq vb) (Leq v)))" |
  "apply_eq (Neq vb) (Lt v) = (if vb \<ge> v then Lt v else Bc False)" |
  "apply_eq (Neq vb) (Gt v) = (if vb \<le> v then Gt v else And (Gt v) (Neq vb))" |

  "apply_eq (Geq va) (Eq v) = (if v \<ge> va then Eq v else Bc False)" |
  "apply_eq (Geq vb) (Lt v) = (if vb < v then And (Lt v) (Geq vb) else Bc False)" |
  "apply_eq (Geq vb) (Gt v) = (if v > vb then Gt v else Not (Lt vb))" |
  "apply_eq (Geq vb) (Neq v) = (if v < vb then Geq v else (if v = vb then Gt vb else And (Geq vb) (Neq v)))"|
  "apply_eq (Geq vb) (Geq v) = (if vb > v then Geq vb else Geq v)" |
  "apply_eq (Geq vb) (Leq v) = (if v > vb then And (Geq vb) (Leq v) else Bc False)" |

  "apply_eq (Leq vb) (Lt v) = (if v < vb then Lt v else Lt vb)" |
  "apply_eq (Leq va) (Eq v) = (if v \<le> va then Eq v else Bc False)" |
  "apply_eq (Leq vb) (Gt v) = (if vb > v then And (Gt v) (Leq vb) else Bc False)" |
  "apply_eq (Leq vb) (Neq v) = (if v > vb then Leq vb else (if v = vb then Lt vb else And (Leq vb) (Neq v)))"|
  "apply_eq (Leq vb) (Geq v) = (if v < vb then And (Leq vb) (Geq v) else Bc False)"|
  "apply_eq (Leq vb) (Leq v) = (if v > vb then Leq vb else Leq v)"*)

(* lemma commutative_apply_eq: "\<forall> x y. apply_eq x y = apply_eq y x" *)


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
  "compose_plus (Eq v) (Geq va) = Geq (v+va)" |
  "compose_plus (Eq v) (Leq va) = Leq (v+va)" |
  "compose_plus (Lt v) (Eq va) = Lt (v+va)" |
  "compose_plus (Lt v) (Lt va) = Lt (v+va)" |
  "compose_plus (Lt v) (Gt va) = Bc True" |
  "compose_plus (Lt v) (Geq vb) = Bc True" |
  "compose_plus (Lt v) (Leq vb) = Lt (v+vb)" |
  "compose_plus (Gt v) (Eq va) = Gt (v+va)" |
  "compose_plus (Gt v) (Lt va) = Bc True" |
  "compose_plus (Gt v) (Gt va) = Gt (v+va)" |
  "compose_plus (Gt v) (Geq vb) = Gt (v+vb)" |
  "compose_plus (Gt v) (Leq vb) = Bc True" |
  "compose_plus (Geq vb) (Eq va) = Geq (vb+va)" |
  "compose_plus (Leq vb) (Eq va) = Leq (vb+va)" |
  "compose_plus (Geq vb) (Lt va) = Bc True" |
  "compose_plus (Leq vb) (Lt va) = Lt (vb+va)" |
  "compose_plus (Geq vb) (Gt va) = Gt (va+vb)" |
  "compose_plus (Leq vb) (Gt va) = Bc True" |
  "compose_plus (Geq vb) (Geq v) = Geq (v+vb)" |
  "compose_plus (Geq vb) (Leq v) = Bc True" |
  "compose_plus (Leq vb) (Geq v) = Bc True" |
  "compose_plus (Leq vb) (Leq v) = Leq (v+vb)"

function apply_plus :: "constraints \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> cexp" where
  "apply_plus _ (N n) (N n') = Eq (n+n')" |
  "apply_plus c (V v) (N n) = compose_plus (c v) (Eq n)" |
  "apply_plus c (N n) (V v) = compose_plus (c v) (Eq n)" |
  "apply_plus c (V v) (V va) = compose_plus (c v) (c va)" |
  "apply_plus c (N n) (Plus va vb) = compose_plus (Eq n) (apply_plus c va vb)" |
  "apply_plus c (V v) (Plus va vb) = compose_plus (c v) (apply_plus c va vb)" |
  "apply_plus c (Plus v va) (N vb) = compose_plus (apply_plus c v va) (Eq vb)" |
  "apply_plus c (Plus v va) (V vb) = compose_plus (apply_plus c v va) (c vb)" |
  "apply_plus c (Plus vb vc) (Plus v va) = compose_plus (apply_plus c vb vc) (apply_plus c v va)"
    apply pat_completeness
    by simp_all
  

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
  "apply_gt (Bc True) (Gt v) = (Gt v, Gt v)" |
  "apply_gt (Bc True) (Neq v) = (Bc True, Neq v)" |
  "apply_gt (Bc True) (Geq v) = (Gt v, Geq v)" |
  "apply_gt (Bc True) (Leq v) = (Bc True, Leq v)" |
  "apply_gt (Eq v) (Bc True) = (Eq v, Lt v)" |
  "apply_gt (Eq v) (Eq va) = (if v > va then (Eq v, Eq va) else (Bc False, Bc False))" |
  "apply_gt (Eq v) (Lt va) = (if v > va then (Eq v, Lt va) else (Eq v, Lt v))" |
  "apply_gt (Eq v) (Gt va) = (if v > va then (Eq v, And (Gt va) (Lt v)) else (Bc False, Bc False))" |
  "apply_gt (Eq v) (Neq va) = (if va \<le> v then (Eq v, Lt v) else (Eq v, And (Lt v) (Neq va)))" |
  "apply_gt (Eq v) (Geq va) = (if v \<le> va then (Bc False, Bc False) else (Eq v, And (Geq va) (Lt v)))" |
  "apply_gt (Eq v) (Leq va) = (if va < v then (Eq v, (Leq va)) else (Eq v, Lt v))" |
  "apply_gt (Lt v) (Bc True) = (Lt v, Lt v)" |
  "apply_gt (Lt v) (Eq va) = (if v \<le> va then (Bc False, Bc False) else (And (Lt v) (Gt va), Eq va))" |
  "apply_gt (Lt v) (Lt va) = (if v \<le> va then (Bc False, Bc False) else (Lt v, Lt va))" |
  "apply_gt (Lt v) (Gt va) = (if v \<le> va then (Bc False, Bc False) else (And (Lt v) (Gt va), And (Gt va) (Lt v)))" |
  "apply_gt (Lt v) (Neq vb) = (if vb \<ge> v then (Lt v, Lt v) else (Lt v, And (Lt v) (Neq vb)))" |
  "apply_gt (Lt v) (Geq va) = (if v \<le> va then (Bc False, Bc False) else (And (Lt v) (Gt va), And (Lt v) (Geq va)))" |
  "apply_gt (Lt v) (Leq va) = (if v \<le> va then (Bc False, Bc False) else (Lt v, Leq va))" |
  "apply_gt (Gt v) (Bc True) = (Gt v, Bc True)" |
  "apply_gt (Gt v) (Eq va) = (if v > va then (Gt v, Eq va) else (Gt va, Eq va))" |
  "apply_gt (Gt v) (Lt va) = (Gt v, Lt va)" |
  "apply_gt (Gt v) (Gt va) = (if va \<ge> v then (Gt va, Gt va) else (Gt v, Gt va))" |
  "apply_gt (Gt v) (Neq vb) = (if vb > v then (Gt v, Leq v) else (Gt v, And (Leq v) (Neq vb)))" |
  "apply_gt (Gt v) (Geq va) = (if va \<ge> v then (Gt va, Not (Lt va)) else (Gt v, Not (Lt va)))" |
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

fun apply_geq :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_geq (Bc False) v = (Bc False, v)" |
  "apply_geq v (Bc False) = (v, Bc False)" |
  "apply_geq v (Not (Bc True)) = (v, Bc False)" |
  "apply_geq (Not (Bc True)) v = (Bc False, v)" |
  "apply_geq v (Not (Bc False)) = apply_geq v (Bc True)" |
  "apply_geq (Not (Bc False)) v = apply_geq (Bc True) v" |
  "apply_geq v (Not (Not vb)) = apply_geq v vb" |
  "apply_geq (Not (Not vb)) v = apply_geq vb v" |

  "apply_geq v (And va vb) = (And (fst (apply_geq v va)) (fst (apply_geq v vb)), And (snd (apply_geq v va)) (snd (apply_geq v vb)))" |
  "apply_geq (And va vb) v = (And (fst (apply_geq va v)) (fst (apply_geq vb v)), And (snd (apply_geq va v)) (snd (apply_geq vb v)))" |
  "apply_geq v (Not (And va vb)) = (Not (And (fst (apply_geq v va)) (fst (apply_geq v vb))), Not (And (snd (apply_geq v va)) (snd (apply_geq v vb))))" |
  "apply_geq (Not (And va vb)) v = (Not (And (fst (apply_geq va v)) (fst (apply_geq vb v))), Not (And (snd (apply_geq va v)) (snd (apply_geq vb v))))" |
  
  "apply_geq (Bc True) (Bc True) = (Bc True, Bc True)" |
  "apply_geq (Bc True) (Lt v) = (Bc True, Lt v)" |
  "apply_geq (Bc True) (Gt v) = (Gt v, Gt v)" |
  "apply_geq (Bc True) (Neq v) = (Bc True, Neq v)" |
  "apply_geq (Bc True) (Geq v) = (Geq v, Geq v)" |
  "apply_geq (Bc True) (Leq v) = (Bc True, Leq v)" |

  "apply_geq (Eq v) va = (Eq v, And va (Leq v))" |

  "apply_geq (Lt v) a = (Lt v, And a (Leq v))" |
  
  "apply_geq (Gt v) (Bc True) = (Gt v, Bc True)" |
  "apply_geq (Gt v) (Eq va) = (And (Gt v) (Geq va), Eq va)" |
  "apply_geq (Gt v) (Lt va) = (Gt v, Lt va)" |
  "apply_geq (Gt v) (Gt va) = (And (Gt v) (Gt va), Gt va)" |
  "apply_geq (Gt v) (Neq vb) = (Gt v, Neq vb)" |
  "apply_geq (Gt v) (Geq va) = (And (Gt v) (Geq va), (Geq va))" |
  "apply_geq (Gt v) (Leq va) = (Gt v, Leq va)" |

  "apply_geq (Neq va) (Bc True) = (Neq va, Bc True)" |
  "apply_geq (Geq va) (Bc True) = (Geq va, Bc True)" |
  "apply_geq (Leq va) (Bc True) = (Leq va, Leq va)" |
  "apply_geq v (Eq va) = (And v (Geq va), Eq va)" |

  "apply_geq (Neq vb) (Lt va) = (Neq vb, Lt va)" |
  "apply_geq (Geq vb) (Lt va) = (Geq vb, Lt va)" |
  "apply_geq (Leq vb) (Lt va) = (And (Leq vb) (Geq va), Lt va)" |
  "apply_geq (Neq vb) (Gt va) = (And (Neq vb) (Gt va), Gt va)" |
  "apply_geq (Geq vb) (Gt va) = (And (Geq vb) (Gt va), Gt va)" |
  "apply_geq (Leq vb) (Gt va) = (And (Leq vb) (Gt va), Gt va)" |
  "apply_geq (Neq va) (Neq vb) = (Neq va, Neq vb)" |
  "apply_geq (Geq va) (Neq vb) = (Geq va, Neq vb)" |
  "apply_geq (Leq va) (Neq vb) = (Leq va, And (Neq vb) (Leq va))" |
  "apply_geq (Neq va) (Geq vb) = (And (Neq va) (Geq vb), Geq vb)" |
  "apply_geq (Geq va) (Geq vb) = (And (Geq va) (Geq vb), Geq vb)" |
  "apply_geq (Leq va) (Geq vb) = (And (Leq va) (Geq vb), Geq vb)" |
  "apply_geq (Neq va) (Leq vb) = (Neq va, Leq vb)" |
  "apply_geq (Geq va) (Leq vb) = (Geq va, Leq vb)" |
  "apply_geq (Leq va) (Leq vb) = (And (Leq va) (Geq vb), Leq vb)"

definition apply_leq :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_leq a b = (let (ca, cb) = (apply_geq b a) in (cb, ca))"

definition apply_lt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_lt a b = (let (ca, cb) = (apply_gt b a) in (cb, ca))"

fun csimp :: "cexp \<Rightarrow> cexp" where
  "csimp (Bc a) = Bc a" |
  "csimp (Eq n) = Eq n" |
  "csimp (Lt n) = Lt n" |
  "csimp (Gt n) = Gt n" |
  "csimp (Not (Bc True)) = Bc False" |
  "csimp (Not (Bc False)) = Bc True" |
  "csimp (Neq n) = Neq n" |
  "csimp (Geq n) = Geq n" |
  "csimp (Leq n) = Leq n" |
  "csimp (Not (Not v)) = v" |
  "csimp (And v (Bc True)) = v" |
  "csimp (And (Bc True) v) = v" |

  (* Catch all so it terminates properly *)
  "csimp (Not (And v va)) = Not (csimp (And v va))" |
  "csimp (And v va) = And (csimp v) (csimp va)"

fun apply_guard :: "constraints \<Rightarrow> guard \<Rightarrow> constraints option" where
  "apply_guard a (gexp.Not (gexp.Not va)) = apply_guard a va" |
  "apply_guard a (gexp.And va vb) = (case apply_guard a va of
    None \<Rightarrow> None |
    Some x \<Rightarrow> (case apply_guard x vb of
      None \<Rightarrow> None |
      Some y \<Rightarrow> Some y
    )
  ) "|
  "apply_guard a (gexp.Not (gexp.And va vb)) = (case ((apply_guard a (gexp.Not va)), (apply_guard a (gexp.Not vb))) of
    (None, None) \<Rightarrow> None |
    (None, Some a) \<Rightarrow> Some a |
    (Some a, None) \<Rightarrow> Some a |
    (Some a, Some b) \<Rightarrow> Some (\<lambda>x. csimp (Or (a x) (b x)))
  )" |
  "apply_guard a (gexp.Eq (N vb) (N v)) = (if vb = v then Some a else None)" |
  "apply_guard a (gexp.Eq (V vb) (N v)) = (case csimp (And (a vb) (Eq v)) of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  )" |
  "apply_guard a (gexp.Eq (V vb) (V v)) = (case csimp (And  (a vb) (a v)) of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update (update a vb s) v s)
  )" |
  "apply_guard a (gexp.Eq (V vb) (Plus v va)) = (case csimp (And (a vb) (apply_plus a v va)) of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  )" |
  "apply_guard a (gexp.Eq (Plus vb vc) (V v)) = (case csimp (And (a v) (apply_plus a vb vc)) of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a v s)
  )" |
  "apply_guard a (gexp.Eq (N v) (V vb)) = (case csimp (And (a vb) (Eq v)) of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  )" |
  "apply_guard a (gexp.Gt (N n) (N n')) = (if n > n' then Some a else None)" |
  "apply_guard a (gexp.Gt (V vb) (N n)) = (let (cvb, _) = (apply_gt (a vb) (Eq n)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (gexp.Gt (V vb) (V v)) = (let (cvb, cv) = (apply_gt (a vb) (a v)) in (case (csimp cvb, csimp cv) of
    (Bc False, _) \<Rightarrow> None |
    (_, Bc False) \<Rightarrow> None |
    (svb, sv) \<Rightarrow> Some (update (update a vb svb) v sv)
  ))" |
  "apply_guard a (gexp.Gt (V vb) (Plus v vc)) = (let (cvb, _) = (apply_gt (a vb) (apply_plus a v vc)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (gexp.Gt (Plus v vc) (V vb)) = (let (_, cvb) = (apply_gt (apply_plus a v vc) (a vb)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (gexp.Gt (N n) (V vb)) = (let (_, cvb) = (apply_gt (Eq n) (a vb)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (gexp.Lt (N n) (N n')) = (if n < n' then Some a else None)" |
  "apply_guard a (gexp.Lt (V vb) (N n)) = (let (cvb, _) = (apply_lt (a vb) (Eq n)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (gexp.Lt (V vb) (V v)) = (let (cvb, cv) = (apply_lt (a vb) (a v)) in (case (csimp cvb, csimp cv) of
    (Bc False, _) \<Rightarrow> None |
    (_, Bc False) \<Rightarrow> None |
    (svb, sv) \<Rightarrow> Some (update (update a vb svb) v sv)
  ))" |
  "apply_guard a (gexp.Lt (V vb) (Plus v vc)) = (let (cvb, _) = (apply_lt (a vb) (apply_plus a v vc)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (gexp.Lt (Plus v vc) (V vb)) = (let (_, cvb) = (apply_lt (apply_plus a v vc) (a vb)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (gexp.Lt (N n) (V vb)) = (let (_, cvb) = (apply_lt (Eq n) (a vb)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |

  "apply_guard a (Ge (N n) (N n')) = (if n \<ge> n' then Some a else None)" |
  "apply_guard a (Ge (V vb) (N n)) = (let (cvb, _) = (apply_geq (a vb) (Eq n)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (Ge (V vb) (V v)) = (let (cvb, cv) = (apply_geq (a vb) (a v)) in (case (csimp cvb, csimp cv) of
    (Bc False, _) \<Rightarrow> None |
    (_, Bc False) \<Rightarrow> None |
    (svb, sv) \<Rightarrow> Some (update (update a vb svb) v sv)
  ))" |
  "apply_guard a (Ge (V vb) (Plus v vc)) = (let (cvb, _) = (apply_geq (a vb) (apply_plus a v vc)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (Ge (Plus v vc) (V vb)) = (let (_, cvb) = (apply_geq (apply_plus a v vc) (a vb)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (Ge (N n) (V vb)) = (let (_, cvb) = (apply_geq (Eq n) (a vb)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (Le (N n) (N n')) = (if n \<le> n' then Some a else None)" |
  "apply_guard a (Le (V vb) (N n)) = (let (cvb, _) = (apply_leq (a vb) (Eq n)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (Le (V vb) (V v)) = (let (cvb, cv) = (apply_leq (a vb) (a v)) in (case (csimp cvb, csimp cv) of
    (Bc False, _) \<Rightarrow> None |
    (_, Bc False) \<Rightarrow> None |
    (svb, sv) \<Rightarrow> Some (update (update a vb svb) v sv)
  ))" |
  "apply_guard a (Le (V vb) (Plus v vc)) = (let (cvb, _) = (apply_leq (a vb) (apply_plus a v vc)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (Le (Plus v vc) (V vb)) = (let (_, cvb) = (apply_leq (apply_plus a v vc) (a vb)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (Le (N n) (V vb)) = (let (_, cvb) = (apply_leq (Eq n) (a vb)) in (case csimp cvb of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a vb s)
  ))" |
  "apply_guard a (Ne (N n) (N n')) = (if n = n' then None else Some a)" |
  "apply_guard a (Ne (V v) (N n)) = (case csimp (And (a v) (Neq n)) of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a v s)
  )" |
  "apply_guard a (Ne (V v) (V va)) = (case (csimp (a v), csimp (a va)) of
    (Bc False, _) \<Rightarrow> None |
    (_, Bc False) \<Rightarrow> None |
    (Eq n, Eq n') \<Rightarrow> (if n = n' then None else Some a) |
    (Eq n, s) \<Rightarrow> Some (update a va (And s (Neq n))) |
    (s, Eq n) \<Rightarrow> Some (update a v (And s (Neq n))) |
    (_, _) \<Rightarrow> Some a
  )" |
  "apply_guard a (Ne (V v) (Plus va vc)) = (case csimp (apply_plus a va vc) of
    Bc False \<Rightarrow> None |
    Eq n \<Rightarrow> Some (update a v (Neq n)) |
    _ \<Rightarrow> Some a
  )" |
  "apply_guard a (Ne (Plus va vc) (V v)) = (case csimp (apply_plus a va vc) of
    Bc False \<Rightarrow> None |
    Eq n \<Rightarrow> Some (update a v (Neq n)) |
    _ \<Rightarrow> Some a
  )" |
  "apply_guard a (Ne (N vb) (V v)) = (case csimp (And (a v) (Neq vb)) of
    Bc False \<Rightarrow> None |
    s \<Rightarrow> Some (update a v s)
  )" |

  (* Don't phrase your guard like this *)
  "apply_guard a (Ge (N v) (Plus vc vd)) = None" |
  "apply_guard a (Ge (Plus vc vd) (Plus v va)) = None" |
  "apply_guard a (Ge (Plus vc vd) (N v)) = None" |
  "apply_guard a (Le (N vb) (Plus v vc)) = None" |
  "apply_guard a (Le (Plus v vc) (Plus va vd)) = None" |
  "apply_guard a (Le (Plus v vc) (N va)) = None" |
  "apply_guard a (Ne (N vb) (Plus v vc)) = None" |
  "apply_guard a (Ne (Plus v vc) (Plus va vd)) = None" |
  "apply_guard a (Ne (Plus v vc) (N va)) = None" |
  "apply_guard a (gexp.Lt (N va) (Plus vb vc)) = None" |
  "apply_guard a (gexp.Lt (Plus vb vc) (Plus v vd)) = None" |
  "apply_guard a (gexp.Lt (Plus vb vc) (N v)) = None" |
  "apply_guard a (gexp.Gt (N va) (Plus vb vc)) = None" |
  "apply_guard a (gexp.Gt (Plus vb vc) (N v)) = None" |
  "apply_guard a (gexp.Gt (Plus vb vc) (Plus v vd)) = None" |
  "apply_guard a (gexp.Eq (N va) (Plus vb vc)) = None" |
  "apply_guard a (gexp.Eq (Plus vb vc) (N v)) = None" |
  "apply_guard a (gexp.Eq (Plus vb vc) (Plus v vd)) = None"


fun apply_update :: "constraints \<Rightarrow> update_function \<Rightarrow> constraints" where
  "apply_update c (v, (N n)) = update c v (Eq n)" |
  "apply_update c (v, V vb) = update c v (csimp (c vb))" |
  "apply_update c (v, Plus vb vc) = update c v (csimp (apply_plus c vb vc))"

primrec apply_guards :: "constraints \<Rightarrow> guard list \<Rightarrow> constraints option" where
  "apply_guards c [] = Some c" |
  "apply_guards c (h#t) = (let h' = (apply_guard c h) in
    (case h' of
      None \<Rightarrow> None |
      Some a \<Rightarrow> (apply_guards a t)
    )
  )"

primrec apply_updates :: "constraints \<Rightarrow> update_function list \<Rightarrow> constraints" where
  "apply_updates c [] = c" |
  "apply_updates c (h#t) = apply_updates (apply_update c h) t"

definition anterior :: "constraints \<Rightarrow> transition \<Rightarrow> constraints option" where
  "anterior c t = (case (apply_guards c (Guard t)) of 
    None \<Rightarrow> None |
    Some a \<Rightarrow> Some (apply_updates a (Updates t))
  )"

lemma "apply_guards empty [] = Some empty"
  by simp

lemma "apply_guards empty [(gexp.Eq (V ''i1'') (N 0))] = Some (\<lambda>x. if x = ''i1'' then Eq 0 else Bc True)"
  apply simp
  by (simp add: update_def)
end