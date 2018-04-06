theory Constraints
imports CExp

begin

type_synonym constraints = "vname \<Rightarrow> cexp"

abbreviation empty :: constraints where
  "empty \<equiv> \<lambda>x. Bc True"

definition update :: "constraints \<Rightarrow> vname \<Rightarrow> cexp \<Rightarrow> constraints" where
  "update m k v = (\<lambda>x. if x=k then v else m x)"

definition constraints_equiv :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "constraints_equiv c c' = (\<forall>i. cexp_equiv (c i) (c' i))"

definition consistent :: "constraints \<Rightarrow> bool" where
  "consistent c = (\<forall>i. satisfiable (c i))"

fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_plus (Bc v) _ = Bc v" |
  "compose_plus _ (Bc v) = Bc v" |
  "compose_plus (Not (Bc v)) _ = Bc (\<not>v)" |
  "compose_plus _ (Not (Bc v)) = Bc (\<not>v)" |

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

termination apply_plus
  apply (relation "measure (\<lambda>(c, x, y). (size x) + (size y))")
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
  "apply_gt (Neq va) (Bc True) = (Neq va, Bc True)" |
  "apply_gt (Gt v) (Bc True) = (Gt v, Bc True)" |
  "apply_gt (Eq v) (Bc True)   = (Eq v, Lt v)" |
  "apply_gt (Lt v) (Bc True)   = (Lt v, Lt v)" |
  "apply_gt (Geq va) (Bc True) = (Geq va, Lt va)" |
  "apply_gt (Leq va) (Bc True) = (Leq va, Lt va)" |

  "apply_gt (Bc True) (Eq v) = (Gt v, Eq v)" |
  "apply_gt (Bc True) (Geq v) = (Gt v, Geq v)" |
  "apply_gt (Bc True) (Gt v) = (Gt v, Gt v)" |
  "apply_gt (Bc True) v = (Bc True, v)" |

  "apply_gt (Lt v) (Gt va) = (And (Lt v)  (Gt va), And (Gt va) (Lt v))" |
  "apply_gt v (Leq vb) = (And v (Gt vb), Leq vb)" |
  "apply_gt v (Gt va) =  (And v (Gt va), Gt va)" |
  "apply_gt v (Lt va) = (And v (Geq va), Lt va)" |
  "apply_gt (Lt v)  (Neq vb) = (Lt v,  And (Neq vb) (Lt v))" |
  "apply_gt (Leq v) (Neq vb) = (Leq v, And (Neq vb) (Lt v))" |
  
  "apply_gt (Eq v) va = (Eq v, And va (Lt v))" |
  "apply_gt v (Eq va) = (And v (Gt va), Eq va)" |

  "apply_gt (Lt v) (Geq va) = (And (Lt v) (Gt va), And (Geq va) (Lt v))" |
  "apply_gt v      (Geq vb) = (And v  (Gt vb), Geq vb)" |

  "apply_gt va vb = (va, vb)"

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

fun apply_guard :: "constraints \<Rightarrow> guard \<Rightarrow> constraints" where
  "apply_guard a (gexp.Not (gexp.Not va)) = apply_guard a va" |
  "apply_guard a (gexp.And va vb) = apply_guard (apply_guard a va) vb"|
  "apply_guard a (gexp.Not (gexp.And va vb)) = (\<lambda>x. Or ((apply_guard a (gexp.Not va)) x) ((apply_guard a (gexp.Not vb)) x))" |
 
  "apply_guard a (gexp.Eq vb (N v)) = update a vb (And (a vb) (Eq v))" |
  "apply_guard a (gexp.Eq vb (V v)) = update a vb (And  (a vb) (a v))" |
  "apply_guard a (gexp.Eq vb (Plus v va)) = update a vb (And (a vb) (apply_plus a v va))" |
 
  "apply_guard a (gexp.Gt vb (N n)) = update a vb (And (a vb) (Gt n))" |
  "apply_guard a (gexp.Gt vb (V v)) = (let (cvb, cv) = (apply_gt (a vb) (a v)) in (update (update a vb cvb) v cv))"|
  "apply_guard a (gexp.Gt vb (Plus v vc)) = (let (cvb, _) = (apply_gt (a vb) (apply_plus a v vc)) in (update a vb cvb))" |
 
  "apply_guard a (gexp.Lt vb (N n)) = update a vb (And (a vb) (Lt n))" |
  "apply_guard a (gexp.Lt vb (V v)) = (let (cvb, cv) = (apply_lt (a vb) (a v)) in (update (update a vb cvb) v cv))"|
  "apply_guard a (gexp.Lt vb (Plus v vc)) = (let (cvb, _) = (apply_lt (a vb) (apply_plus a v vc)) in (update a vb cvb))" |

  "apply_guard a (Ge vb (N n)) = update a vb (And (a vb) (Geq n))" |
  "apply_guard a (Ge vb (V v)) = (let (cvb, cv) = (apply_geq (a vb) (a v)) in (update (update a vb cvb) v cv))" |
  "apply_guard a (Ge vb (Plus v vc)) = (let (cvb, _) = (apply_geq (a vb) (apply_plus a v vc)) in (update a vb cvb))" |
  
  "apply_guard a (Le vb (N n)) = update a vb (And (a vb) (Leq n))" |
  "apply_guard a (Le vb (V v)) = (let (cvb, cv) = (apply_leq (a vb) (a v)) in (update (update a vb cvb) v cv))" |
  "apply_guard a (Le vb (Plus v vc)) = (let (cvb, _) = (apply_leq (a vb) (apply_plus a v vc)) in (update a vb cvb))" |

  "apply_guard a (Ne vb (N v)) = update a vb (And (a vb) (Neq v))" |
  "apply_guard a (Ne vb (V v)) = update a vb (Not (And  (a vb) (a v)))" |
  "apply_guard a (Ne vb (Plus va vc)) = update a vb (Not (And (a vb) (apply_plus a va vc)))"

fun apply_update :: "constraints \<Rightarrow> update_function \<Rightarrow> constraints" where
  "apply_update c (v, (N n)) = update c v (Eq n)" |
  "apply_update c (v, V vb) = update c v (c vb)" |
  "apply_update c (v, Plus vb vc) = update c v (apply_plus c vb vc)"

primrec apply_guards :: "constraints \<Rightarrow> guard list \<Rightarrow> constraints" where
  "apply_guards c [] = c" |
  "apply_guards c (h#t) = (apply_guards (apply_guard c h) t)"

primrec apply_updates :: "constraints \<Rightarrow> update_function list \<Rightarrow> constraints" where
  "apply_updates c [] = c" |
  "apply_updates c (h#t) = apply_updates (apply_update c h) t"

definition posterior :: "constraints \<Rightarrow> transition \<Rightarrow> constraints" where
  "posterior c t = (let c' = (apply_guards c (Guard t)) in (if consistent c' then (apply_updates c' (Updates t)) else (\<lambda>i. Bc False)))"

lemma "apply_guards empty [] = empty"
  by simp

lemma "constraints_equiv (apply_guards empty [(gexp.Eq ''i1'' (N 0))]) (\<lambda>x. if x = ''i1'' then Eq 0 else Bc True)"
  by (simp add: constraints_equiv_def update_def cexp_equiv_def)

definition notempty :: "constraints \<Rightarrow> bool" where
  "notempty c = (\<not> (\<forall>i. (c i) = Bc True))"

end