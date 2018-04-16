theory Constraints
imports CExp

begin

type_synonym constraints = "vname \<Rightarrow> cexp"

abbreviation empty :: constraints where
  "empty \<equiv> \<lambda>x. Bc True"

definition update :: "constraints \<Rightarrow> vname \<Rightarrow> cexp \<Rightarrow> constraints" where
  "update c k v = (\<lambda>r. if r=k then v else c r)"

definition constraints_equiv :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "constraints_equiv c c' = (\<forall>r. cexp_equiv (c r) (c' r))"

definition consistent :: "constraints \<Rightarrow> bool" where
  "consistent c = (\<forall>r. satisfiable (c r))"

definition nonempty :: "constraints \<Rightarrow> bool" where
  "nonempty c = (\<not> (\<forall>r. cexp_equiv (c r) (Bc True)))"

definition constraints_simulates :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "constraints_simulates c c' = (\<forall>r. cexp_simulates (c r) (c' r))"

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

  "compose_plus (Eq v)   (Eq va)  = Eq (v+va)" |
  "compose_plus (Eq v)   (Lt va)  = Lt (v+va)" |
  "compose_plus (Eq v)   (Gt va)  = Gt (v+va)" |
  "compose_plus (Eq v)   (Geq va) = Geq (v+va)" |
  "compose_plus (Eq v)   (Leq va) = Leq (v+va)" |
  
  "compose_plus (Lt v)   (Eq va)  = Lt (v+va)" |
  "compose_plus (Gt v)   (Eq va)  = Gt (v+va)" |
  "compose_plus (Geq vb) (Eq va)  = Geq (vb+va)" |
  "compose_plus (Leq vb) (Eq va)  = Leq (vb+va)" |

  "compose_plus (Lt v)   (Lt va)  = Lt (v+va)" |
  "compose_plus (Lt v)   (Leq vb) = Lt (v+vb)" |
  "compose_plus (Leq vb) (Lt va)  = Lt (vb+va)" |
  "compose_plus (Leq vb) (Leq v)  = Leq (v+vb)" |
  
  "compose_plus (Gt v)   (Gt va)  = Gt (v+va)" |
  "compose_plus (Gt v)   (Geq vb) = Gt (v+vb)" |
  "compose_plus (Geq vb) (Gt va)  = Gt (va+vb)" |
  "compose_plus (Geq vb) (Geq v)  = Geq (v+vb)" |

  "compose_plus _ _ = Bc True" 

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

  "apply_gt v (And va vb) = (and (fst (apply_gt v va)) (fst (apply_gt v vb)), and (snd (apply_gt v va)) (snd (apply_gt v vb)))" |
  "apply_gt (And va vb) v = (and (fst (apply_gt va v)) (fst (apply_gt vb v)), and (snd (apply_gt va v)) (snd (apply_gt vb v)))" |
  "apply_gt v (Not (And va vb)) = (Not (And (fst (apply_gt v va)) (fst (apply_gt v vb))), Not (And (snd (apply_gt v va)) (snd (apply_gt v vb))))" |
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

  "apply_gt va vb = (va, vb)"

fun apply_geq :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_geq a b = (let (ca, cb) = (apply_gt a b) in (Or ca b, Or cb a))"

definition apply_leq :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_leq a b = (let (ca, cb) = (apply_geq b a) in (cb, ca))"

definition apply_lt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_lt a b = (let (ca, cb) = (apply_gt b a) in (cb, ca))"

fun apply_guard :: "constraints \<Rightarrow> guard \<Rightarrow> constraints" where
  "apply_guard a (gexp.Not (gexp.Not va)) = apply_guard a va" |
  "apply_guard a (gexp.And va vb) = apply_guard (apply_guard a va) vb"|
  "apply_guard a (gexp.Not (gexp.And va vb)) = (\<lambda>x. Or ((apply_guard a (gexp.Not va)) x) ((apply_guard a (gexp.Not vb)) x))" |
 
  "apply_guard a (gexp.Eq vb (N v)) = update a vb (and (a vb) (Eq v))" |
  "apply_guard a (gexp.Eq vb (V v)) = (let eq = (and (a vb) (a v)) in update (update a vb eq) v eq)" |
  "apply_guard a (gexp.Eq vb (Plus v va)) = update a vb (and (a vb) (apply_plus a v va))" |
 
  "apply_guard a (gexp.Gt vb (N n)) = update a vb (and (a vb) (Gt n))" |
  "apply_guard a (gexp.Gt vb (V v)) = (let (cvb, cv) = (apply_gt (a vb) (a v)) in (update (update a vb cvb) v cv))"|
  "apply_guard a (gexp.Gt vb (Plus v vc)) = (let (cvb, _) = (apply_gt (a vb) (apply_plus a v vc)) in (update a vb cvb))" |
 
  "apply_guard a (gexp.Lt vb (N n)) = update a vb (and (a vb) (Lt n))" |
  "apply_guard a (gexp.Lt vb (V v)) = (let (cvb, cv) = (apply_lt (a vb) (a v)) in (update (update a vb cvb) v cv))"|
  "apply_guard a (gexp.Lt vb (Plus v vc)) = (let (cvb, _) = (apply_lt (a vb) (apply_plus a v vc)) in (update a vb cvb))" |

  "apply_guard a (Ge vb (N n)) = update a vb (and (a vb) (Geq n))" |
  "apply_guard a (Ge vb (V v)) = (let (cvb, cv) = (apply_geq (a vb) (a v)) in (update (update a vb cvb) v cv))" |
  "apply_guard a (Ge vb (Plus v vc)) = (let (cvb, _) = (apply_geq (a vb) (apply_plus a v vc)) in (update a vb cvb))" |
  
  "apply_guard a (Le vb (N n)) = update a vb (and (a vb) (Leq n))" |
  "apply_guard a (Le vb (V v)) = (let (cvb, cv) = (apply_leq (a vb) (a v)) in (update (update a vb cvb) v cv))" |
  "apply_guard a (Le vb (Plus v vc)) = (let (cvb, _) = (apply_leq (a vb) (apply_plus a v vc)) in (update a vb cvb))" |

  "apply_guard a (Ne vb (N v)) = update a vb (and (a vb) (Neq v))" |
  "apply_guard a (Ne vb (V v)) = update a vb (Not (and  (a vb) (a v)))" |
  "apply_guard a (Ne vb (Plus va vc)) = update a vb (Not (and (a vb) (apply_plus a va vc)))"

fun apply_update :: "constraints \<Rightarrow> constraints \<Rightarrow> update_function \<Rightarrow> constraints" where
  "apply_update l c (v, (N n)) = update c v (Eq n)" |
  "apply_update l c (v, V vb) = update c v (l vb)" |
  "apply_update l c (v, Plus vb vc) = update c v (apply_plus l vb vc)"

primrec apply_guards :: "constraints \<Rightarrow> guard list \<Rightarrow> constraints" where
  "apply_guards c [] = c" |
  "apply_guards c (h#t) = (apply_guards (apply_guard c h) t)"

primrec apply_updates :: "constraints \<Rightarrow> constraints \<Rightarrow> update_function list \<Rightarrow> constraints" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = apply_updates l (apply_update l c h) t"

definition posterior :: "constraints \<Rightarrow> transition \<Rightarrow> constraints" where
  "posterior c t = (let c' = (apply_guards c (Guard t)) in (if consistent c' then (apply_updates c' empty (Updates t)) else (\<lambda>i. Bc False)))"

lemma "apply_guards empty [] = empty"
  by simp

lemma "constraints_equiv (apply_guards empty [(gexp.Eq ''i1'' (N 0))]) (\<lambda>x. if x = ''i1'' then Eq 0 else Bc True)"
  by (simp add: constraints_equiv_def update_def)

lemma constraints_simulates_symetry: "constraints_simulates c c"
  by (simp add: constraints_simulates_def)

end