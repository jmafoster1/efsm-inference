theory CExp
  imports Main
begin

datatype cexp = Bc bool | Eq int | Lt int | Gt int | Not cexp | And cexp cexp

(* Less than or equal to *)
abbreviation Leq :: "int \<Rightarrow> cexp" where
  "Leq v \<equiv> Not (Gt v)"

(* Greater than or equal to *)
abbreviation Geq :: "int \<Rightarrow> cexp" where
  "Geq v \<equiv> Not (Lt v)"

(* Not equal to *)
abbreviation Neq :: "int \<Rightarrow> cexp" where
  "Neq v \<equiv> Not (Eq v)"

(* Logical Or in terms of And and Not*)
abbreviation Or :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "Or v va \<equiv> Not (And (Not v) (Not va))"

(* Does a given value of "i" satisfy the given cexp? *)
fun ceval :: "cexp \<Rightarrow> (int \<Rightarrow> bool)" where
  "ceval (Bc b) = (\<lambda>i. b)" |
  "ceval (Eq v) = (\<lambda>i. i = v)" |
  "ceval (Lt v) = (\<lambda>i. i < v)" |
  "ceval (Gt v) = (\<lambda>i. i > v)" |
  "ceval (Not v) = (\<lambda>i. \<not>(ceval v i))" |
  "ceval (And v va) = (\<lambda>i. (ceval v i \<and> ceval va i))"

(* Are cexps "c" and "c'" satisfied under the same conditions? *)
abbreviation cexp_equiv :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_equiv c c' \<equiv> (\<forall>i. (ceval c i) = (ceval c' i))"

(* Is cexp "c" satisfied under all "i" values? *)
abbreviation valid :: "cexp \<Rightarrow> bool" where
  "valid c \<equiv> (\<forall> i. ceval c i)"

(* Is there some value of "i" which satisfies "c"? *)
abbreviation satisfiable :: "cexp \<Rightarrow> bool" where
  "satisfiable v \<equiv> (\<exists>i. ceval v i)"

(* Does cexp "c" simulate "c'"? *)
abbreviation cexp_simulates :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_simulates c c' \<equiv> (\<forall>i. ceval c' i \<longrightarrow> ceval c i)"

definition "and" :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "and x y = (case x of
    Bc True \<Rightarrow> y |
    Bc False \<Rightarrow> Bc False |
    Eq i \<Rightarrow> (case y of 
      Eq i' \<Rightarrow> (if i = i' then Eq i else Bc False) |
      _ \<Rightarrow> And x y
    ) |
    _ \<Rightarrow> (case y of
      Bc True \<Rightarrow> x |
      Bc False \<Rightarrow> Bc False |
      _ \<Rightarrow> And x y
    )
  )"

theorem and_is_And:  "ceval (and x y) = ceval (And x y)"
proof (cases "x")
  case (Bc x1)
  then show ?thesis
    apply (case_tac "x1 = True")
    by (simp_all add: and_def)
next
  case (Eq x2)
  then show ?thesis
    apply simp
    apply (cases "y")
         apply (simp_all add: and_def)
    by auto  
next
  case (Lt x3)
  then show ?thesis
    apply simp
    apply (cases "y")
         apply simp_all
    apply (cases "y = Bc True")
    by (simp_all add: and_def)
next
  case (Gt x4)
  then show ?thesis
    apply simp
    apply (cases "y")
         apply simp_all
    apply (cases "y = Bc True")
    by (simp_all add: and_def)
next
  case (Not x5)
  then show ?thesis
    apply simp
    apply (cases "y")
         apply simp_all
    apply (cases "y = Bc True")
    by (simp_all add: and_def)
next
  case (And x61 x62)
  then show ?thesis
    apply simp
    apply (cases "y")
         apply simp_all
    apply (cases "y = Bc True")
    by (simp_all add: and_def)
qed
declare and_is_And [simp]

definition "not" :: "cexp \<Rightarrow> cexp" where
  "not c = (case c of
    Bc True \<Rightarrow> Bc False |
    Bc False \<Rightarrow> Bc True |
    Not x \<Rightarrow> x |
    c \<Rightarrow> Not c
  )"

theorem not_is_Not: "ceval (not x) = ceval (Not x)"
  proof (cases "x")
  case (Bc x1)
  then show ?thesis
    apply (case_tac "x1 = True")
    by (simp_all add: not_def)
  next
  case (Eq x2)
  then show ?thesis
    by (simp add: not_def)
  next
  case (Lt x3)
  then show ?thesis
    by (simp add: not_def)
  next
  case (Gt x4)
  then show ?thesis
    by (simp add: not_def)
  next
  case (Not x5)
  then show ?thesis
    by (simp add: not_def)
  next
  case (And x61 x62)
  then show ?thesis
    by (simp add: not_def)
qed
declare not_is_Not [simp]

lemma "ceval (Bc True) = ceval (Not (Bc False))"
  by simp

lemma "ceval (Bc False) = ceval (Not (Bc True))"
  by simp

lemma "\<forall> i. (ceval (And (Eq 1) (Gt 2))) i = False"
  by simp

lemma "ceval (Not (Not v)) = ceval v"
  by simp

lemma "cexp_simulates (Bc True) a"
  by simp

lemma everything_simulates_false: "\<forall>c. cexp_simulates c (Bc False)"
  by simp

lemma "cexp_simulates (Bc False) a \<Longrightarrow> cexp_equiv a (Bc False)"
  by simp

lemma "cexp_simulates (Lt 10) (Lt 5)"
  by simp

lemma simulates_symmetry: "cexp_simulates x x"
  by simp

fun compose_plus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_plus (Not (Not v)) va = compose_plus v va" |
  "compose_plus v (Not (Not va)) = compose_plus v va" |
  "compose_plus (And v va) vb = and (compose_plus v vb) (compose_plus va vb)" |
  "compose_plus v (And va vb) = and (compose_plus v va) (compose_plus v vb)" |
  "compose_plus (Not (And v va)) vb = not (and (compose_plus v vb) (compose_plus va vb))" |
  "compose_plus v (Not (And va vb)) = not (and (compose_plus v va) (compose_plus v vb))" |
  "compose_plus (Eq v) (Eq va) = Eq (v+va)" |
  "compose_plus (Eq v) (Lt va) = Lt (v+va)" |
  "compose_plus (Eq v) (Gt va) = Gt (v+va)" |
  "compose_plus (Eq v) (Leq va) = Leq (v+va)" |
  "compose_plus (Eq v) (Geq va) = Geq (v+va)" |

  "compose_plus (Lt v) (Eq va) = Lt (v+va)" |
  "compose_plus (Lt v) (Lt va) = Lt (v+va)" |
  "compose_plus (Lt v) (Leq va) = Lt (v+va)" |

  "compose_plus (Gt v) (Eq va) = Gt (v+va)" |
  "compose_plus (Gt v) (Gt va) = Gt (v+va)" |
  "compose_plus (Gt v) (Geq va) = Gt (v+va)" |

  "compose_plus (Leq v) (Eq va) = Leq (v+va)" |
  "compose_plus (Leq v) (Lt va) = Lt (v+va)" |
  "compose_plus (Leq v) (Leq va) = Leq (v+va)" |

  "compose_plus (Geq v) (Eq va) = Geq (v+va)" |
  "compose_plus (Geq v) (Gt va) = Gt (v+va)" |
  "compose_plus (Geq v) (Geq va) = Geq (v+va)" |

  "compose_plus (Bc False) _ = Bc False" |
  "compose_plus _ (Bc False) = Bc False" |
  "compose_plus (Not (Bc True)) _ = Bc False" |
  "compose_plus _ (Not (Bc True)) = Bc False" |

  "compose_plus _ _ = Bc True"

fun compose_minus :: "cexp \<Rightarrow> cexp \<Rightarrow> cexp" where
  "compose_minus (Bc v) _ = Bc v" |
  "compose_minus _ (Bc v) = Bc v" |
  "compose_minus (Not (Bc v)) _ = Bc (\<not>v)" |
  "compose_minus _ (Not (Bc v)) = Bc (\<not>v)" |

  "compose_minus a (Not (Not vb)) = compose_minus a vb"|
  "compose_minus (Not (Not vb)) a = compose_minus vb a"|
  "compose_minus a (And va vb) = and (compose_minus a va) (compose_minus a vb)"|
  "compose_minus (And va vb) a = and (compose_minus va a) (compose_minus vb a)"|
  "compose_minus a (Not (And va vb)) = Not (and (compose_minus a va) (compose_minus a vb))"|
  "compose_minus (Not (And va vb)) a = Not (and (compose_minus va a) (compose_minus vb a))"|

  "compose_minus (Eq n) (Eq n') = Eq (n-n')" |
  "compose_minus (Eq n) (Lt n') = Gt (n-n')" |
  "compose_minus (Eq n) (Gt n') = Lt (n-n')" |
  "compose_minus (Eq v) (Geq vb) = Leq (v-vb)" |
  "compose_minus (Eq v) (Leq vb) = Geq (v-vb)" |
  
  "compose_minus (Lt v) (Eq va) = Lt (v-va)" |
  "compose_minus (Lt v) (Gt va) = Lt (v-va)" |
  "compose_minus (Lt v) (Geq va) = Lt (v-va)" |

  "compose_minus (Gt v) (Eq va) = Gt (v-va)" |
  "compose_minus (Gt v) (Lt va) = Gt (v-va)" |
  "compose_minus (Gt v) (Leq va) = Gt (v-va)" |

  "compose_minus (Geq v) (Eq va) = Geq (v-va)" |
  "compose_minus (Geq vb) (Lt va) = Geq (vb-va)" |
  "compose_minus (Geq vb) (Leq v) = Geq (vb-v)" |

  "compose_minus (Leq v) (Eq va) = Leq (v-va)" |
  "compose_minus (Leq v) (Gt va) = Lt (v-va)" |
  "compose_minus (Leq vb) (Geq v) = Leq (vb-v)" |

  "compose_minus _ _ = Bc True"

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
  "apply_gt v (Not (And va vb)) = (Not (and (fst (apply_gt v va)) (fst (apply_gt v vb))), Not (and (snd (apply_gt v va)) (snd (apply_gt v vb))))" |
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

fun apply_lt :: "cexp \<Rightarrow> cexp \<Rightarrow> (cexp \<times> cexp)" where
  "apply_lt a b = (let (ca, cb) = (apply_gt b a) in (cb, ca))"
end