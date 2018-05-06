theory Constraints
imports Types CExp

begin

type_synonym constraints = "aexp \<Rightarrow> cexp"

abbreviation empty :: constraints where
  "empty \<equiv> (\<lambda>x. case x of
    (V v) \<Rightarrow> if hd v = CHR ''r'' then Undef else Bc True |
    _ \<Rightarrow> Bc True
  )"

fun get :: "constraints \<Rightarrow> aexp \<Rightarrow> cexp" where
  "get c (N n) = Eq n" |
  "get c (V v) = c (V v)" |
  "get c (Plus v va) = (And (c (Plus v va)) (c (Plus va v)))" |
  "get c (Minus v va) = (c (Minus v va))"

fun update :: "constraints \<Rightarrow> aexp \<Rightarrow> cexp \<Rightarrow> constraints" where
  "update c k v = (\<lambda>r. if r=k then v else c r)"

fun conjoin :: "constraints \<Rightarrow> constraints \<Rightarrow> constraints" where
  "conjoin c c' = (\<lambda>r. (and (c r) (c' r)))"

abbreviation constraints_equiv :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "constraints_equiv c c' \<equiv> (\<forall>r. cexp_equiv (c r) (c' r))"

fun cexp2gexp :: "aexp \<Rightarrow> cexp \<Rightarrow> gexp" where
  "cexp2gexp _ (Bc b) = gexp.Bc b" |
  "cexp2gexp a Undef = gexp.Bc False" |
  "cexp2gexp a (Eq v) = gexp.Eq a (N v)" |
  "cexp2gexp a (Lt v) = gexp.Lt a (N v)" |
  "cexp2gexp a (Gt v) = gexp.Gt a (N v)" |
  "cexp2gexp a (Not v) = gNot (cexp2gexp a v)" |
  "cexp2gexp a (And v va) = gAnd (cexp2gexp a v) (cexp2gexp a va)"
  
(* Is there a variable evaluation which can satisfy all of the constraints? *)
abbreviation consistent :: "constraints \<Rightarrow> bool" where
  "consistent c \<equiv> \<exists>s. \<forall>r. (c r) = Undef \<or> (gval (cexp2gexp r (c r)) s)"

theorem consistent_empty_1: "empty r = Undef \<or> empty r = Bc True"
  apply (cases r)
  by simp_all

theorem consistent_empty_2: "(\<forall>r. c r = Bc True \<or> c r = Undef) \<longrightarrow> consistent c"
  by force

lemma consistent_empty_3: "(\<forall>r. empty r = Bc True \<or> empty r = Undef) \<longrightarrow> consistent empty"
  apply (insert consistent_empty_2)
  by simp

lemma consistent_empty [simp]: "consistent empty"
  apply (insert consistent_empty_1 consistent_empty_3)
  by auto

abbreviation valid_constraints :: "constraints \<Rightarrow> bool" where
  "valid_constraints c \<equiv> \<forall>s. \<forall>r. gval (cexp2gexp r (c r)) s"

primrec and_insert :: "(vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) \<Rightarrow> (vname \<times> cexp) list" where
  "and_insert [] c = [c]" |
  "and_insert (h#t) c = (if fst h = fst c then ((fst h, and (snd h) (snd c))#t) else (h#(and_insert t c)))"

primrec pair_and :: "(vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) list \<Rightarrow> (vname \<times> cexp) list" where
  "pair_and [] c = c" |
  "pair_and (h#t) c = pair_and t (and_insert c h)"

fun guard2constraints :: "constraints \<Rightarrow> guard \<Rightarrow> (aexp \<times> cexp) list" where
  "guard2constraints a (gexp.Bc v) = [(V '''', Bc v)]" |
  "guard2constraints a (gexp.Eq v vb) = [(v, get a vb), (vb, get a v)]" |
  
  "guard2constraints a (gexp.Gt v (N n)) = [(v, (Gt n))]" |
  "guard2constraints a (gexp.Gt v vb) = (let (cv, cvb) = apply_gt (get a v) (get a vb) in [(v, cv), (vb, cvb)])" |

  "guard2constraints a (gexp.Lt v (N n)) = [(v, (Gt n))]" |
  "guard2constraints a (gexp.Lt v vb) = (let (cv, cvb) = apply_lt (get a v) (get a vb) in [(v, cv), (vb, cvb)])" |
  "guard2constraints a (Nor v va) = map (\<lambda>x. ((fst x), not (snd x))) (guard2constraints a v)@(guard2constraints a va)"

primrec pairs2constraints :: "(aexp \<times> cexp) list \<Rightarrow> constraints" where
  "pairs2constraints [] = empty" |
  "pairs2constraints (h#t) = conjoin (pairs2constraints t) (\<lambda>r. if r = (fst h) then (snd h) else Bc True)"

fun apply_guard :: "constraints \<Rightarrow> guard \<Rightarrow> constraints" where
  "apply_guard a g = conjoin a (pairs2constraints (guard2constraints a g))"

fun apply_update :: "constraints \<Rightarrow> constraints \<Rightarrow> update_function \<Rightarrow> constraints" where
  "apply_update l c (v, (N n)) = update c (V v) (Eq n)" |
  "apply_update l c (v, V vb) = update c (V v) (l (V vb))" |
  "apply_update l c (v, Plus vb vc) = update c (V v) (compose_plus (get l vb) (get l vc))" |
  "apply_update l c (v, Minus vb vc) = update c (V v) (compose_minus (get l vb) (get l vc))"

primrec constraints_apply_guards :: "constraints \<Rightarrow> guard list \<Rightarrow> constraints" where
  "constraints_apply_guards c [] = c" |
  "constraints_apply_guards c (h#t) = (constraints_apply_guards (apply_guard c h) t)"

primrec apply_updates :: "constraints \<Rightarrow> constraints \<Rightarrow> update_function list \<Rightarrow> constraints" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = apply_updates l (apply_update l c h) t"

definition posterior :: "constraints \<Rightarrow> transition \<Rightarrow> constraints" where
  "posterior c t = (let c' = (constraints_apply_guards c (Guard t)) in (if consistent c' then (apply_updates c' empty (Updates t)) else (\<lambda>i. Bc False)))"

abbreviation can_take :: "transition \<Rightarrow> constraints \<Rightarrow> bool" where
  "can_take t c \<equiv> consistent (constraints_apply_guards c (Guard t))"

primrec posterior_n :: "nat \<Rightarrow> transition \<Rightarrow> constraints \<Rightarrow> constraints" where
  "posterior_n 0 _ c = c " |
  "posterior_n (Suc m) t c = posterior_n m t (posterior c t)"

primrec posterior_sequence :: "transition list \<Rightarrow> constraints \<Rightarrow> constraints" where
  "posterior_sequence [] c = c" |
  "posterior_sequence (h#t) c = posterior_sequence t (posterior c h)"

lemma "constraints_apply_guards empty [] = empty"
  by simp

abbreviation subsumes :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "subsumes c c' \<equiv> (\<forall> r i. (ceval (c' r) i \<longrightarrow> ceval (c r) i) \<or> ((c r) = Undef))"

lemma "subsumes (\<lambda>x. Bc True) (\<lambda>x. Bc False)"
  by simp

lemma subsumes_reflexivity:  "subsumes x x"
  by simp

primrec apply_outputs :: "output_function list \<Rightarrow> state \<Rightarrow> registers \<Rightarrow> outputs" where
  "apply_outputs [] _ _ = []" |
  "apply_outputs (h#t) i r = (aval h (join i r))#(apply_outputs t i r)"

primrec apply_guards :: "guard list \<Rightarrow> state \<Rightarrow> registers \<Rightarrow> bool" where
  "apply_guards [] _ _ = True" |
  "apply_guards (h#t) i r =  ((gval h (join i r)) \<and> (apply_guards t i r))"

(* Widening the precondition and reducing nondeterminism *)
(* Guards of A imply guards of B and if the precondition of A is satisfied and we do a B then the
   posterior state of B is consistent with those of A *)
abbreviation is_generalisation :: "constraints \<Rightarrow> transition \<Rightarrow> constraints \<Rightarrow> transition \<Rightarrow> bool" where
  "is_generalisation cb b ca a \<equiv> (subsumes (constraints_apply_guards cb (Guard b)) (constraints_apply_guards ca (Guard a))) \<and>
                                 (\<forall>i r. (apply_guards (Guard a) i r) \<longrightarrow> (apply_outputs (Outputs b) i r) = (apply_outputs (Outputs a) i r)) \<and>
                                 (subsumes (posterior ca a) (posterior (constraints_apply_guards cb (Guard a)) b))"
end