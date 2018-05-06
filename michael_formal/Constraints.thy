theory Constraints
imports Types CExp

begin

type_synonym constraint = "(aexp \<times> cexp)"
type_synonym constraints = "constraint list"

abbreviation empty :: constraints where
  "empty \<equiv> []"

primrec update :: "constraints \<Rightarrow> aexp \<Rightarrow> cexp \<Rightarrow> constraints" where
  "update [] k v = [(k, v)]" |
  "update (h#t) k v = (if fst h = k then (k, v)#t else h#(update t k v))"

primrec get :: "constraints \<Rightarrow> aexp \<Rightarrow> cexp" where
  "get [] v = (case v of
    (N n) \<Rightarrow> Eq n |
    (V v') \<Rightarrow> (if hd v' = CHR ''r'' then Undef else Bc True) |
    _ \<Rightarrow> Bc True
  )" |
  "get (h#t) v = (if fst h = v then snd h else get t v)"

fun constraint2gexp :: "constraint \<Rightarrow> gexp" where
  "constraint2gexp (_, Bc b) = gexp.Bc b" |
  "constraint2gexp (v, Undef) = gexp.Bc True" |
  "constraint2gexp (v, cexp.Eq vb) = gexp.Eq v (N vb)" |
  "constraint2gexp (v, cexp.Lt vb) = gexp.Lt v (N vb)" |
  "constraint2gexp (v, cexp.Gt vb) = gexp.Gt v (N vb)" |
  "constraint2gexp (v, cexp.Nand vb vc) = gexp.Nand (constraint2gexp (v, vb)) (constraint2gexp (v, vc))"

primrec consistent_r :: "constraints \<Rightarrow> gexp \<Rightarrow> bool" where
  "consistent_r [] g = gexp_satisfiable g" |
  "consistent_r (h#t) g = consistent_r t (gAnd (constraint2gexp h) g)"

abbreviation consistent :: "constraints \<Rightarrow> bool" where
  "consistent c \<equiv> consistent_r c (gexp.Bc True)"

abbreviation constraints_equiv :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "constraints_equiv c c' \<equiv> (\<forall>r. cexp_equiv (get c r) (get c' r))"

primrec constraints_nand :: "constraints \<Rightarrow> constraints \<Rightarrow> constraints" where
  "constraints_nand [] c = c" |
  "constraints_nand (h#t) c = constraints_nand t (update c (fst h) (Or (not (snd h)) (not (get c (fst h)))))"

(* This assumes the existence of a list of guards which contains all "permutations" of each guard *)
(* e.g. if r1>r2+i1 is in the list then so are the following:                                     *)
(* 0 > r2+i1-r1 | r1 > r2+i1 | r2+i1 < r1 |              |                                        *)
(*              | i1 < r1-r2 | r1-r2 > i1 |              |                                        *)
(*              | r2 < r1-i1 | r1-i1 > r2 | r2+i1-r1 < 0 |                                        *)
(* It also assumes that the list is sorted to maximise information gain, i.e. literal checks are  *)
(* before compound checks and that solvable simultaneous guards have been solved                  *)
fun applyguard :: "constraints \<Rightarrow> guard \<Rightarrow> constraints" where
  "applyguard a (gexp.Bc v) = update a (V '''') (Bc v)" |
  "applyguard a (gexp.Eq va (N n)) = update a va (Eq n)" |
  "applyguard a (gexp.Eq v (V vb)) = update a v (get a (V vb))" |
  "applyguard a (gexp.Eq v (Plus vb vc)) = update a v (compose_plus (get a vb) (get a vc))" |
  "applyguard a (gexp.Eq v (Minus vb vc)) = update a v (compose_minus (get a vb) (get a vc))" |
  "applyguard a (gexp.Gt va (N n)) = update a va (Gt n)" |
  "applyguard a (gexp.Gt v (V vb)) = update a v (make_gt (get a v) (get a (V vb)))" |
  "applyguard a (gexp.Gt v (Plus vb vc)) = [(v, make_gt (get a v) (compose_plus (get a vb) (get a vc)))]" |
  "applyguard a (gexp.Gt v (Minus vb vc)) = [(v, make_gt (get a v) (compose_minus (get a vb) (get a vc)))]" |
  "applyguard a (gexp.Lt va (N n)) = [(va, Lt n)]" |
  "applyguard a (gexp.Lt v (V vb)) = [(v, make_lt (get a v) (get a (V vb)))]" |
  "applyguard a (gexp.Lt v (Plus vb vc)) = [(v, make_lt (get a v) (compose_plus (get a vb) (get a vc)))]" |
  "applyguard a (gexp.Lt v (Minus vb vc)) = [(v, make_lt (get a v) (compose_minus (get a vb) (get a vc)))]" |
  "applyguard a (gexp.Nand v va) = constraints_nand (applyguard a v) (applyguard a va)"

fun apply_update :: "constraints \<Rightarrow> constraints \<Rightarrow> update_function \<Rightarrow> constraints" where
  "apply_update l c (v, (N n)) = update c (V v) (Eq n)" |
  "apply_update l c (v, V vb) = update c (V v) (get l (V vb))" |
  "apply_update l c (v, Plus vb vc) = update c (V v) (compose_plus (get l vb) (get l vc))" |
  "apply_update l c (v, Minus vb vc) = update c (V v) (compose_minus (get l vb) (get l vc))"

primrec constraints_apply_guards :: "constraints \<Rightarrow> guard list \<Rightarrow> constraints" where
  "constraints_apply_guards c [] = c" |
  "constraints_apply_guards c (h#t) = (constraints_apply_guards (applyguard c h) t)"

primrec apply_updates :: "constraints \<Rightarrow> constraints \<Rightarrow> update_function list \<Rightarrow> constraints" where
  "apply_updates _ c [] = c" |
  "apply_updates l c (h#t) = apply_updates l (apply_update l c h) t"

definition posterior :: "constraints \<Rightarrow> transition \<Rightarrow> constraints" where
  "posterior c t = (let c' = (constraints_apply_guards c (Guard t)) in (if consistent c' then (apply_updates c' [] (Updates t)) else [((V ''''), Bc False)]))"

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

lemma "constraints_equiv (constraints_apply_guards empty [(gexp.Eq (V ''i1'') (N 0))]) [((V ''i1''), Eq 0)]"
  by simp

abbreviation subsumes :: "constraints \<Rightarrow> constraints \<Rightarrow> bool" where
  "subsumes c c' \<equiv> (\<forall> r i. (ceval (get c' r) i \<longrightarrow> ceval (get c r) i) \<or> ((get c r) = Undef))"

lemma "subsumes [(x, Bc True)] [(x, Bc False)]"
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