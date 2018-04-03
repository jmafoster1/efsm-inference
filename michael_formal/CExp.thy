theory CExp
  imports Syntax
begin
datatype cexp = Bc bool | And cexp cexp | Not cexp | Lt aexp | Gt aexp

type_synonym constraints = "vname \<rightharpoonup> cexp"

definition Eq :: "aexp \<Rightarrow> cexp" where
  "Eq x = And (Not (Gt x)) (Not (Lt x))"

definition get :: "constraints \<Rightarrow> vname \<Rightarrow> cexp" where
  "get c v = (case (c v) of
    None \<Rightarrow> (Bc True) |
    Some c \<Rightarrow> c
  )"

fun cexp_simp :: "cexp \<Rightarrow> cexp" where
  "cexp_simp (Bc c) = Bc c" |
  "cexp_simp (And (Bc False) _) = Bc False" |
  "cexp_simp (And _ (Bc False)) = Bc False" |
  "cexp_simp (And (Bc True) c) = cexp_simp c" |
  "cexp_simp (And c (Bc True)) = cexp_simp c" |
  "cexp_simp (And c c') = (if c = c' then c else And (cexp_simp c) (cexp_simp c'))" |
  "cexp_simp (Not c) = Not (cexp_simp c)" |
  "cexp_simp (Lt v) = Lt v" |
  "cexp_simp (Gt v) = Gt v"

definition conjoin :: "constraints \<Rightarrow> constraints \<Rightarrow> constraints" where
  "conjoin c1 c2 = (\<lambda>x. case (c1 x) of
    None \<Rightarrow> (case (c2 x) of
      None \<Rightarrow> None |
      Some c' \<Rightarrow> Some (cexp_simp c')
    ) |
    Some c \<Rightarrow> (case (c2 x) of
      None \<Rightarrow> Some c |
      Some c' \<Rightarrow> Some (cexp_simp (And c c'))
    )
  )"

(*Bc bool | And cexp cexp | Not cexp | Lt aexp | Gt aexp*)
fun plus_c :: "cexp \<Rightarrow> cexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "plus_c (Bc c) _ _ = (Bc c)" |
  "plus_c _ (Bc c) _ = (Bc c)" |
  "plus_c (And a b) (Eq (N n)) c = And (plus_c a (Eq (N n)) c) (plus_c b (Eq (N n)) c)"

fun plus_a :: "aexp \<Rightarrow> aexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "plus_a (N n) (N n') _ = Eq (N (n+n'))" |
  "plus_a (N n) (V v) c = plus_c (Eq (N n)) (get c v) c" |
  "plus_a (V v) (N n) c = plus_c (Eq (N n)) (get c v) c" |
  "plus_a (V v) (V v') c = plus_c (get c v) (get c v') c" |
  "plus_a (V v) (Plus x y) c =  plus_c (get c v) (plus_a x y c) c" |
  "plus_a (N n) (Plus x y) c =  plus_c (Eq (N n)) (plus_a x y c) c" |
  "plus_a (Plus x y) (V v) c =  plus_c (get c v) (plus_a x y c) c" |
  "plus_a (Plus x y) (N n) c =  plus_c (Eq (N n)) (plus_a x y c) c" |
  "plus_a (Plus x y) (Plus x' y') c =  plus_c (plus_a x y c) (plus_a x' y' c) c"

(*
  Takes an update function and a set of constraints and returns an updated set of constraints.
*)
fun apply_update :: "update_function \<Rightarrow> constraints \<Rightarrow> constraints \<Rightarrow> constraints" where
  "apply_update (v, (N n)) old new = map_update new v (Eq (N n))" |
  "apply_update (v, (V v')) old new = (case (old v) of
    None \<Rightarrow> map_update new v (Bc True) |
    Some c  \<Rightarrow> map_update old v c
  )" |
  "apply_update (v, (Plus a b)) old new = map_update new v (plus a b old)"

(*
  Takes a list of update functions, a set of old constraints, a set of new constraints, and returns
  an updated set of constraints.
*)
primrec apply_updates :: "update_function list \<Rightarrow> constraints \<Rightarrow> constraints \<Rightarrow> constraints" where
  "apply_updates [] _ new = new" |
  "apply_updates (h#t) old new = new ++ apply_updates t old (apply_update h old new)"

value "(apply_updates [(''r1'', (V ''i1'')), (''r2'', (N 0))] (map_of [(''i1'', (Eq (N 1)))]) empty) ''r2''"

fun apply_guard :: "guard \<Rightarrow> constraints \<Rightarrow> constraints" where
  "apply_guard (bexp.Bc True) c = c" |
  "apply_guard (bexp.Bc False) _ = (\<lambda>x. Some (Bc False))" |
  "apply_guard (bexp.Not e) c = conjoin c (\<lambda>x. case ((apply_guard e c) x) of None \<Rightarrow> None | Some e' \<Rightarrow> Some (Not e'))" |
  "apply_guard (bexp.And e1 e2) c = conjoin c (conjoin (apply_guard e1 c) (apply_guard e2 c))" |
  "apply_guard (Less (V v) e) c = conjoin c (map_update empty v (Lt e))" |
  "apply_guard (Less e (V v)) c = conjoin c (map_update empty v (Gt e))" |
  "apply_guard _ _ = empty" (* Phrase your guard differently *)

primrec apply_guards :: "guard list \<Rightarrow> constraints \<Rightarrow> constraints" where
  "apply_guards [] c  = c" |
  "apply_guards (h#t) c = c ++ apply_guard h c"

value "(apply_guards [(bexp.And (bexp.Not (bexp.Less (N 50) (V ''i1''))) (bexp.Not (bexp.Less (V ''i1'') (N 50))))] empty) ''i1''"

definition constraints :: "constraints \<Rightarrow> transition \<Rightarrow> constraints" where
  "constraints c t = apply_updates (Updates t) (apply_guards (Guard t) c) empty"

end