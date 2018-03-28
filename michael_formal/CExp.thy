theory CExp
imports Syntax
begin
datatype cexp = Bc bool | Not cexp | Less aexp | Gt aexp | Eq aexp
type_synonym constraints = "vname \<rightharpoonup> cexp"

definition get :: "constraints \<Rightarrow> vname \<Rightarrow> cexp" where
  "get c v = (case (c v) of None \<Rightarrow> (Bc True) | Some c \<Rightarrow> c)"

fun get_constraint :: "bexp \<Rightarrow> constraints \<Rightarrow> constraints" where
  "get_constraint (bexp.Bc True) c = c" | (*Literal true doesn't change anything*)
  "get_constraint (bexp.Bc False) _ = (\<lambda>x. Some (Bc False))" | (*Literal false invalidates everything*)
  "get_constraint (bexp.Not v) c = (\<lambda>x. 
    (case ((get_constraint v c) x) of
      None \<Rightarrow> None |
      (Some c') \<Rightarrow> Some (Not c'))
    )" | (*Negate whatever we get from parsing the condition*)
  "get_constraint (bexp.And v va) c = (get_constraint v c) ++ (get_constraint va c)" | (*Create two constraint sets*)
  "get_constraint (bexp.Less (V v) (N n)) c = map_of [(v, Less (N n))]" | (*Variable is less than literal*)
  "get_constraint (bexp.Less (N n) (V v)) _ = map_of [(v, Gt (N n))]" | (*Literal < variable \<Rightarrow> variable > literal*)
  "get_constraint (bexp.Less (V v) (V va)) _ = (map_of [(v, Less (V va))]) ++ (map_of [(va, Gt (V v))])" | (*v1 < v2 \<Rightarrow> v2 > v1*)
  "get_constraint (bexp.Less (N n1) (N n2)) _ = (\<lambda>x. Some (Bc (bval (bexp.Less (N n1) (N n2)) <>)))" | (*Two literals can just be evaluated*)
  "get_constraint (bexp.Less (V v) (Plus va vb)) _ = map_of [(v, Less (Plus va vb))]" |
  "get_constraint (bexp.Less (Plus va vb) (V v)) _ = map_of [(v, Gt (Plus va vb))]" |
  "get_constraint (bexp.Less (N vb) (Plus v vc)) b = undefined" | (*Don't phrase your guard like this!*)
  "get_constraint (bexp.Less (Plus vb vc) (N v)) b = undefined" | (*Don't phrase your guard like this!*)
  "get_constraint (bexp.Less (Plus vb vc) (Plus v vd)) b = undefined" (*Don't phrase your guard like this!*)

lemma "((get_constraint (bexp.Less (N 0) (V ''i1'')) empty) ''i1'') = Some (Gt (N 0))"
  by simp

lemma "((get_constraint (bexp.Less (N 100) (V ''r2'')) empty) ''r2'') = Some (Gt (N 100))"
  by simp

lemma "let c = (get_constraint (bexp.Less (V ''i1'') (V ''i2'')) empty) 
        in c ''i1'' = Some (Less (V ''i2'')) \<and> c ''i2'' = Some (Gt (V ''i1''))"
  by simp

fun cexp_simp :: "cexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "cexp_simp (Bc v) _ = (Bc v)" |
  "cexp_simp (Not v) c = Not (cexp_simp v c)"

fun plus_simp :: "aexp \<Rightarrow> constraints \<Rightarrow> cexp" where
  "plus_simp (N n) _ = Eq (N n)" |
  "plus_simp (V v) c = (cexp_simp (get c v) c)" |
  "plus_simp (Plus (N n1) (N n2)) _ = Eq (N (aval (Plus (N n1) (N n2)) <>))"

fun resolve :: "(string \<times> aexp) \<Rightarrow> constraints \<Rightarrow> constraints" where
  "resolve (r, (N n)) _ = map_of [(r, Eq (N n))]" |
  "resolve (r, (V v)) c = map_of [(r, (cexp_simp (get c v) c))]" |
  "resolve (r, Plus v va) = map_of [(r, (cexp_simp ))]

primrec updates :: "update_function \<Rightarrow> constraints \<Rightarrow> constraints" where
  "updates [] _ = empty" |
  "updates (h#t) c = (resolve h c) ++ updates t c"

primrec intermediate :: "bexp list \<Rightarrow> constraints \<Rightarrow> constraints" where
  "intermediate [] c = c" |
  "intermediate (h#t) c = intermediate t c++(get_constraint h c)"


fun update_constraints :: "transition \<Rightarrow> constraints \<Rightarrow> constraints" where
  "update_constraints t c = posterior (Updates t) (intermediate (Guard t) c)"

end