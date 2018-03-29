theory CExp
  imports  Syntax
begin
datatype cexp = Bc bool | Not bexp | Less aexp | Eq aexp

type_synonym constraints = "vname \<rightharpoonup> cexp"

fun get_constraint :: "constraints \<Rightarrow> vname \<Rightarrow> cexp" where
  "get_constraint c v = (case (c v) of
    None \<Rightarrow> (Bc True) |
    Some (Eq (N n)) \<Rightarrow> (Eq (N n))
  )"

(*
  Takes an update function and a set of constraints and returns an updated set of constraints.
*)
fun apply_update :: "update_function \<Rightarrow> constraints \<Rightarrow> constraints" where
  "apply_update (v, (N n)) old = map_update old v (Eq (N n))" |
  "apply_update (v, (V v')) old = map_update old v (get_constraint old v')"

(*
  Takes a list of update functions, a set of old constraints, a set of new constraints, and returns
  an updated set of constraints.
*)
primrec apply_updates :: "update_function list \<Rightarrow> constraints \<Rightarrow> constraints \<Rightarrow> constraints" where
  "apply_updates [] _ new = new" |
  "apply_updates (h#t) old new = new ++ apply_updates t old (apply_update h old)"

value "(apply_updates [(''r1'', (V ''i1'')), (''r2'', (N 0))] (map_of [(''i1'', (Eq (N 1)))]) empty) ''r2''"

end