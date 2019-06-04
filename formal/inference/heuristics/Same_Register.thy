theory Same_Register
  imports "../Inference"
begin

fun updates :: "update_function list \<Rightarrow> vname option" where
  "updates [(R n, a)] = Some (R n)" |
  "updates _ = None"

fun a_replace_with :: "aexp \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> aexp" where
  "a_replace_with (L v) _ _ = L v" |
  "a_replace_with (V v) r1 r2 = (if v = r1 then V r2 else V v)" |
  "a_replace_with (Plus a1 a2) r1 r2 = Plus (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "a_replace_with (Minus a1 a2) r1 r2 = Plus (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)"

fun g_replace_with :: "gexp \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> gexp" where
  "g_replace_with (gexp.Bc x) _ _ = gexp.Bc x" |
  "g_replace_with (gexp.Eq a1 a2) r1 r2 = gexp.Eq (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "g_replace_with (gexp.Gt a1 a2) r1 r2 = gexp.Eq (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "g_replace_with (gexp.Nor g1 g2) r1 r2 = gexp.Nor (g_replace_with g1 r1 r2) (g_replace_with g2 r1 r2)" |
  "g_replace_with (gexp.Null a1) r1 r2 = gexp.Null (a_replace_with a1 r1 r2)"

(* replace r1 with r2 *)
fun u_replace_with :: "update_function \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> update_function" where
  "u_replace_with (r, a) r1 r2 = ((if r = r1 then r2 else r), a_replace_with a r1 r2)"

definition t_replace_with :: "transition \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> transition" where
  "t_replace_with t r1 r2 = \<lparr>Label = Label t,
                             Arity = Arity t,
                             Guard = map (\<lambda>g. g_replace_with g r1 r2) (Guard t),
                             Outputs = map (\<lambda>p. a_replace_with p r1 r2) (Outputs t),
                             Updates = map (\<lambda>u. u_replace_with u r1 r2) (Updates t)\<rparr>"

definition replace_with :: "iEFSM \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> iEFSM" where
  "replace_with e r1 r2 = fimage (\<lambda>(u, tf, t). (u, tf, t_replace_with t r1 r2)) e"

definition print :: "String.literal \<Rightarrow> unit" where
  "print p = ()"

definition tprint :: "transition \<Rightarrow> unit" where
  "tprint p = ()"

definition r_print :: "transition \<Rightarrow> transition" where
  "r_print t = (let f = tprint t in t)"

fun same_register :: update_modifier where
  "same_register t1ID t2ID s new old = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID);
     ut1 = updates (Updates t1);
     ut2 = updates (Updates t2) in
     if same_structure t1 t2 then
      case (ut1, ut2) of
       (Some r1, Some r2) \<Rightarrow> Some (replace_with new r1 r2) |
       (_, _) \<Rightarrow> None
     else None
   )"

abbreviation "coin_general r \<equiv> \<lparr>Label = STR ''coin'', Arity = 1, Guard = [], Outputs = [Plus (V (R r)) (V (I 1))], Updates = [(R r, Plus (V (R r)) (V (I 1)))]\<rparr>"

lemma "same_structure (coin_general x) (coin_general y)"
  by (simp add: same_structure_def)

abbreviation select :: "String.literal \<Rightarrow> transition" where
  "select drink \<equiv> \<lparr>Label = (STR ''select''), Arity = 1, Guard = [gexp.Eq (V (I 1)) (L ((value.Str drink)))], Outputs = [], Updates = []\<rparr>"

lemma "same_structure (select coke) (select pepsi)"
  by (simp add: same_structure_def)

code_printing
  constant "print" \<rightharpoonup> (Scala) "println" |
  constant "tprint" \<rightharpoonup> (Scala) "println"


end