theory Same_Register
  imports "../Inference"
begin

fun updates :: "update_function list \<Rightarrow> vname option" where
  "updates [(n, a)] = Some (R n)" |
  "updates _ = None"

fun a_replace_with :: "aexp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> aexp" where
  "a_replace_with (L v) _ _ = L v" |
  "a_replace_with (V v) r1 r2 = (if v = R r1 then V (R r2) else V v)" |
  "a_replace_with (Plus a1 a2) r1 r2 = Plus (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "a_replace_with (Minus a1 a2) r1 r2 = Plus (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)"

fun g_replace_with :: "gexp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gexp" where
  "g_replace_with (gexp.Bc x) _ _ = gexp.Bc x" |
  "g_replace_with (gexp.Eq a1 a2) r1 r2 = gexp.Eq (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "g_replace_with (gexp.Gt a1 a2) r1 r2 = gexp.Eq (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "g_replace_with (gexp.Nor g1 g2) r1 r2 = gexp.Nor (g_replace_with g1 r1 r2) (g_replace_with g2 r1 r2)" |
  "g_replace_with (gexp.Null a1) r1 r2 = gexp.Null (a_replace_with a1 r1 r2)"

(* replace r1 with r2 *)
fun u_replace_with :: "update_function \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> update_function" where
  "u_replace_with (r, a) r1 r2 = ((if r = r1 then r2 else r), a_replace_with a r1 r2)"

definition t_replace_with :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "t_replace_with t r1 r2 = \<lparr>Label = Label t,
                             Arity = Arity t,
                             Guard = map (\<lambda>g. g_replace_with g r1 r2) (Guard t),
                             Outputs = map (\<lambda>p. a_replace_with p r1 r2) (Outputs t),
                             Updates = map (\<lambda>u. u_replace_with u r1 r2) (Updates t)\<rparr>"

definition replace_with :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iEFSM" where
  "replace_with e r1 r2 = to_new_representation (fimage (\<lambda>(u, tf, t). (u, tf, t_replace_with t r1 r2)) (to_old_representation e))"

definition print :: "String.literal \<Rightarrow> unit" where
  "print p = ()"

definition tprint :: "transition \<Rightarrow> unit" where
  "tprint p = ()"

definition r_print :: "transition \<Rightarrow> transition" where
  "r_print t = (let f = tprint t in t)"

fun same_register :: update_modifier where
  "same_register t1ID t2ID s new old _ = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID);
     ut1 = updates (Updates t1);
     ut2 = updates (Updates t2) in
     if same_structure t1 t2 then
      case (ut1, ut2) of
       (Some (R r1), Some (R r2)) \<Rightarrow> Some (replace_with new r1 r2) |
       (_, _) \<Rightarrow> None
     else None
   )"

code_printing
  constant "print" \<rightharpoonup> (Scala) "println" |
  constant "tprint" \<rightharpoonup> (Scala) "println"

end