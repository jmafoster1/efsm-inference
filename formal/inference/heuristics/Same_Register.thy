theory Same_Register
  imports "../Inference"
begin

hide_const Transition.L
hide_const Transition.V
hide_const Transition.I
hide_const Transition.R
hide_const Transition.Plus
hide_const Transition.Minus
hide_const Transition.Times
hide_const Transition.Bc
hide_const Transition.Eq
hide_const Transition.Gt

fun updates :: "update_function list \<Rightarrow> vname_o option" where
  "updates [(n, a)] = Some (R n)" |
  "updates _ = None"

fun a_replace_with :: "aexp_o \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> aexp_o" where
  "a_replace_with (L v) _ _ = L v" |
  "a_replace_with (V v) r1 r2 = (if v = R r1 then V (R r2) else V v)" |
  "a_replace_with (Plus a1 a2) r1 r2 = Plus (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "a_replace_with (Minus a1 a2) r1 r2 = Minus (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "a_replace_with (Times a1 a2) r1 r2 = Times (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)"

fun g_replace_with :: "gexp_o \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> gexp_o" where
  "g_replace_with (Bc x) _ _ = Bc x" |
  "g_replace_with (Eq a1 a2) r1 r2 = Eq (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "g_replace_with (Gt a1 a2) r1 r2 = Eq (a_replace_with a1 r1 r2) (a_replace_with a2 r1 r2)" |
  "g_replace_with (Nor g1 g2) r1 r2 = Nor (g_replace_with g1 r1 r2) (g_replace_with g2 r1 r2)" |
  "g_replace_with (In v s) r1 r2 = In v s"

(* replace r1 with r2 *)
fun u_replace_with :: "update_function \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> update_function" where
  "u_replace_with (r, a) r1 r2 = ((if r = r1 then r2 else r), Abs_aexp (a_replace_with (aexp a) r1 r2))"

definition t_replace_with :: "transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition" where
  "t_replace_with t r1 r2 = \<lparr>Label = Label t,
                             Arity = Arity t,
                             Guard = map (\<lambda>g. Abs_gexp (g_replace_with (gexp g) r1 r2)) (Guard t),
                             Outputs = map (\<lambda>p. Abs_aexp (a_replace_with (aexp p) r1 r2)) (Outputs t),
                             Updates = map (\<lambda>u. u_replace_with u r1 r2) (Updates t)\<rparr>"

definition replace_with :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iEFSM" where
  "replace_with e r1 r2 = (fimage (\<lambda>(u, tf, t). (u, tf, t_replace_with t r1 r2)) e)"

fun same_register :: update_modifier where
  "same_register t1ID t2ID s new _ old _ = (let
     t1 = get_by_ids new t1ID;
     t2 = get_by_ids new t2ID;
     ut1 = updates (Updates t1);
     ut2 = updates (Updates t2) in
     if same_structure t1 t2 then
      case (ut1, ut2) of
       (Some (R r1), Some (R r2)) \<Rightarrow> Some (replace_with new r1 r2) |
       (_, _) \<Rightarrow> None
     else None
   )"
end