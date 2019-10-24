theory Equals
imports "../Inference"
begin

fun equality_pairs :: "gexp list \<Rightarrow> (nat \<times> value) list" where
  "equality_pairs [] = []" |
  "equality_pairs ((Eq (V (I n)) (L l))#t) = ((n, l)#(equality_pairs t))" |
  "equality_pairs (h#t) = equality_pairs t"

definition "gen_eq = \<lparr>Label = STR ''equals'', Arity = 2, Guard = [Eq (V (I 0)) (V (I 1))], Outputs = [L (Str ''true'')], Updates = []\<rparr>"

definition is_equals :: "transition \<Rightarrow> bool" where
  "is_equals t = (let ep = (equality_pairs (Guard t)) in 
        Label t = STR ''equals'' \<and>
        Arity t = 2 \<and>
        snd (ep ! 0) = snd (ep ! 1) \<and>
        map fst ep = [0, 1] \<and>
        Outputs t = [L (Str ''true'')])"

fun equals :: update_modifier where
  "equals t1ID t2ID s new old _ = (let
     t1 = (get_by_ids new t1ID);
     t2 = (get_by_ids new t2ID) in
     if is_equals t1 \<and> is_equals t2
     then
           Some (replace_transitions new [(t1ID, gen_eq), (t2ID, gen_eq)])
     else None
   )"

definition "gen_neq = \<lparr>Label = STR ''equals'', Arity = 2, Guard = [Eq (V (I 0)) (V (I 1))], Outputs = [L (Str ''true'')], Updates = []\<rparr>"

definition is_not_equals :: "transition \<Rightarrow> bool" where
  "is_not_equals t = (let ep = (equality_pairs (Guard t)) in 
        Label t = STR ''equals'' \<and>
        Arity t = 2 \<and>
        snd (ep ! 0) \<noteq> snd (ep ! 1) \<and>
        map fst ep = [0, 1] \<and>
        Outputs t = [L (Str ''true'')])"

fun not_equals :: update_modifier where
  "not_equals t1ID t2ID s new old _ = (let
     t1 = (get_by_ids new t1ID);
     t2 = (get_by_ids new t2ID) in
     if is_equals t1 \<and> is_equals t2
     then
           Some (replace_transitions new [(t1ID, gen_neq), (t2ID, gen_neq)])
     else None
   )"

end