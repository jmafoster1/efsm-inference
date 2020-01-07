theory Weak_Subsumption
imports "../Inference"
begin

definition maxBy :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "maxBy f a b = (if (f a > f b) then a else b)"

fun weak_subsumption :: "log \<Rightarrow> update_modifier" where
  "weak_subsumption log t1ID t2ID s new _ old _ = (let
     t1 = get_by_ids new t1ID;
     t2 = get_by_ids new t2ID
     in
     if
      Label t1 = Label t2 \<and>
      Arity t1 = Arity t2 \<and>
      Guard t1 = Guard t2 \<and>
      Outputs t1 = Outputs t2 \<and>
      length (Updates t1) \<noteq> length (Updates t2)
     then
      let newEFSM = replace_all new [t1ID, t2ID] (maxBy (length \<circ> Updates) t1 t2) in
      if satisfies (set log) (tm newEFSM) then
        Some newEFSM
      else
        None
     else
      None
   )"

end