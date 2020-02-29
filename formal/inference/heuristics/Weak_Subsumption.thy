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
      same_structure t1 t2
     then
      let
        maxT = maxBy (\<lambda>x. ((length \<circ> Updates) x, map snd (Updates x))) t1 t2;
        minT = if maxT = t1 then t2 else t1;
        newEFSMmax = replace_all new [t1ID, t2ID] maxT in
      \<comment> \<open>Most of the time, we'll want the transition with the most updates so start with that one\<close>
      if satisfies (set log) (tm newEFSMmax) then
        Some newEFSMmax
      else
        \<comment> \<open>There may be other occasions where we want to try the other transition\<close>
        \<comment> \<open>e.g. if their updates are equal but one has a different guard\<close>
        let newEFSMmin = replace_all new [t1ID, t2ID] minT in
        if satisfies (set log) (tm newEFSMmin) then
          Some newEFSMmin
        else
          None
     else
      None
   )"

end