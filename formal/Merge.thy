theory Merge
imports EFSM Traces
begin

(* This is a simple union of transitions. It does *not* preserve deteminism! *)
definition state_merge :: "transition_matrix \<Rightarrow> state \<Rightarrow> state \<Rightarrow> transition_matrix" where
"state_merge M s1 s2 \<equiv> 
    \<lambda>(s,s') . if s = s1 \<or> s = s2 then M(s1,s') \<union> M(s2,s')
              else if s' = s1 \<or> s' = s2 then M(s,s1) \<union> M(s,s2)
              else M(s,s')"



end
