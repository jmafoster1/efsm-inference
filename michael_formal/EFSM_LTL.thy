theory EFSM_LTL
imports EFSM Filesystem
begin

type_synonym property = "statename \<Rightarrow> datastate \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> statename \<Rightarrow> outputs \<Rightarrow> datastate \<Rightarrow> bool"
type_synonym operator =  "efsm \<Rightarrow> statename \<Rightarrow> datastate \<Rightarrow> property \<Rightarrow> bool"

function globally :: operator where
  "globally e s d f = (\<exists> l i d' s' o'. step e s d l i = Some (s', o', d') \<and> f s d l i s' o' d' \<and> globally e s' d' f)"
   apply auto[1]
  by simp

lemma "globally filesystem 1 <> (\<lambda> s d l i s' o' d'. True)"
  

end