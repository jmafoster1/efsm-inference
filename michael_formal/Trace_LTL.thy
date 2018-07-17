theory Trace_LTL
  imports EFSM Filesystem "Coinductive.Coinductive_Stream"
begin

type_synonym property = "statename \<Rightarrow> datastate \<Rightarrow> outputs \<Rightarrow> event \<Rightarrow> bool"
type_synonym operator = "efsm \<Rightarrow> statename \<Rightarrow> datastate \<Rightarrow> outputs \<Rightarrow> event stream \<Rightarrow> property \<Rightarrow> bool"

definition "next" :: operator where
  "next e s d p t f = (case step e s d (fst (shd t)) (snd (shd t)) of
    None \<Rightarrow> False |
    Some (s', o', d') \<Rightarrow> f s' d' o' (shd (stl t))
  )"

coinductive globally :: operator where
  C_always: "f s d p (shd t) \<Longrightarrow> step e s d (fst (shd t)) (snd (shd t)) = Some (s', o', d') \<Longrightarrow> globally e s' d' o' (stl t) f \<Longrightarrow> globally e s d p t f"

inductive eventually :: operator where
  ev_h: "f s d p (shd t) \<Longrightarrow> eventually e s d p t f" |
  ev_t: "step e s d (fst (shd t)) (snd (shd t)) = Some (s', o', d') \<and> eventually e s' d' o' (stl t) f \<Longrightarrow> eventually e s d p t f"

inductive Until :: "efsm \<Rightarrow> statename \<Rightarrow> datastate \<Rightarrow> outputs \<Rightarrow> event stream \<Rightarrow> property \<Rightarrow> property \<Rightarrow> bool" where
  until_h: "f' s d p (shd t) \<Longrightarrow> Until e s d p t f f'" |
  until_t: "f s d p (shd t) \<Longrightarrow> step e s d (fst (shd t)) (snd (shd t)) = Some (s', o', d') \<and> Until e s' d' o' (stl t) f f' \<Longrightarrow> Until e s d p t f f'"

lemma "Until filesystem 1 <> [] t (\<lambda>s d p (l, i). s = 1) (\<lambda>s d p (l, i). l=''login'')"
proof (induction t)
case (1 y)
  then show ?case
apply simp
qed
  
end