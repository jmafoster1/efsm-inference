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

coinductive valid_trace_aux :: "efsm \<Rightarrow> statename \<Rightarrow> datastate \<Rightarrow> event stream \<Rightarrow> bool" where
  C_always: "step e s d (fst (shd t)) (snd (shd t)) = Some (s', o', d') \<Longrightarrow> valid_trace_aux e s' d' (stl t) \<Longrightarrow> valid_trace_aux e s d t"

abbreviation valid_trace :: "efsm \<Rightarrow> event stream \<Rightarrow> bool" where
  "valid_trace e t \<equiv> valid_trace_aux e (s0 e) <> t"

lemma valid_first_step: "valid_trace e t \<Longrightarrow> step e (s0 e) <> (fst (shd t)) (snd (shd t)) \<noteq> None"
  apply simp
  apply (rule ccontr)
  apply simp
  by (meson valid_trace_aux.cases)

lemma valid_step: "valid_trace_aux e s d t \<Longrightarrow> step e s d (fst (shd t)) (snd (shd t)) \<noteq> None"
  apply simp
  apply (rule ccontr)
  apply simp
  using valid_trace_aux.simps by blast

lemma invalid_step: "step e s d (fst (shd t)) (snd (shd t)) = None \<Longrightarrow> \<not> valid_trace_aux e s d t"
  using valid_step by blast

lemma globally_true: "valid_trace_aux e s d t \<Longrightarrow> globally e s d p t (\<lambda> s d p e. True)"
proof (coinduction)
case globally
  then show ?case
    apply simp
    sorry
qed
  
end