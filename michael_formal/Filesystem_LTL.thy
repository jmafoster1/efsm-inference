theory Filesystem_LTL
  imports Filesystem "Coinductive.Coinductive_Stream"
begin
type_synonym state = "(statename \<times> datastate \<times> label \<times> inputs \<times> outputs)"
type_synonym property = "state \<Rightarrow> bool"
type_synonym operator = "property \<Rightarrow> state stream \<Rightarrow> bool"

abbreviation X :: operator where
  "X f s \<equiv> f (shd (stl s))"

abbreviation G :: operator where
  "G f s \<equiv> (\<forall>x\<in>sset s. f x)"

abbreviation F :: operator where
  "F f s \<equiv> (\<exists>x\<in>sset s. f x)"

inductive U :: "property \<Rightarrow> property \<Rightarrow> state stream \<Rightarrow> bool" where
  until_h: "f' (shd s) \<Longrightarrow> U f f' s" |
  until_t: "f (shd s) \<Longrightarrow> U f f' (stl s) \<Longrightarrow> U f f' s"

coinductive valid :: "state stream \<Rightarrow> efsm \<Rightarrow> bool" where
  valid_always: "step e s d l i \<noteq> None \<Longrightarrow> step e s d l i = Some (s', p, d') \<Longrightarrow> valid (SCons (s, d, l, i, p) (SCons (s', d', l', i', p') t)) e"

lemma valid_first_step: "step e s d l i = None \<Longrightarrow> \<not> valid (SCons (s, d, l, i, p) t) e"
  apply (rule ccontr)
  apply simp
  apply (rule valid.cases)
   apply simp
  by simp

lemma no_step: "\<forall>ad ae b. step e a aa ab ac \<noteq> Some (ad, ae, b) \<equiv> step e a aa ab ac = None"
  by (smt not_None_eq prod.collapse)

lemma some_step: "\<exists>y. step e a aa ab ac = Some y \<equiv> step e a aa ab ac \<noteq> None"
  by simp

lemma some_step_2: "\<exists>ad ae b. step e a aa ab ac = Some (ad, ae, b) \<equiv> step e a aa ab ac \<noteq> None"
  by simp

lemma "F f s \<Longrightarrow> f (shd s) \<or> F f (stl s)"
  by (metis insertE stream.exhaust_sel stream.set)

lemma globally_not_not_eventually_not: "G f s \<equiv> \<not> F (\<lambda>x. \<not> f x) s"
  by simp

lemma eventually_not_not_globally: "F (\<lambda>x. \<not> f x) s \<equiv> \<not> G f s"
  by simp

lemma some_not_none:  "step ea s d l i = Some (s', p, d') \<Longrightarrow> step ea s d l i \<noteq> None"
  by simp

lemma "valid t e \<Longrightarrow> step e s d l i = None \<Longrightarrow> \<forall>p. (s, d, l, i, p) \<notin> sset t"
  try

lemma "(a, aa, ab, ac, b) \<in> sset t \<Longrightarrow> step e a aa ab ac = None \<Longrightarrow> \<not> valid t e"
  apply (rule ccontr, simp)
  apply (rule valid.cases)
   apply simp
  apply simp
  apply auto


lemma "valid (SCons (s, d, l, i, p) t) e \<Longrightarrow> \<not> F (\<lambda> (s, d, l, i, p). step e s d l i = None) (SCons (s, d, l, i, p) t)"
  apply simp
  apply safe
  using no_step valid_first_step apply blast
  apply (simp only: some_step)
  apply (rule ccontr)
  apply (simp add: no_step)
  
  

lemma "valid s filesystem \<Longrightarrow> G (\<lambda>(s, d, l, i, p). s = 1 \<or> s = 2) s"
  apply (rule ccontr)
  apply simp

end