subsection \<open>Contexts\<close>
text\<open>
This theory defines contexts as a way of relating possible constraints on register values to
observable output. We then use contexts to extend the idea of transition subsumption to EFSM
transitions with register update functions.
\<close>

theory Contexts
  imports
    EFSM GExp
begin

definition can_take :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" where
  "can_take t i r = apply_guards (Guard t) (join_ir i r)"

definition medial :: "datastate \<Rightarrow> transition \<Rightarrow> bool" where
  "medial c t = apply_guards (Guard t) c"

definition strip_inputs :: "datastate \<Rightarrow> registers" where
  "strip_inputs d = (\<lambda>r. d (R r))"

definition posterior :: "transition \<Rightarrow> datastate \<Rightarrow> registers option" where
  "posterior t d = (if medial d t then Some (apply_updates (Updates t) d (strip_inputs d)) else None)"

definition subsumes :: "transition \<Rightarrow> datastate \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes t2 c t1 = (medial c t1 \<longrightarrow> medial c t2 \<and>
                       medial c t1 \<longrightarrow> apply_outputs (Outputs t1) c = apply_outputs (Outputs t2) c \<and>
                       (\<exists>p1 p2. posterior t2 c = Some p1 \<and> posterior t2 c = Some p2 \<longrightarrow> (\<forall>P. P p1 \<longrightarrow> P p2)) \<and> 
                       (\<exists>p1 p2. posterior t2 c = Some p1 \<longrightarrow> posterior t2 c = Some p2))"

lemma transition_subsumes_self: "subsumes t c t"
  apply (simp add: subsumes_def)
  by auto

primrec posterior_sequence :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> registers option" where
  "posterior_sequence _ _ r [] = Some r" |
  "posterior_sequence e s r (a#t) = (case step e s r (fst a) (snd a) of
                                            None \<Rightarrow> None |
                                            Some (_, s', _, r') \<Rightarrow> posterior_sequence e s' r' t
                                         )"

abbreviation anterior_context :: "transition_matrix \<Rightarrow> trace \<Rightarrow> registers option" where
  "anterior_context e t \<equiv> posterior_sequence e 0 <> t"

lemma posterior_sequence_accepts: "\<forall>s d. posterior_sequence e s d t = Some ca \<longrightarrow> accepts e s d t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply simp
     apply (case_tac "step e s d (fst a) (snd a)")
     apply simp
    apply (case_tac aa)
    apply simp
    apply (rule accepts.step)
     apply simp
    by simp
qed

lemma anterior_context_accepts: "\<exists>c. anterior_context e p = Some c \<Longrightarrow> accepts_trace e p"
  using posterior_sequence_accepts
  by auto

lemma accepts_gives_context: "\<forall>s d. accepts e s d t \<longrightarrow> (\<exists>c. posterior_sequence e s d t = Some c)"
proof(induct t)
case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply simp
     apply (case_tac "step e s d (fst a) (snd a)")
     apply simp
     apply (simp add: conditions_inaccepts)
    apply simp
    apply (case_tac aa)
    apply simp
    using inaccepts_future_inaccepts by blast
qed

lemma accepts_trace_gives_context: "accepts_trace e p \<Longrightarrow> (\<exists>c. anterior_context e p = Some c)"
  using accepts_gives_context by auto

end
