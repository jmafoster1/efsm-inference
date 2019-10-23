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

definition can_take :: "nat \<Rightarrow> gexp list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" where
  "can_take a g i r = (length i = a \<and> apply_guards g (join_ir i r))"

lemma can_take_subset_append: "set (Guard t) \<subseteq> set (Guard t') \<Longrightarrow> can_take a (Guard t @ Guard t') i c = can_take a (Guard t') i c"
  by (simp add: apply_guards_subset_append can_take_def)

definition "can_take_transition t i r = can_take (Arity t) (Guard t) i r"

lemma can_take_transition_empty_guard: "Guard t = [] \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def Ex_list_of_length)

lemma valid_list_can_take: "\<forall>g \<in> set (Guard t). valid g \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def apply_guards_def valid_def Ex_list_of_length)

lemma cant_take_if: "\<exists>g \<in> set (Guard t). gval g (join_ir i r) \<noteq> true \<Longrightarrow> \<not> can_take_transition t i r"
  using apply_guards_cons apply_guards_rearrange can_take_def can_take_transition_def by blast

lemma medial_subset:
  "length i = Arity t \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   set (Guard t') \<subseteq> set (Guard t) \<Longrightarrow>
   can_take_transition t i r \<Longrightarrow>
   can_take_transition t' i r"
  by (simp add: can_take_transition_def can_take_def apply_guards_subset)

definition posterior_separate :: "nat \<Rightarrow> gexp list \<Rightarrow> update_function list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior_separate a g u i r = (if can_take a g i r then Some (apply_updates u (join_ir i r) r) else None)"

definition posterior :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior t i r = posterior_separate (Arity t) (Guard t) (Updates t) i r"

definition r2d :: "registers \<Rightarrow> datastate" where
  "r2d regs = (\<lambda>i. case i of R r \<Rightarrow> regs $ r | _ \<Rightarrow> None)"

definition subsumes :: "transition \<Rightarrow> registers \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes t2 r t1 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<and>
                       (\<forall>i. can_take_transition t1 i r \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                       (\<forall>p1 p2 i. posterior_separate (Arity t2) ((Guard t2)@(Guard t1)) (Updates t2) i r = Some p2 \<and>
                                  posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1 \<longrightarrow>
                                  (\<forall>P r'. (p1 $ r' = None) \<or> (P (p2 $ r') \<longrightarrow> P (p1 $ r')))) \<and>
                       (\<forall>p1 p2 i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1 \<longrightarrow> (\<forall>r. p1 $ r \<noteq> None \<longrightarrow>  p2 $ r \<noteq> None))
                      )"

lemma subsumption: 
  "(Label t1 = Label t2 \<and> Arity t1 = Arity t2) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow> can_take_transition t2 i r) \<Longrightarrow>
   (\<forall>i. can_take_transition t1 i r \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<Longrightarrow>
   (\<forall>p1 p2 i. posterior_separate (Arity t2) ((Guard t2)@(Guard t1)) (Updates t2) i r = Some p2 \<and>
                                  posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1 \<longrightarrow>
                                  (\<forall>P r'. (p1 $ r' = None) \<or> (P (p2 $ r') \<longrightarrow> P (p1 $ r')))) \<Longrightarrow>
   (\<forall>p1 p2 i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1 \<longrightarrow> (\<forall>r. p1 $ r \<noteq> None \<longrightarrow>  p2 $ r \<noteq> None)) \<Longrightarrow>
   subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma bad_guards:
  "\<exists>i. can_take_transition t1 i r \<and> \<not> can_take_transition t2 i r \<Longrightarrow>
   \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma inconsistent_updates:
  "\<exists>p1 p2. (\<exists>i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1) \<and>
           (\<exists>r. (\<exists>y. p1 $ r = Some y) \<and> p2 $ r = None) \<Longrightarrow>
   \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma inconsistent_updates2:
  "\<exists>p1 p2. (\<exists>i. posterior_separate (Arity t2) (Guard t2 @ Guard t1) (Updates t2) i r = Some p2 \<and>
                posterior_separate (Arity t1) (Guard t1) (Updates t1) i r = Some p1) \<and>
           (\<exists>P r'. P (p2 $ r') \<and> (\<exists>y. p1 $ r' = Some y) \<and> \<not> P (p1 $ r')) \<Longrightarrow>
    \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma bad_outputs: "\<exists>i. can_take_transition t1 i r \<and> apply_outputs (Outputs t1) (join_ir i r) \<noteq> apply_outputs (Outputs t2) (join_ir i r) \<Longrightarrow>
 \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma transition_subsumes_self: "subsumes t c t"
  apply (simp add: subsumes_def)
  using posterior_separate_def by auto

definition posterior_sequence :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> registers option" where
  "posterior_sequence e s r t = (case accepting_sequence e s r t [] of
    None \<Rightarrow> None
    | Some seq \<Rightarrow>
      if seq = [] then
        Some r
      else let
        (_, _, _, r') = last seq in Some r'
  )"

abbreviation anterior_context :: "transition_matrix \<Rightarrow> trace \<Rightarrow> registers option" where
  "anterior_context e t \<equiv> posterior_sequence e 0 <> t"

lemma anterior_context_empty: "anterior_context e [] = Some <>"
  by (simp add: posterior_sequence_def)

lemma accepting_sequence_length_aux: "\<forall>s d seq. accepting_sequence e s d t seq = Some seq' \<longrightarrow> length seq' \<ge> length seq"
proof(induct t)
  case Nil
  then show ?case
    by auto
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (simp add: Let_def)
    apply (case_tac "ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir (snd a) d) d) t)
         (possible_steps e s d (fst a) (snd a)) =
        {||}")
     apply simp
    apply simp
    apply (case_tac "SOME x.
             x |\<in>| possible_steps e s d (fst a) (snd a) \<and>
             (case x of (s', T) \<Rightarrow> accepts e s' (apply_updates (Updates T) (join_ir (snd a) d) d) t)")
    apply (simp add: Let_def)
    by fastforce
qed

lemma accepting_sequence_length: "accepting_sequence e s d t seq = Some seq' \<Longrightarrow> length seq' \<ge> length seq"
  by (simp add: accepting_sequence_length_aux)

lemma posterior_sequence_implies_accepting_sequence: "(posterior_sequence e s d t = Some ca) \<Longrightarrow> (accepting_sequence e s d t [] \<noteq> None)"
  apply (simp add: posterior_sequence_def)
  apply (case_tac "accepting_sequence e s d t []")
   apply simp
  by simp

lemma accepting_sequence_accepts: "\<forall>d. accepting_sequence e s d t [] = Some y \<longrightarrow> accepts e s d t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (simp add: Let_def)
    apply (case_tac "ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir (snd a) d) d) t)
         (possible_steps e s d (fst a) (snd a)) =
        {||}")
     apply simp
    apply simp
    apply (case_tac "SOME x.
             x |\<in>| possible_steps e s d (fst a) (snd a) \<and>
             (case x of (s', T) \<Rightarrow> accepts e s' (apply_updates (Updates T) (join_ir (snd a) d) d) t)")
    apply (simp add: Let_def)
    apply (case_tac a)
    apply simp
    apply (rule accepts.step)
    by fastforce
qed

lemma posterior_sequence_accepts: "posterior_sequence e s d t = Some ca \<longrightarrow> accepts e s d t"
  using posterior_sequence_implies_accepting_sequence[of e s d t ca]
  apply simp
  apply clarify
  apply simp
  using accepting_sequence_accepts
  by auto

lemma anterior_context_accepts: "\<exists>c. anterior_context e p = Some c \<Longrightarrow> accepts_trace e p"
  using posterior_sequence_accepts by blast

lemma posterior_sequence_gives_accept: "posterior_sequence e s d t \<noteq> None \<Longrightarrow> accepts e s d t"
  using option.discI posterior_sequence_accepts by auto

lemma accepting_sequence_posterior_sequence_not_none:
  "accepting_sequence e s d t [] \<noteq> None \<Longrightarrow>
   posterior_sequence e s d t \<noteq> None"
  apply (simp add: posterior_sequence_def)
  apply (case_tac "accepting_sequence e s d t []")
   apply simp
  apply simp
  apply (case_tac "last a")
  by simp

lemma posterior_sequence_none_accepting_sequence_none: "(posterior_sequence e s d t = None) = (accepting_sequence e s d t [] = None)"
  apply standard
  using accepting_sequence_posterior_sequence_not_none apply blast
  by (simp add: posterior_sequence_def)

lemma rejects_gives_no_accepting_sequence: "\<forall>s d. \<not>accepts e s d t \<longrightarrow> accepting_sequence e s d t [] = None"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: accepts.base)
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (cases a)
    apply (simp only: trace_reject_2)
    apply (simp add: Let_def)
    apply (case_tac "SOME x.
                x |\<in>| possible_steps e s d aa b \<and>
                (case x of (s', T) \<Rightarrow> accepts e s' (apply_updates (Updates T) (join_ir b d) d) t)")
    apply simp
    by fastforce
qed

lemma rejects_gives_no_posterior_sequence: "\<not>accepts e s d t \<Longrightarrow> posterior_sequence e s d t = None"
  by (simp add: posterior_sequence_def rejects_gives_no_accepting_sequence)

lemma no_accepting_sequence_rejected: "\<forall>d s seq. accepting_sequence e s d t seq = None \<longrightarrow> \<not> accepts e s d t"
proof(induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (rule accepts.cases)
      apply simp
     apply simp
    apply clarify
    apply (simp add: Let_def)
    apply (case_tac "ffilter (\<lambda>(s', T). accepts e s' (apply_updates (Updates T) (join_ir i da) da) t) (possible_steps e sa da l i) = {||}")
     apply auto[1]
    apply simp
    apply (case_tac "SOME x.
                x |\<in>| possible_steps e sa da l i \<and>
                (case x of (s', T) \<Rightarrow> accepts e s' (apply_updates (Updates T) (join_ir i da) da) t)")
    apply (simp add: Let_def)
    by (metis (no_types, lifting) case_prodD case_prodI someI_ex)
qed

lemma no_posterior_sequence_reject: "posterior_sequence e s d t = None \<Longrightarrow> \<not>accepts e s d t"
  apply (simp add: posterior_sequence_none_accepting_sequence_none)
  using no_accepting_sequence_rejected
  by blast

lemma accepts_gives_context: "\<forall>s d. accepts e s d t \<longrightarrow> (\<exists>c. posterior_sequence e s d t = Some c)"
  using no_posterior_sequence_reject by blast

lemma accepts_trace_gives_context: "accepts_trace e p \<Longrightarrow> (\<exists>c. anterior_context e p = Some c)"
  using accepts_gives_context by auto

lemma accepts_trace_anterior_not_none: "accepts_trace e p \<Longrightarrow> anterior_context e p \<noteq> None"
  using accepts_trace_gives_context by blast

lemma "\<forall>s. apply_guards (Guard t2) s \<longrightarrow> apply_guards (Guard t1) s \<Longrightarrow>
       Label t1 = Label t2 \<Longrightarrow>
       Arity t1 = Arity t2 \<Longrightarrow>
       Outputs t1 = Outputs t2 \<Longrightarrow>
       Updates t1 = Updates t2 \<Longrightarrow>
       subsumes t1 c t2"
  apply (rule subsumption)
      apply simp
     apply (simp add: can_take_transition_def can_take_def)
    apply simp
   apply (simp add: posterior_separate_def can_take_def)
   apply auto[1]
  apply (simp add: posterior_def posterior_separate_def can_take_def)
  by auto

lemma no_choice_no_subsumption:
  "Label t = Label t' \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   \<not> choice t t' \<Longrightarrow>
   \<exists>i. can_take_transition t' i c \<Longrightarrow>
  \<not> subsumes t c t'"
  apply (rule bad_guards)
  apply (simp add: can_take_transition_def can_take_def)
  apply clarify
  apply (rule_tac x=i in exI)
  using choice_def by blast
end