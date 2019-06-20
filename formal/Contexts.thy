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

declare gval.simps [simp]
declare ValueEq_def [simp]

definition can_take :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" where
  "can_take t i r = (length i = Arity t \<and> apply_guards (Guard t) (join_ir i r))"

lemma enumerate_gexp_regs_set_reg_unconstrained:
  "\<forall>x\<in>set G. enumerate_gexp_regs x = {} \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r))"
  by (simp add: enumerate_gexp_regs_empty_reg_unconstrained)

lemma enumerate_gexp_inputs_set_input_unconstrained:
  "\<forall>x\<in>set G. enumerate_gexp_inputs x = {} \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (I r))"
  by (simp add: enumerate_gexp_inputs_empty_input_unconstrained)

lemma unconstrained_variable_swap: "\<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (I r)) \<Longrightarrow>
       \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r)) \<Longrightarrow>
       apply_guards G (join_ir i r) = apply_guards G (join_ir i' r')"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    unfolding apply_guards_def
    apply simp
    by (metis input_unconstrained_gval_input_swap register_unconstrained_gval_register_swap)
qed

lemma unconstrained_variable_swap_apply_guards:
  "\<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (I r)) \<Longrightarrow>
   \<forall>r. \<forall>g\<in>set G. \<not> gexp_constrains g (V (R r)) \<Longrightarrow>
   gval (foldr gAnd G (Bc True)) s = true \<Longrightarrow>
   apply_guards G s'"
proof(induct G)
  case Nil
  then show ?case
    by (simp add: apply_guards_def)
next
  case (Cons a G)
  then show ?case
    apply (simp only: foldr.simps comp_def gval_gAnd maybe_and_true apply_guards_cons)
    apply simp
    by (metis unconstrained_variable_swap_gval)
qed

lemma "max_reg t = None \<Longrightarrow> valid_transition t \<Longrightarrow> satisfiable (foldr gAnd (Guard t) (Bc True)) \<Longrightarrow> \<exists>i. can_take t i r"
  apply (simp add: max_reg_def valid_transition_def max_input_def)
  apply (case_tac "enumerate_registers t = {}")
  defer
   apply simp
  apply simp
  apply (case_tac "enumerate_inputs t = {}")
   apply (simp add: can_take_def satisfiable_def)
  using enumerate_gexp_inputs_set_input_unconstrained[of "Guard t"]
        enumerate_gexp_regs_set_reg_unconstrained[of "Guard t"]
   apply (simp add: enumerate_registers_def enumerate_inputs_def)
   apply clarify
   apply (simp add: unconstrained_variable_swap_apply_guards)
  apply (simp add: can_take_def satisfiable_def)



lemma medial_subset: "length i = Arity t \<Longrightarrow>
                      Arity t = Arity t' \<Longrightarrow>
                      set (Guard t') \<subseteq> set (Guard t) \<Longrightarrow> can_take t i r \<longrightarrow> can_take t' i r"
  by (simp add: can_take_def apply_guards_subset)

definition d2r :: "datastate \<Rightarrow> registers" where
  "d2r d = (\<lambda>r. d (R r))"

lemma d2r_keeps_regs_same [simp]: "d2r c r = c (R r)"
  by (simp add: d2r_def)

definition posterior :: "transition \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> registers option" where
  "posterior t i r = (if can_take t i r then Some (apply_updates (Updates t) (join_ir i r) r) else None)"

definition r2d :: "registers \<Rightarrow> datastate" where
  "r2d regs = (\<lambda>i. case i of R r \<Rightarrow> regs r | _ \<Rightarrow> None)"

definition subsumes :: "transition \<Rightarrow> registers \<Rightarrow> transition \<Rightarrow> bool" where
  "subsumes t2 r t1 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and>
                       (\<forall>i. can_take t1 i r \<longrightarrow> can_take t2 i r) \<and>
                       (\<forall>i. can_take t1 i r \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<and>
                       (\<forall>p1 p2 i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1 \<longrightarrow> (\<forall>P r'. (p1 r' = None) \<or> (P (p2 r') \<longrightarrow> P (p1 r')))) \<and>
                       (\<forall>p1 p2 i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1 \<longrightarrow> (\<forall>r. p1 r \<noteq> None \<longrightarrow>  p2 r \<noteq> None))
                      )"

lemma subsumption: 
  "(Label t1 = Label t2 \<and> Arity t1 = Arity t2) \<Longrightarrow>
   (\<forall>i. can_take t1 i r \<longrightarrow> can_take t2 i r) \<Longrightarrow>
   (\<forall>i. can_take t1 i r \<longrightarrow> apply_outputs (Outputs t1) (join_ir i r) = apply_outputs (Outputs t2) (join_ir i r)) \<Longrightarrow>
   (\<forall>p1 p2 i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1 \<longrightarrow> (\<forall>P r'. (p1 r' = None) \<or> (P (p2 r') \<longrightarrow> P (p1 r')))) \<Longrightarrow>
   (\<forall>p1 p2 i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1 \<longrightarrow> (\<forall>r. p1 r \<noteq> None \<longrightarrow>  p2 r \<noteq> None)) \<Longrightarrow>
   subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma bad_guards: "\<exists>i. can_take t1 i r \<and> \<not> can_take t2 i r \<Longrightarrow> \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma inconsistent_updates: "\<exists>p1 p2. (\<exists>i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1) \<and> (\<exists>r. (\<exists>y. p1 r = Some y) \<and> p2 r = None) \<Longrightarrow>
 \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma inconsistent_updates2: "\<exists>p1 p2. (\<exists>i. posterior t2 i r = Some p2 \<and> posterior t1 i r = Some p1) \<and> (\<exists>P r'. P (p2 r') \<and> (\<exists>y. p1 r' = Some y) \<and> \<not> P (p1 r')) \<Longrightarrow>
 \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

lemma bad_outputs: "\<exists>i. can_take t1 i r \<and> apply_outputs (Outputs t1) (join_ir i r) \<noteq> apply_outputs (Outputs t2) (join_ir i r) \<Longrightarrow>
 \<not> subsumes t2 r t1"
  by (simp add: subsumes_def)

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

lemma accepts_trace_anterior_not_none: "accepts_trace e p \<Longrightarrow> anterior_context e p \<noteq> None"
  using accepts_trace_gives_context by blast
end
