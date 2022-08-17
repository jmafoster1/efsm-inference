section\<open>LTL for EFSMs\<close>
text\<open>This theory builds off the \texttt{Linear\_Temporal\_Logic\_on\_Streams} theory from the HOL
library and defines functions to ease the expression of LTL properties over EFSMs. Since the LTL
operators effectively act over traces of models we must find a way to express models as streams.\<close>

theory EFSM_LTL
imports "Extended_Finite_State_Machines.EFSM" "HOL-Library.Linear_Temporal_Logic_on_Streams"
begin

text_raw\<open>\snip{statedef}{1}{2}{%\<close>
record state =
  statename :: "nat option"
  datastate :: registers
  action :: action
  "output" :: outputs
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{whitebox}{1}{2}{%\<close>
type_synonym whitebox_trace = "state stream"
text_raw\<open>}%endsnip\<close>

type_synonym property = "whitebox_trace \<Rightarrow> bool"

abbreviation label :: "state \<Rightarrow> String.literal" where
  "label s \<equiv> fst (action s)"

abbreviation inputs :: "state \<Rightarrow> value list" where
  "inputs s \<equiv> snd (action s)"

text_raw\<open>\snip{ltlStep}{1}{2}{%\<close>
fun ltl_step :: "transition_matrix \<Rightarrow> cfstate option \<Rightarrow> registers \<Rightarrow> action \<Rightarrow> (nat option \<times> outputs \<times> registers)" where
  "ltl_step _ None r _ = (None, [], r)" |
  "ltl_step e (Some s) r (l, i) = (let possibilities = possible_steps e s r l i in
                   if possibilities = {||} then (None, [], r)
                   else
                     let (s', t) = Eps (\<lambda>x. x |\<in>| possibilities) in
                     (Some s', (evaluate_outputs t i r), (evaluate_updates t i r))
                  )"
text_raw\<open>}%endsnip\<close>

lemma ltl_step_singleton:
"\<exists>t. possible_steps e n r (fst v) (snd v) = {|(aa, t)|} \<and> evaluate_outputs t (snd v) r  = b \<and> evaluate_updates t (snd v) r = c\<Longrightarrow>
ltl_step e (Some n) r v = (Some aa, b, c)"
  apply (cases v)
  by auto

lemma ltl_step_none: "possible_steps e s r a b = {||} \<Longrightarrow> ltl_step e (Some s) r (a, b) = (None, [], r)"
  by simp

lemma ltl_step_none_2: "possible_steps e s r (fst ie) (snd ie) = {||} \<Longrightarrow> ltl_step e (Some s) r ie = (None, [], r)"
  by (metis ltl_step_none prod.exhaust_sel)

lemma ltl_step_alt: "ltl_step e (Some s) r t = (
  let possibilities = possible_steps e s r (fst t) (snd t) in
  if possibilities = {||} then
    (None, [], r)
  else
  let (s', t') = Eps (\<lambda>x. x |\<in>| possibilities) in
  (Some s', (apply_outputs (Outputs t') (join_ir (snd t) r)), (apply_updates (Updates t') (join_ir (snd t) r) r))
)"
  by (case_tac t, simp add: Let_def)

lemma ltl_step_some:
  assumes "possible_steps e s r l i = {|(s', t)|}"
      and "evaluate_outputs t i r = p"
      and "evaluate_updates t i r = r'"
    shows "ltl_step e (Some s) r (l, i) = (Some s', p, r')"
  by (simp add: assms)

lemma ltl_step_cases:
  assumes invalid: "P (None, [], r)"
      and valid: "\<forall>(s', t) |\<in>| (possible_steps e s r l i). P (Some s', (evaluate_outputs t i r), (evaluate_updates t i r))"
    shows "P (ltl_step e (Some s) r (l, i))"
  apply simp
  apply (case_tac "possible_steps e s r l i")
   apply (simp add: invalid)
  apply simp
  subgoal for x S'
    apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
    apply simp
    apply (insert assms(2))
    apply (simp add: fBall_def Ball_def fmember_def)
    by (metis (mono_tags, lifting) fst_conv prod.case_eq_if snd_conv someI_ex)
  done

text\<open>The \texttt{make\_full\_observation} function behaves similarly to \texttt{observe\_execution}
from the \texttt{EFSM} theory. The main difference in behaviour is what is recorded. While the
observe execution function simply observes an execution of the EFSM to produce the corresponding
output for each action, the intention here is to record every detail of execution, including the
values of internal variables.

Thinking of each action as a step forward in time, there are five components which characterise
a given point in the execution of an EFSM. At each point, the model has a current control state and
data state. Each action has a label and some input parameters, and its execution may produce
some observableoutput. It is therefore sufficient to provide a stream of 5-tuples containing the
current control state, data state, the label and inputs of the action, and computed output. The
make full observation function can then be defined as in Figure 9.1, with an additional
function watch defined on top of this which starts the make full observation off in the
initial control state with the empty data state.

Careful inspection of the definition reveals another way that \texttt{make\_full\_observation}
differs from \texttt{observe\_execution}. Rather than taking a cfstate, it takes a cfstate option.
The reason for this is that we need to make our EFSM models complete. That is, we need them to be
able to respond to every action from every state like a DFA. If a model does not recognise a given
action in a given state, we cannot simply stop processing because we are working with necessarily
infinite traces. Since these traces are generated by observing action sequences, the make full
observation function must keep processing whether there is a viable transition or not.

To support this, the make full observation adds an implicit ``sink state'' to every EFSM it
processes by lifting control flow state indices from \texttt{nat} to \texttt{nat option} such that
state $n$ is seen as state \texttt{Some} $n$. The control flow state \texttt{None} represents a sink
state. If a model is unable to recognise a particular action from its current state, it moves into
the \texttt{None} state. From here, the behaviour is constant for the rest of the time --- the
control flow state remains None; the data state does not change, and no output is produced.\<close>

text_raw\<open>\snip{makeFullObservation}{1}{2}{%\<close>
primcorec make_full_observation :: "transition_matrix \<Rightarrow> cfstate option \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> action stream \<Rightarrow> whitebox_trace" where
  "make_full_observation e s d p i = (
    let (s', o', d') = ltl_step e s d (shd i) in
    \<lparr>statename = s, datastate = d, action=(shd i), output = p\<rparr>##(make_full_observation e s' d' o' (stl i))
  )"
text_raw\<open>}%endsnip\<close>

lemma make_full_observation_step: "make_full_observation e s d p (h##t) = (
    let (s', o', d') = ltl_step e s d h in
    \<lparr>statename = s, datastate = d, action=h, output = p\<rparr>##(make_full_observation e s' d' o' t))"
  by (simp add: make_full_observation.ctr[of e s d p "h##t"])

lemma make_full_observation_none: "make_full_observation e None r p (x##xs) = \<lparr>statename=None, datastate=r, action=x, output = p\<rparr>##(make_full_observation e None r [] xs)"
  by (simp add: make_full_observation_step)

text_raw\<open>\snip{watch}{1}{2}{%\<close>
abbreviation watch :: "transition_matrix \<Rightarrow> action stream \<Rightarrow> whitebox_trace" where
  "watch e i \<equiv> (make_full_observation e (Some 0) <> [] i)"
text_raw\<open>}%endsnip\<close>

subsection\<open>Expressing Properties\<close>
text\<open>In order to simplify the expression and understanding of properties, this theory defines a
number of named functions which can be used to express certain properties of EFSMs.\<close>

subsubsection\<open>State Equality\<close>
text\<open>The \textsc{state\_eq} takes a cfstate option representing a control flow state index and
returns true if this is the control flow state at the head of the full observation.\<close>

abbreviation state_eq :: "cfstate option \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
  "state_eq v s \<equiv> statename (shd s) = v"

lemma state_eq_holds: "state_eq s = holds (\<lambda>x. statename x = s)"
  apply (rule ext)
  by (simp add: holds_def)

lemma state_eq_None_not_Some: "state_eq None s \<Longrightarrow> \<not> state_eq (Some n) s"
  by simp

subsubsection\<open>Label Equality\<close>
text\<open>The \textsc{label\_eq} function takes a string and returns true if this is equal to the label
at the head of the full observation.\<close>

abbreviation "label_eq v s \<equiv> fst (action (shd s)) = (String.implode v)"

lemma watch_label: "label_eq l (watch e t) = (fst (shd t) = String.implode l)"
  by (simp add: )

subsubsection\<open>Input Equality\<close>
text\<open>The \textsc{input\_eq} function takes a value list and returns true if this is equal to the
input at the head of the full observation.\<close>

abbreviation "input_eq v s \<equiv> inputs (shd s) = v"

subsubsection\<open>Action Equality\<close>
text\<open>The \textsc{action\_eq} function takes a (label, value list) pair and returns true if this is
equal to the action at the head of the full observation. This effectively combines
\texttt{label\_eq} and \texttt{input\_eq} into one function.\<close>

abbreviation "action_eq e \<equiv> label_eq (fst e) aand input_eq (snd e)"

subsubsection\<open>Output Equality\<close>
text\<open>The \textsc{output\_eq} function takes a takes a value option list and returns true if this is
equal to the output at the head of the full observation.\<close>

abbreviation "output_eq v s \<equiv> output (shd s) = v"

text_raw\<open>\snip{ltlVName}{1}{2}{%\<close>
datatype ltl_vname = Ip nat | Op nat | Rg nat
text_raw\<open>}%endsnip\<close>

subsubsection\<open>Checking Arbitrary Expressions\<close>
text\<open>The \textsc{check\_exp} function takes a guard expression and returns true if the guard
expression evaluates to true in the given state.\<close>

type_synonym ltl_gexp = "ltl_vname gexp"

definition join_iro :: "value list \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> ltl_vname datastate" where
  "join_iro i r p = (\<lambda>x. case x of
    Rg n \<Rightarrow> r $r n |
    Ip n \<Rightarrow> Some (i ! n) |
    Op n \<Rightarrow> p ! n
  )"

lemma join_iro_R [simp]: "join_iro i r p (Rg n) = r $r n"
  by (simp add: join_iro_def)

abbreviation "check_exp g s \<equiv> (gval g (join_iro (snd (action (shd s))) (datastate (shd s)) (output (shd s))) = trilean.true)"

lemma alw_ev: "alw f = not (ev (\<lambda>s. \<not>f s))"
  by simp

lemma alw_state_eq_smap:
  "alw (state_eq s) ss = alw (\<lambda>ss. shd ss = s) (smap statename ss)"
  apply standard
   apply (simp add: alw_iff_sdrop )
  by (simp add: alw_mono alw_smap )

lemma alw_output_eq_smap:
  "alw (output_eq s) ss = alw (\<lambda>ss. shd ss = s) (smap output ss)"
  apply standard
   apply (simp add: alw_iff_sdrop )
  by (simp add: alw_mono alw_smap )

subsection\<open>Sink State\<close>
text\<open>Once the sink state is entered, it cannot be left and there are no outputs or updates
henceforth.\<close>

lemma shd_state_is_none: "(state_eq None) (make_full_observation e None r p t)"
  by (simp add: )

lemma unfold_observe_none: "make_full_observation e None d p t = (\<lparr>statename = None, datastate = d, action=(shd t), output = p\<rparr>##(make_full_observation e None d [] (stl t)))"
  by (simp add: stream.expand)

lemma once_none_always_none_aux:
  assumes "\<exists> p r i. j = (make_full_observation e None r p) i"
  shows "alw (state_eq None) j"
  using assms apply coinduct
  apply simp
  by fastforce

lemma once_none_always_none: "alw (state_eq None) (make_full_observation e None r p t)"
  using once_none_always_none_aux by blast

lemma once_none_nxt_always_none: "alw (nxt (state_eq None)) (make_full_observation e None r p t)"
  using once_none_always_none
  by (simp add: alw_iff_sdrop del: sdrop.simps)

lemma snth_sconst: "(\<forall>i. s !! i = h) = (s = sconst h)"
  by (auto simp add: sconst_alt sset_range)

lemma alw_sconst: "(alw (\<lambda>xs. shd xs = h) t) = (t = sconst h)"
  by (simp add: snth_sconst[symmetric] alw_iff_sdrop)

lemma smap_statename_None: "smap statename (make_full_observation e None r p i) = sconst None"
  by (meson EFSM_LTL.alw_sconst alw_state_eq_smap once_none_always_none)

lemma alw_not_some: "alw (\<lambda>xs. statename (shd xs) \<noteq> Some s) (make_full_observation e None r p t)"
  by (metis (mono_tags, lifting) alw_mono once_none_always_none option.distinct(1) )

lemma state_none: "((state_eq None) impl nxt (state_eq None)) (make_full_observation e s r p t)"
  by (simp add: )

lemma state_none_2:
  "(state_eq None) (make_full_observation e s r p t) \<Longrightarrow>
   (state_eq None) (make_full_observation e s r p (stl t))"
  by (simp add: )

lemma no_output_none_aux:
  assumes "\<exists> p r i. j = (make_full_observation e None r []) i"
  shows "alw (output_eq []) j"
  using assms apply coinduct
  apply simp
  by fastforce

lemma no_output_none: "nxt (alw (output_eq [])) (make_full_observation e None r p t)"
  using no_output_none_aux by auto

lemma nxt_alw: "nxt (alw P) s \<Longrightarrow> alw (nxt P) s"
  by (simp add: alw_iff_sdrop)

lemma no_output_none_nxt: "alw (nxt (output_eq [])) (make_full_observation e None r p t)"
  using nxt_alw no_output_none by blast

lemma no_output_none_if_empty: "alw (output_eq []) (make_full_observation e None r [] t)"
  by (metis (mono_tags, lifting) alw_nxt make_full_observation.simps(1) no_output_none state.select_convs(4))

lemma smap_output_None: "smap output (make_full_observation e None r [] i) = sconst []"
  by (meson EFSM_LTL.alw_sconst alw_output_eq_smap no_output_none_if_empty)

lemma no_updates_none_aux:
  assumes "\<exists> p i. j = (make_full_observation e None r p) i"
  shows "alw (\<lambda>x. datastate (shd x) = r) j"
  using assms apply coinduct
  by fastforce

lemma no_updates_none: "alw (\<lambda>x. datastate (shd x) = r) (make_full_observation e None r p t)"
  using no_updates_none_aux by blast

lemma smap_datastate_None: "smap datastate (make_full_observation e None r p i) = sconst r"
  apply (simp add: alw_sconst[symmetric])
  by (metis (mono_tags, lifting) alw_iff_sdrop no_updates_none sdrop_smap stream.map_sel(1))

lemma action_components: "(label_eq l aand input_eq i) s = (action (shd s) = (String.implode l, i))"
  by (metis fst_conv prod.collapse snd_conv)

coinductive valid_trace :: "transition_matrix \<Rightarrow> cfstate option \<Rightarrow> registers \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
step_some: "\<exists>(s', tr) |\<in>| possible_steps e s r l i.
              evaluate_outputs tr i r = (output (shd t)) \<and>
              Some s' = (statename (shd t)) \<and>
              evaluate_updates tr i r = (datastate (shd t)) \<and>
              valid_trace e (Some s') (evaluate_updates tr i r) t \<Longrightarrow>
        valid_trace e (Some s) r (\<lparr>statename=Some s, datastate = r, action=(l, i), output = p\<rparr>##t)" |
step_none: "possible_steps e s r l i = {||} \<Longrightarrow> [] = (output (shd t)) \<Longrightarrow> valid_trace e None r t \<Longrightarrow> valid_trace e (Some s) r (\<lparr>statename=Some s, datastate = r, action=(l, i), output = p\<rparr>##t)" |
base [simp]: "smap (\<lambda>x. (statename x, datastate x, output x)) t = sconst (None, r, []) \<Longrightarrow> valid_trace e None r t"

inductive valid_prefix :: "transition_matrix \<Rightarrow> cfstate option \<Rightarrow> registers \<Rightarrow> state list \<Rightarrow> bool" where
step_some: "\<exists>(s', tr) |\<in>| possible_steps e s r l i. (t = [] \<or> evaluate_outputs tr i r = (output (hd t)) \<and>
              Some s' = (statename (hd t)) \<and>
              evaluate_updates tr i r = (datastate (hd t))) \<and>
                valid_prefix e (Some s') (evaluate_updates tr i r) t \<Longrightarrow>
            valid_prefix e (Some s) r (\<lparr>statename=Some s, datastate = r, action=(l, i), output = p\<rparr>#t)" |
step_none: "possible_steps e s r l i = {||} \<Longrightarrow>
            t = [] \<or> [] = (output (hd t)) \<Longrightarrow>
            valid_prefix e None r t \<Longrightarrow>
            valid_prefix e (Some s) r (\<lparr>statename=Some s, datastate = r, action=(l, i), output = p\<rparr>#t)" |
base [simp]: "valid_prefix e s r []"

lemma shd_exI: "\<exists>h t. P (h##t) \<Longrightarrow> \<exists>t. P t"
  by auto

lemma state_exI: "\<exists>s r l i p. P \<lparr>statename=s, datastate = r, action=(l, i), output = p\<rparr> \<Longrightarrow> \<exists>h. P h"
  by auto

lemma fempty: "(X = {||}) = (\<nexists>x. x |\<in>| X)"
  by simp

lemma always_invalid_step: "\<exists>l. possible_steps e s r l i = {||}"
  apply (simp add: possible_steps_def)
  apply (simp only: fempty ffmember_filter)
  apply simp
  apply (insert ex_new_if_finite[of "fset (fimage (Label \<circ> snd) e)"])
  apply (simp add: infinite_literal)
  by (metis (mono_tags, lifting) fmember_implies_member image_iff snd_conv)

lemma always_valid_trace: "\<exists>t. valid_trace e s r t"
  apply (rule shd_exI)
  apply (rule state_exI)
  apply (rule_tac x=s in exI)
  apply (rule_tac x=r in exI)
  apply (case_tac s)
   apply simp
   apply (rule_tac x=l in exI)
   apply (rule_tac x=i in exI)
   apply (rule_tac x="[]" in exI)
   apply (rule_tac x="sconst \<lparr>statename=None, datastate = r, action=(l, i), output = []\<rparr>" in exI)
   apply (rule valid_trace.base)
   apply (metis (no_types, lifting) id_apply siterate.code smap_sconst state.select_convs(1) state.select_convs(2) state.select_convs(4))
  subgoal for s
    apply simp
    apply (insert always_invalid_step[of e s r i])
    apply (erule exE)
    apply (rule_tac x=l in exI)
    apply (rule_tac x=i in exI)
    apply (rule_tac x="[]" in exI)
    apply (rule_tac x="sconst \<lparr>statename=None, datastate = r, action=a, output = []\<rparr>" in exI)
    apply (rule valid_trace.step_none)
      apply simp
     apply simp
    apply (rule valid_trace.base)
    by (metis (no_types, lifting) smap_sconst state.select_convs(1) state.select_convs(2) state.select_convs(4))
  done

lemma always_valid_trace_output: "\<exists>t. Some s = statename (shd t) \<and> evaluate_outputs b i r = output (shd t) \<and> evaluate_updates b i r = datastate (shd t) \<and> valid_trace e (Some s) (evaluate_updates b i r) t"
  apply (insert always_valid_trace[of e "Some s" "(evaluate_updates b i r)"])
  apply clarify
  apply (rule valid_trace.cases)
  apply simp
    apply (rule_tac x="(shd t)\<lparr>output := evaluate_outputs b i r\<rparr>##(stl t)" in exI, simp add: valid_trace.step_some)
   apply (rule_tac x="(shd t)\<lparr>output := evaluate_outputs b i r\<rparr>##(stl t)" in exI, simp add: valid_trace.step_none)
  by simp

lemma fmember_not_fempty: "x |\<in>| X \<Longrightarrow> X \<noteq> {||}"
  by auto

lemma ex_comm: "\<exists>t a b. P t a b = (\<exists>a b t. P t a b)"
  by blast

lemma ex_comm_back: "\<exists>a b t. P t a b \<Longrightarrow> \<exists>t a b. P t a b"
  by auto

lemma valid_prefix_append: "valid_prefix e s r (xs @ [x]) \<Longrightarrow> valid_prefix e s r xs"
  apply (induct xs arbitrary: s r)
   apply simp
  apply simp
  apply (rule valid_prefix.cases)
     apply simp
    apply clarsimp
    apply (rule valid_prefix.step_some)
    apply (rule_tac x="(aa, b)" in fBexI)
     apply (simp add: hd_append)
    apply simp
   apply (metis append_is_Nil_conv hd_append2 list.inject valid_prefix.step_none)
  by force

(*
  This shows that if a finite trace represents a valid execution of the model, then there is an
  infinite execution for which that finite trace is a prefix.
*)
lemma valid_prefix_ex_valid_trace: "valid_prefix e s r p \<Longrightarrow> \<exists>t. valid_trace e s r (shift p t)"
proof(induction p arbitrary: s r)
  case Nil
  then show ?case
    by (simp add: always_valid_trace)
next
  case (Cons a p)
  then show ?case
    apply (cases a)
    apply clarsimp
    apply (rule valid_prefix.cases)
       apply simp
      apply clarsimp
    subgoal for l i pa sa s' t
      apply (simp add: valid_trace.simps[of e "Some sa"])
      using always_valid_trace_output by blast
     apply clarsimp
    subgoal for l i pa sa
      apply (simp add: valid_trace.simps[of e "Some sa"])
      apply (cases p)
       apply simp
       apply (rule_tac x="sconst \<lparr>statename=None, datastate=r, action=(l, i), output = []\<rparr>" in exI)
       apply (simp add: smap_sconst)
      by simp
    by fastforce
qed

lemma scons_sconst: "xs = x##xs \<Longrightarrow> xs = sconst x"
  by (coinduction, metis id_apply siterate.simps(1) siterate.simps(2) stream.sel(1) stream.sel(2))

lemma smap_pair: "szip (smap f t) (smap g t) = smap (\<lambda>x. (f x, g x)) t"
  apply (coinduction arbitrary: t)
  by auto

lemma valid_trace_make_full_observation_None: "valid_trace e None r (make_full_observation e None r [] xs)"
  apply (rule valid_trace.base)
  apply (coinduction arbitrary: xs)
  by auto

lemma aux: "(\<exists>l i t.
           (\<exists>pa. make_full_observation e (Some s) r p xs =
                 \<lparr>statename = Some s, datastate = r, action = (l, i), output = pa\<rparr> ## t) \<and>
           (\<exists>(s', tr)|\<in>|possible_steps e s r l i.
               evaluate_outputs tr i r = output (shd t) \<and>
               Some s' = statename (shd t) \<and>
               evaluate_updates tr i r = datastate (shd t) \<and>
               ((\<exists>p xs. t = make_full_observation e (Some s') (evaluate_updates tr i r) p xs) \<or>
                valid_trace e (Some s') (evaluate_updates tr i r) t)) \<or>
           (\<exists>pa. make_full_observation e (Some s) r p xs =
                 \<lparr>statename = Some s, datastate = r, action = (l, i), output = pa\<rparr> ## t) \<and>
           possible_steps e s r l i = {||} \<and> [] = output (shd t) \<and> valid_trace e None r t) \<Longrightarrow>
(\<exists>l i t.
           (\<exists>pa. make_full_observation e (Some s) r p xs =
                 \<lparr>statename = Some s, datastate = r, action = (l, i), output = pa\<rparr> ## t) \<and>
           (\<exists>(s', tr)|\<in>|possible_steps e s r l i.
               evaluate_outputs tr i r = output (shd t) \<and>
               Some s' = statename (shd t) \<and>
               evaluate_updates tr i r = datastate (shd t) \<and>
               ((\<exists>p xs. t = make_full_observation e (Some s') (evaluate_updates tr i r) p xs) \<or>
                valid_trace e (Some s') (evaluate_updates tr i r) t))) \<or>
       (\<exists>l i t.
           (\<exists>pa. make_full_observation e (Some s) r p xs =
                 \<lparr>statename = Some s, datastate = r, action = (l, i), output = pa\<rparr> ## t) \<and>
           possible_steps e s r l i = {||} \<and> [] = output (shd t) \<and> valid_trace e None r t)"
  by blast

lemma valid_trace_Some:
  shows "valid_trace e (Some s) r (make_full_observation e (Some s) r p xs)"
  apply (coinduction arbitrary: s r p xs)
  apply simp
  subgoal for s r p xs
    apply (rule aux)
    apply (cases xs)
    apply (cases "(shd xs)")
    subgoal for x1 x2 l i
      apply (rule_tac x=l in exI)
      apply (rule_tac x=i in exI)
      apply (case_tac "possible_steps e s r l i = {||}")
       apply (simp add: make_full_observation_step)
      using valid_trace_make_full_observation_None apply presburger
      apply (simp add: make_full_observation_step)
      apply (cases "SOME x. x |\<in>| possible_steps e s r l i")
      apply simp
      apply (rule_tac x="(a, b)" in fBexI)
       apply blast
      by (metis ex_fin_conv someI)
    done
  done

lemma valid_trace_make_full_observation: "valid_trace e s r (make_full_observation e s r [] (smap action (t::state stream)))"
  by (metis (no_types, lifting) valid_trace_make_full_observation_None valid_trace_Some ltl_step.elims)

lemma valid_trace_smap_action_None: "valid_trace e None r t \<Longrightarrow> make_full_observation e None r [] (smap action t) = t"
  apply (coinduction arbitrary: t)
  apply (rule valid_trace.cases)
     apply simp
    apply simp
   apply simp
  apply simp
  by (metis (mono_tags, lifting) Pair_inject old.unit.exhaust siterate.simps(1) siterate.simps(2) state.surjective stream.map_id stream.map_sel(1) stream.map_sel(2) valid_trace.base)

lemma valid_watch_1_None: "(\<forall>t. \<phi> (make_full_observation e None r [] t)) \<Longrightarrow> (\<forall>t. valid_trace e None r t \<longrightarrow> \<phi> t)"
  apply standard
  subgoal for t
    apply (erule_tac x="smap action t" in allE)
    apply (rule impI)
    by (simp add: valid_trace_smap_action_None)
  done

lemma valid_trace_None:
  assumes "valid_trace e None r t"
    shows "smap statename t = sconst None"
      and "smap output t = sconst []"
      and "smap datastate t = sconst r"
  using assms apply (rule valid_trace.cases)
      apply simp
     apply simp
    apply (metis assms smap_statename_None valid_trace_smap_action_None)
  using assms apply (rule valid_trace.cases)
     apply simp
    apply simp
   apply (metis assms smap_output_None valid_trace_smap_action_None)
  using assms apply (rule valid_trace.cases)
    apply simp
   apply simp
  by (metis assms smap_datastate_None valid_trace_smap_action_None)

lemma valid_trace_no_possible_steps:
  "valid_trace e (Some s) r (\<lparr>statename = Some s, datastate = r, action = (l, i), output = p\<rparr> ## t) \<Longrightarrow>
    possible_steps e s r l i = {||} \<Longrightarrow> smap output t = sconst []"
  apply (rule valid_trace.cases)
  using valid_trace_None(2) by auto

(*
  This shows that if there's a finite trace p which represents a valid execution of the model for
  which there is no infinite trace with p as a prefix for which the property \<phi> holds, then \<phi> does
  not hold true for all traces.
*)
definition "ltl_apply \<phi> e = (\<forall>t \<in> {t. valid_trace e (Some 0) <> t}. \<phi> t)"

lemma ltl_apply: "(\<And>t. valid_trace e (Some 0) <> t \<Longrightarrow> \<phi> t) \<Longrightarrow> (ltl_apply \<phi> e)"
  by (simp add: ltl_apply_def)

lemma ltl_apply_all_states_registers: "(\<And>s r t. valid_trace e s r t \<Longrightarrow> \<phi> t) \<Longrightarrow> ltl_apply \<phi> e"
  by (simp add: ltl_apply_def)

lemma ltl_apply_S:
  assumes "(\<And>s r t. s |\<notin>| Some |`| (S e) \<Longrightarrow> valid_trace e s r t \<Longrightarrow> \<phi> t)"
  assumes "(\<And>s r t. s |\<in>| Some |`| (S e) \<Longrightarrow> valid_trace e s r t \<Longrightarrow> \<phi> t)"
    shows "ltl_apply \<phi> e"
  apply (simp add: ltl_apply_def)
  by (meson assms)

lemma one_step_ltl_apply:
  assumes "(\<And>s r t. s |\<notin>| Some |`| (S e) \<Longrightarrow> valid_trace e s r t \<Longrightarrow> \<phi> t)"
  assumes "\<And>s r l i t p. s |\<in>| (S e) \<Longrightarrow>
              possible_steps e s r l i = {||} \<or>
              (\<exists>(s', tr) |\<in>| possible_steps e s r l i.
              evaluate_outputs tr i r = (output (shd t)) \<and>
              Some s' = (statename (shd t)) \<and>
              evaluate_updates tr i r = (datastate (shd t))) \<Longrightarrow>
              valid_trace e (Some s) r (\<lparr>statename=Some s, datastate=r, action=(l, i), output = p\<rparr>##t) \<Longrightarrow>
              \<phi> (\<lparr>statename=Some s, datastate=r, action=(l, i), output = p\<rparr>##t)"
  shows "ltl_apply \<phi> e"
  apply (simp add: ltl_apply_def)
  apply clarsimp
  apply (rule valid_trace.cases)
     apply simp
    apply (erule fBexE)
  subgoal for x ea s r l i t p xa
    using assms(2)[of s r l i t]
    apply clarsimp
    apply (case_tac "0 |\<in>| S ea")
     apply simp
    apply (case_tac "\<exists>(s', tr)|\<in>|possible_steps ea 0 <> l i.
                evaluate_outputs tr i <> = output (shd t) \<and>
                Some s' = statename (shd t) \<and> evaluate_updates tr i <> = datastate (shd t)")
      apply simp
     apply auto[1]
    using assms(1) by blast
  subgoal for x ea s r l i t p
    using assms(2)[of s r l i t "[]"]
    apply clarsimp
    using assms(1) assms(2) fimageE by blast
  by simp

end
