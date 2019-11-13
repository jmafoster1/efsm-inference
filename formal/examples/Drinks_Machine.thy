section\<open>Examples\<close>
subsection\<open>Drinks Machine\<close>
text\<open>This theory formalises a simple drinks machine. The \emph{select} operation takes one
argument - the desired beverage. The \emph{coin} operation also takes one parameter representing
the value of the coin. The \emph{vend} operation has two flavours - one which dispenses the drink if
the customer has inserted enough money, and one which dispenses nothing if the user has not inserted
sufficient funds.

We first define a datatype \emph{statemane} which corresponds to $S$ in the formal definition.
Note that, while statename has four elements, the drinks machine presented here only requires three
states. The fourth element is included here so that the \emph{statename} datatype may be used in
the next example.
\<close>
theory Drinks_Machine
  imports "../Contexts"
begin

definition I :: "nat \<Rightarrow> vname" where
  "I n = vname.I (n-1)"
declare I_def [simp]

definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = STR ''select'',
        Arity = 1,
        Guard = [], \<comment> \<open> No guards \<close>
        Outputs = [],
        Updates = [ \<comment> \<open> Two updates: \<close>
                    (1, V (I 1)), \<comment> \<open>  Firstly set value of r1 to value of i1 \<close>
                    (2, L (Num 0)) \<comment> \<open> Secondly set the value of r2 to literal zero \<close>
                  ]
      \<rparr>"

text_raw\<open>\snip{coin}{1}{2}{%\<close>
definition coin :: "transition" where
"coin \<equiv> \<lparr>
        Label = STR ''coin'',
        Arity = 1,
        Guard = [],
        Outputs = [Plus (V (R 2)) (V (I 1))],
        Updates = [
                    (1, V (R 1)),
                    (2, Plus (V (R 2)) (V (I 1)))
                  ]
      \<rparr>"
text_raw\<open>}%endsnip\<close>

lemma label_coin: "Label coin = STR ''coin''"
  by (simp add: coin_def)

definition vend :: "transition" where
"vend \<equiv> \<lparr>
        Label = STR ''vend'',
        Arity = 0,
        Guard = [(Ge (V (R 2)) (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"

lemma label_vend: "Label vend = STR ''vend''"
  by (simp add: vend_def)

definition vend_fail :: "transition" where
"vend_fail \<equiv> \<lparr>
        Label = STR ''vend'',
        Arity = 0,
        Guard = [(GExp.Lt (V (R 2)) (L (Num 100)))],
        Outputs =  [],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"

lemma label_vend_fail: "Label vend_fail = STR ''vend''"
  by (simp add: vend_fail_def)

lemma arity_vend_fail: "Arity vend_fail = 0"
  by (simp add: vend_fail_def)

definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
          ((0,1), select),    \<comment> \<open> If we want to go from state 1 to state 2 then select will do that \<close>
          ((1,1), coin),
          ((1,1), vend_fail), \<comment> \<open> If we want to go from state 2 to state 2 then coin will do that \<close>
          ((1,2), vend) \<comment> \<open> If we want to go from state 2 to state 3 then vend will do that \<close>
         |}"

lemma "S drinks = {|0, 1, 2|}"
  apply (simp add: S_def drinks_def)
  by auto

lemmas transitions = select_def coin_def vend_def vend_fail_def

lemma possible_steps_0:  "length i = 1 \<Longrightarrow> possible_steps drinks 0 r (STR ''select'') i = {|(1, select)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def)

lemma arity_vend: "Arity vend = 0"
  by (simp add: vend_def)

lemma drinks_vend_insufficient: "r $ 2 = Some (Num x1) \<Longrightarrow> x1 < 100 \<Longrightarrow> possible_steps drinks 1 r (STR ''vend'') [] = {|(1, vend_fail)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma drinks_vend_invalid: "\<nexists>n. r $ 2 = Some (Num n) \<Longrightarrow> possible_steps drinks 1 r (STR ''vend'') [] = {||}"
  apply (simp add: possible_steps_empty drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def join_ir_def value_gt_def MaybeBoolInt_not_num_1 connectives)

lemma possible_steps_1_coin: "length i = 1 \<Longrightarrow> possible_steps drinks 1 r (STR ''coin'') i = {|(1, coin)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions )

lemma possible_steps_2_vend: "\<exists>n. r $ 2 = Some (Num n) \<and> n \<ge> 100 \<Longrightarrow> possible_steps drinks 1 r (STR ''vend'') [] = {|(2, vend)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma accepts_from_2: "accepts drinks 1 (<>(2 := Num 100, 1 := d)) [(STR ''vend'', [])]"
  apply (rule accepts.step)
  by (simp add: possible_steps_2_vend coin_def join_ir_def input2state_def value_plus_def accepts.base)

lemma regsimp: "<>(2 := n, 1 := d, 2 := n', 1 := d) = <>(2 := n', 1 := d)"
  by (metis finfun_update_twice finfun_update_twist)

lemma accepts_from_1a: "accepts drinks 1 (<>(2 := Num 50, 1 := d)) [(STR ''coin'', [Num 50]), (STR ''vend'', [])]"
  apply (rule accepts.step)
  apply (simp add: possible_steps_1_coin coin_def join_ir_def input2state_def value_plus_def regsimp)
  by (simp add: accepts_from_2)

lemma accepts_from_1: "accepts drinks 1 (<>(2 := Num 0, 1 := d))
     [(STR ''coin'', [Num 50]), (STR ''coin'', [Num 50]), (STR ''vend'', [])]"
  apply (rule accepts.step)
  apply (simp add: possible_steps_1_coin coin_def join_ir_def input2state_def value_plus_def regsimp)
  by (simp add: accepts_from_1a)

lemma purchase_coke: "observe_trace drinks 0 <> [(STR ''select'', [Str ''coke'']), (STR ''coin'', [Num 50]), (STR ''coin'', [Num 50]), (STR ''vend'', [])] =
                       [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke'')]]"
  apply (rule observe_trace_possible_step)
     apply (simp add: possible_steps_0)
     apply (simp add: select_def join_ir_def input2state_def accepts_from_1)
    apply (simp add: select_def)
   apply (simp add: select_def join_ir_def input2state_def)
  apply (rule observe_trace_possible_step)
      apply (simp add: possible_steps_1_coin)
     apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp accepts_from_1a)
    apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp apply_outputs_def)
   apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp)
  apply (rule observe_trace_possible_step)
      apply (simp add: possible_steps_1_coin)
     apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp accepts_from_2)
    apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp apply_outputs_def)
   apply (simp add: coin_def value_plus_def join_ir_def input2state_def regsimp)
  apply (rule observe_trace_possible_step)
      apply (simp add: possible_steps_2_vend)
     apply (simp add: accepts.base)
    apply (simp add: vend_def join_ir_def apply_outputs_def)
   apply simp
  by simp

lemma rejects_input: "l \<noteq> STR ''coin'' \<Longrightarrow> l \<noteq> STR ''vend'' \<Longrightarrow> \<not> accepts drinks 1 d' [(l, i)]"
  apply (rule trace_reject_no_possible_steps)
  apply (simp add: possible_steps_empty drinks_def)
  using label_coin label_vend label_vend_fail by blast

lemma rejects_accepts_prefix:
  "l \<noteq> STR ''coin'' \<Longrightarrow>
   l \<noteq> STR ''vend'' \<Longrightarrow>
   \<not> (accepts_trace drinks [(STR ''select'', [Str ''coke'']), (l, i)])"
  apply (rule trace_reject_later)
  apply (simp add: possible_steps_0 select_def join_ir_def input2state_def)
  using rejects_input by blast

lemma rejects_termination: "observe_trace drinks 0 <> [(STR ''select'', [Str ''coke'']), (STR ''rejects'', [Num 50]), (STR ''coin'', [Num 50])] = [[]]"
  apply (rule observe_trace_step)
   apply (simp add: step_def possible_steps_0 select_def)
  apply (rule observe_trace_no_possible_step)
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks_def)
  using arity_vend arity_vend_fail label_coin by auto

(* Part of Example 2 in Foster et. al. *)
lemma r2_0_vend: "can_take_transition vend i r \<Longrightarrow> \<exists>n. r $ 2 = Some (Num n) \<and> n \<ge> 100" (* You can't take vend immediately after taking select *)
  apply (simp add: can_take_transition_def can_take_def vend_def apply_guards_def maybe_negate_true maybe_or_false connectives)
  by (simp add: value_gt_def join_ir_def MaybeBoolInt_lt)

lemma drinks_vend_sufficient: "r $ 2 = Some (Num x1) \<Longrightarrow>
                x1 \<ge> 100 \<Longrightarrow>
                possible_steps drinks 1 r (STR ''vend'') [] = {|(2, vend)|}"
  using possible_steps_2_vend by blast

lemma drinks_end: "possible_steps drinks 2 r a b = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma drinks_vend_r2_String: "r $ 2 = Some (value.Str x2) \<Longrightarrow> possible_steps drinks 1 r (STR ''vend'') [] = {||}"
  apply (simp add: possible_steps_empty drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma drinks_vend_r2_rejects: "\<nexists>n. r $ 2 = Some (Num n) \<Longrightarrow> step drinks 1 r (STR ''vend'') [] = None"
  apply (rule no_possible_steps_1)
  apply (simp add: possible_steps_empty drinks_def)
  apply safe
    apply (simp add: coin_def)
   apply (simp add: vend_fail_def apply_guards_def join_ir_def value_gt_def MaybeBoolInt_not_num_1 connectives)
  by (simp add: vend_def apply_guards_def maybe_negate_true maybe_or_false value_gt_def join_ir_def MaybeBoolInt_not_num_1 connectives)

lemma drinks_0_rejects: "\<not> (fst a = STR ''select'' \<and> length (snd a) = 1) \<Longrightarrow>
    (possible_steps drinks 0 r (fst a) (snd a)) = {||}"
  apply (simp add: drinks_def possible_steps_def transitions)
  by force

lemma drinks_vend_empty: "(possible_steps drinks 0 <> (STR ''vend'') []) = {||}"
  using drinks_0_rejects
  by auto

lemma drinks_1_rejects: "fst a = STR ''coin'' \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
          a \<noteq> (STR ''vend'', []) \<Longrightarrow>
          possible_steps drinks 1 r (fst a) (snd a) = {||}"
proof
  assume not_coin: "fst a = STR ''coin'' \<longrightarrow> length (snd a) \<noteq> 1"
  assume not_vend: "a \<noteq> (STR ''vend'', [])"
  show "possible_steps drinks 1 r (fst a) (snd a) |\<subseteq>| {||}"
    using not_coin not_vend
    apply (simp add: drinks_def possible_steps_def)
    apply safe
     apply (simp add: One_nat_def)
    apply (metis arity_vend arity_vend_fail label_coin label_vend label_vend_fail length_0_conv numeral_1_eq_Suc_0 prod.collapse zero_neq_numeral)
    apply simp
    by (metis One_nat_def arity_vend arity_vend_fail label_vend label_vend_fail length_0_conv numeral_1_eq_Suc_0 prod.collapse simps(2) transitions(2) zero_neq_numeral)
  show "{||} |\<subseteq>| possible_steps drinks 1 r (fst a) (snd a)"
    by simp
qed

lemma drinks_rejects_future: "t \<noteq> [] \<Longrightarrow> \<not>accepts drinks 2 d t"
  apply safe
  apply (rule accepts.cases)
    apply simp
   apply simp
  by (simp add: drinks_end)

lemma drinks_1_rejects_trace: "\<not> (aa = STR ''vend'' \<and> b = []) \<Longrightarrow> \<not> (aa = STR ''coin'' \<and> length b = 1) \<Longrightarrow> \<not>accepts drinks 1 r ((aa, b) # t)"
  apply clarify
  apply (rule accepts.cases)
    apply simp
   apply simp
  apply clarify
  unfolding step_def
  using drinks_1_rejects by auto

lemma rejects_state_step: "s > 1 \<Longrightarrow> step drinks s r l i = None"
  apply (rule no_possible_steps_1)
  by (simp add: possible_steps_empty drinks_def)

lemma invalid_other_states: "s > 1 \<Longrightarrow> \<not> accepts drinks s r ((aa, b) # t)"
  apply clarify
  apply (rule accepts.cases)
    apply simp
   apply simp
  apply clarify
  using rejects_state_step accepts_cons_step by blast
end
