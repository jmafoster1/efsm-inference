theory DM_Inference
imports Inference "../examples/Drinks_Machine_2"
begin

lemma "max coin vend = vend"
  by (simp add: max_def coin_def vend_def less_eq_transition_ext_def less_transition_ext_def)

lemma merge_q1_q2: "merge_states q1 q2 (T drinks2) = (\<lambda> (a,b) .
  if (a, b) = (q0, q1) then {|select|} else
  if (a, b) = (q1,q1) then {|vend_nothing, coin, vend_fail|} else
  if (a, b) = (q1, q3) then {|vend|} else {||})"
  apply (rule ext)
  apply clarify
  apply (simp add: merge_states_def drinks2_def merge_with_def)
  by auto

lemma defined_drinks2: "(defined (T drinks2)) = {(q0,q1), (q1,q1), (q1,q2), (q2,q2), (q2,q3)}"
  apply (simp add: defined_def drinks2_def)
  using prod.inject by fastforce

lemma finite_defined_drinks2: "finite (defined (T drinks2))"
  by (simp add: defined_drinks2)

lemma possible_transitions: "t \<noteq> select \<Longrightarrow> t \<noteq> vend_nothing \<Longrightarrow> t \<noteq> coin \<Longrightarrow> t \<noteq> vend_fail \<Longrightarrow> t \<noteq> vend \<Longrightarrow> t \<notin> (if s' = q0 \<and> s2 = q1 then {select} else if (s', s2) = (q1, q1) then {vend_nothing, coin, vend_fail} else if (s', s2) = (q1, q3) then {vend} else {})"
  by simp

lemma unequal_labels[simp]: "Label t1 \<noteq> Label t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma unequal_arities[simp]: "Arity t1 \<noteq> Arity t2 \<Longrightarrow> t1 \<noteq> t2"
  by auto

lemma choice_vend_vend_nothing: "choice vend vend_nothing"
  apply (simp add: choice_def transitions)
  apply (rule_tac x="<R 2 := Num 100>" in exI)
  by simp

lemma vend_nothing_lt_vend: "vend_nothing < vend"
  by (simp add: less_transition_ext_def transitions)

lemma no_choice_vend_coin: "\<not> choice vend coin"
  by (simp add: choice_def transitions)

lemma coin_not_vend_fail: "coin \<noteq> vend_fail"
  by (simp add: transitions)

lemma no_choice_vend_vend_fail:  "\<not> choice vend vend_fail"
  apply (simp add: choice_def transitions)
  apply safe
  apply (case_tac " MaybeBoolInt (\<lambda>x y. y < x) (Some (Num 100)) (s (R 2))")
   apply simp
  by simp

lemma vend_nothing_lt_vend_fail: "vend_nothing < vend_fail"
  by (simp add: less_transition_ext_def transitions)

lemma choice_vend_nothing_vend_fail: "choice vend_nothing vend_fail"
  apply (simp add: choice_def transitions)
  apply (rule_tac x="<R 2 := Num 0>" in exI)
  by simp

lemma vend_vend_nothing_nondeterminism: "nondeterministic_pairs (merge_states q1 q2 (T drinks2)) \<noteq> {}"
  apply (simp add: nondeterministic_pairs_def merge_q1_q2)
  apply (rule_tac x=q1 in exI)
  apply (rule_tac x=q1 in exI)
  apply simp
  apply (rule_tac x=q1 in exI)
  apply simp
  apply (rule_tac x=vend_nothing in exI)
  apply (rule_tac x=vend_fail in exI)
  apply (simp add: vend_nothing_lt_vend_fail)
  by (simp add: choice_vend_nothing_vend_fail)

lemma nondeterminism_example: "(q1, (q1, q1), vend_nothing, vend_fail) \<in> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  apply (simp add: merge_q1_q2 nondeterministic_pairs_def vend_nothing_lt_vend_fail)
  apply (simp add: transitions choice_def)
  apply (rule_tac x="<R 2 := Num 0>" in exI)
  by simp

lemma nond_transitions_not_none: "nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> None"
  apply (simp add: nondeterministic_transitions_def)
  apply (simp add: vend_vend_nothing_nondeterminism)
  by (metis surj_pair)

lemma nondeterminism_example_2: "(q1, (q1, q3), (vend_nothing, vend)) \<in> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  apply (simp add: merge_q1_q2 nondeterministic_pairs_def vend_nothing_lt_vend)
  apply (simp add: transitions choice_def)
  apply (rule_tac x="<R 2 := Num 100>" in exI)
  by simp

lemma nondeterministic_pairs_aux_1: "\<And>xa a b aa ba.
       x = (q1, (a, b), aa, ba) \<Longrightarrow>
       aa |\<in>| (if a = q3 then {|vend|} else {||}) \<Longrightarrow>
       ba |\<in>| (if b = q1 then {|vend_nothing, coin, vend_fail|} else if (q1, b) = (q1, q3) then {|vend|} else {||}) \<Longrightarrow>
       aa < ba \<Longrightarrow> choice aa ba \<Longrightarrow> xa = q1 \<Longrightarrow> a \<noteq> q1 \<Longrightarrow> False"
proof -
fix xa :: statename and a :: statename and b :: statename and aa :: transition and ba :: transition
assume a1: "aa < ba"
assume a2: "ba |\<in>| (if b = q1 then {|vend_nothing, coin, vend_fail|} else if (q1, b) = (q1, q3) then {|vend|} else {||})"
assume a3: "aa |\<in>| (if a = q3 then {|vend|} else {||})"
assume a4: "choice aa ba"
have f5: "\<forall>f t. f \<noteq> {||} \<or> (t::transition) |\<notin>| f"
by auto
  have f6: "(if b = q1 then {|vend_nothing, coin, vend_fail|} else if (q1, b) = (q1, q3) then {|vend|} else {||}) \<noteq> {||}"
    using a2 by blast
  have f7: "aa |\<in>| {|vend|}"
using f5 a3 by presburger
then have "ba |\<notin>| {|vend_nothing, coin, vend_fail|}"
using f5 a4 a1 by (metis (no_types) choice_def finsertE label_vend label_vend_not_coin less_imp_not_less no_choice_vend_vend_fail vend_nothing_lt_vend)
then have "ba |\<in>| {|vend|}"
using f6 a2 by presburger
then show False
using f7 a1 by fastforce
qed

lemma nondeterministic_pairs_members: "x \<in> nondeterministic_pairs (merge_states q1 q2 (T drinks2)) \<Longrightarrow> x = (q1, (q1, q3), (vend_nothing, vend)) \<or> x = (q1, (q1, q1), vend_nothing, vend_fail)"
  apply (simp add: nondeterministic_pairs_def)
  apply clarify
  apply simp
  apply (case_tac "xa=q1")
   apply (case_tac "a=q1")
    apply (case_tac "b=q1")
     apply (simp add: merge_q1_q2)
     apply (metis choice_def label_vend_fail label_vend_not_coin label_vend_nothing not_less_iff_gr_or_eq vend_nothing_lt_vend_fail)
    apply (simp add: merge_q1_q2)
    apply (metis choice_symmetry fempty_iff finsertE no_choice_vend_coin no_choice_vend_vend_fail)
   apply (simp add: merge_q1_q2)
   apply (meson nondeterministic_pairs_aux_1)
  apply (simp add: merge_q1_q2)
  by (smt fempty_iff fsingleton_iff not_less_iff_gr_or_eq prod.inject)

lemma nondeterminisitic_pairs: "(nondeterministic_pairs (merge_states q1 q2 (T drinks2))) = {(q1, (q1, q3), (vend_nothing, vend)), (q1, (q1, q1), vend_nothing, vend_fail)}"
  using nondeterministic_pairs_members nondeterminism_example nondeterminism_example_2 by blast        

lemma no_nondeterminism_q0: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> Some (q0, (aa, b), ab, ba)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def)

lemma no_nondeterminism_q2: "\<forall>aa b ab ba. (q2, (aa, b), ab, ba) \<notin> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  by (simp add: merge_q1_q2 nondeterministic_pairs_def)

lemma no_nondeterminism_q2_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> Some (q2, (aa, b), ab, ba)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def)

lemma no_nondeterminism_q3: "\<forall>aa b ab ba. (q3, (aa, b), ab, ba) \<notin> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  by (simp add: merge_q1_q2 nondeterministic_pairs_def)

lemma no_nondeterminism_q3_2: "\<forall>aa b ab ba. nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> Some (q3, (aa, b), ab, ba)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def)

lemma only_nondeterminism_q1: "nondeterministic_transitions (merge_states q1 q2 (T drinks2)) = Some (a, (aa, b), aaa, ba) \<Longrightarrow> a = q1"
  apply (case_tac a)
  apply (simp add: no_nondeterminism_q0)
    apply simp
   apply (simp add: no_nondeterminism_q2_2)
  by (simp add: no_nondeterminism_q3_2)

lemma no_transitions_to_q0: "aa = q0 \<or> b = q0 \<Longrightarrow> (a, (aa, b), ab, ba) \<notin> nondeterministic_pairs (merge_states q1 q2 (T drinks2))"
  apply (cases a)
     apply (meson Pair_inject nondeterministic_pairs_members statename.distinct(1))
    apply (meson Pair_inject nondeterministic_pairs_members statename.distinct(1) statename.distinct(5))
   apply (simp add: no_nondeterminism_q2)
  by (simp add: no_nondeterminism_q3)

lemma no_transitions_to_q0_2: "aa = q0 \<or> b = q0 \<Longrightarrow> nondeterministic_transitions (merge_states q1 q2 (T drinks2)) \<noteq> Some (a, (aa, b), ab, ba)"
  apply (cases a)
     apply (simp add: no_nondeterminism_q0)
    apply (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def)
    apply auto[1]
   apply (simp add: no_nondeterminism_q2_2)
  by (simp add: no_nondeterminism_q3_2)

lemma q1_nondeterminism_options: "(q1, (q1, q1), ab, ba) \<in> nondeterministic_pairs (merge_states q1 q2 (T drinks2)) \<Longrightarrow> ab = vend_fail \<and> ba = vend_nothing \<or> ab = vend_nothing \<and> ba = vend_fail"
  apply (simp add: nondeterministic_pairs_def merge_q1_q2 choice_def)
  apply safe
  by (simp_all add: transitions)

lemma q1_nondeterminism_options_2: "nondeterministic_transitions (merge_states q1 q2 (T drinks2)) = Some (q1, (q1, q1), ab, ba) \<Longrightarrow> ab = vend_fail \<and> ba = vend_nothing \<or> ab = vend_nothing \<and> ba = vend_fail"
  by (simp add: nondeterministic_transitions_def vend_vend_nothing_nondeterminism nondeterminisitic_pairs max_def)

lemma merge_self_state: "merge_states x x t = t"
  by (simp add: merge_states_def)

lemma medial_vend_nothing: "(medial c (Guard vend_nothing)) = c"
  by (simp add: transitions)

lemma medial_vend_fail: "medial select_posterior (Guard vend_fail) = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Lt (Num 100))\<rbrakk>"
  apply (rule ext)
  by (simp add: transitions)

lemma vend_nothing_posterior: "posterior select_posterior vend_nothing = select_posterior"
  apply (simp only: posterior_def medial_vend_nothing)
  apply (simp add: consistent_select_posterior del: One_nat_def)
  apply (rule ext)
  apply (simp add: Let_def)
  by (simp add: transitions)

lemma consistent_medial_vend_fail: "consistent \<lbrakk>V (R 1) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> And (cexp.Eq (Num 0)) (cexp.Lt (Num 100))\<rbrakk>"
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  by (simp add: connectives consistent_empty_4)

lemma vend_fail_posterior: "posterior select_posterior vend_fail = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> And (Eq (Num 0)) (Lt (Num 100))\<rbrakk>"
  apply (simp only: posterior_def medial_vend_fail)
  apply (simp add: consistent_medial_vend_fail del: One_nat_def)
  apply (rule ext)
  by (simp add: transitions)

lemma vend_fail_subsumes_vend_nothing: "subsumes select_posterior vend_fail vend_nothing"
  apply (simp add: subsumes_def del: One_nat_def)
  apply safe
  using guard_vend_nothing medial_vend_fail apply auto[1]
    apply (simp add: transitions)
   apply (simp add: medial_vend_nothing del: One_nat_def)
   apply (simp add: vend_nothing_posterior del: One_nat_def)
   apply (simp only: vend_fail_posterior)
   apply (simp del: One_nat_def)
   apply (case_tac "r = V (R 2)")
    apply simp
    apply (case_tac "ValueLt (Some i) (Some (Num 100))")
     apply simp
    apply simp
   apply (case_tac "r = V (R 1)")
    apply simp
   apply simp
   apply (simp only: vend_fail_posterior)
  apply (simp add: consistent_def)
  apply (rule_tac x="<R 1 := Num 0, R 2 := Num 0>" in exI)
  by (simp add: connectives consistent_empty_4)

lemma posterior_select: "length (snd e) = Suc 0 \<Longrightarrow> (posterior \<lbrakk>\<rbrakk> (snd (the_elem (possible_steps drinks2 q0 Map.empty ''select'' (snd e))))) =
     (\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R (Suc 0)) then cexp.Bc True else \<lbrakk>\<rbrakk> a)"
  apply (simp add: posterior_def)
  apply (simp add: possible_steps_q0)
  apply (simp add: select_def)
  apply (rule ext)
  apply simp
  by (smt One_nat_def Suc_1 aexp.inject(2) aexp.simps(18) n_not_Suc_n vname.inject(2) vname.simps(5))

lemma apply_updates_vend_nothing_2: "(EFSM.apply_updates (Updates vend_nothing)
           (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R 1 then Some (hd (snd e)) else None))
           (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R 1 then Some (hd (snd e)) else None)) = <R 2 \<mapsto> Num 0, R 1 \<mapsto> (hd (snd e))>"
  apply (rule ext)
  by (simp add: transitions)

lemma select_posterior_equiv: "\<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> = select_posterior"
  apply (rule ext)
  by simp

lemma select_posterior_equiv_2: "(\<lambda>a. if a = V (R 2) then cexp.Eq (Num 0) else if a = V (R (Suc 0)) then cexp.Bc True else \<lbrakk>\<rbrakk> a) = select_posterior"
  apply (rule ext)
  by simp

lemma register_simp: "(\<lambda>x. if x = R (Suc 0)
          then aval (snd (R (Suc 0), V (R (Suc 0)))) (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else <R (Suc 0) := hd (snd e)> (R n)))
          else EFSM.apply_updates [(R 2, V (R 2))] (case_vname Map.empty (\<lambda>n. if n = 2 then Some (Num 0) else <R (Suc 0) := hd (snd e)> (R n)))
                <R (Suc 0) := hd (snd e), R 2 := Num 0> x) =  <R (Suc 0) := hd (snd e), R 2 := Num 0>"
  apply (rule ext)
  by simp

lemma observe_vend_nothing: "a = (''vend'', []) \<Longrightarrow> (observe_all drinks2 q1 <R (Suc 0) := hd (snd e), R 2 := Num 0> (a # t)) = (vend_nothing, q1, [], <R (Suc 0) := hd (snd e), R 2 := Num 0>)#(observe_all drinks2 q1 <R (Suc 0) := hd (snd e), R 2 := Num 0> t)"
  apply simp
  apply (simp add: drinks2_vend_insufficient)
  apply (simp add: updates_vend_nothing outputs_vend_nothing)
  apply safe
   apply (rule ext)
   apply simp
  by (simp only: register_simp)

lemma error_trace: "t \<noteq> [] \<Longrightarrow> observe_all drinks2 q0 Map.empty t = [] \<Longrightarrow> observe_all drinks2 q0 Map.empty (t @ [e]) = []"
  apply (cases t)
   apply simp
  apply simp
  apply (case_tac "is_singleton (possible_steps drinks2 q0 Map.empty (fst a) (snd a))")
   apply simp
   apply (case_tac "the_elem (possible_steps drinks2 q0 Map.empty (fst a) (snd a))")
   apply simp
  by simp

lemma reg_simp_3: "(\<lambda>a. if a = R 2 then Some (Num 0) else if a = R (Suc 0) then Some (hd (snd e)) else None) = <R (Suc 0) := hd (snd e), R 2 := Num 0>"
  apply (rule ext)
  by simp

lemma coin_updates: "(EFSM.apply_updates (Updates coin)
            (case_vname (\<lambda>n. input2state (snd a) (Suc 0) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else <R (Suc 0) := s> (R n)))
            <R (Suc 0) := s, R 2 := Num 0>) = (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus (Some (Num 0)) (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma equal_first_event: "observe_all drinks2 q0 Map.empty t = x # list \<Longrightarrow>
       observe_all drinks2 q0 Map.empty (t @ [e]) = y # lista \<Longrightarrow> x = y"
proof (induct t)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  then show ?case
    apply simp
    apply (case_tac "fst a = ''select'' \<and> length (snd a) = 1")
     apply (simp add: possible_steps_q0 select_posterior)
     apply (simp add: updates_select)
     apply auto[1]
    by (simp add: drinks2_q0_invalid)
qed

lemma drinks2_singleton_q0: "is_singleton (possible_steps drinks2 q0 Map.empty (fst e) (snd e)) \<Longrightarrow> fst e = ''select'' \<and> length (snd e) = 1"
  apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
   apply simp
  by (simp add: drinks2_q0_invalid)

lemma drinks2_observe_all_fst_select: "observe_all drinks2 q0 Map.empty (t @ [e]) = [(aaa, q1, c, d)] \<Longrightarrow> aaa = select"
proof (induct t)
  case Nil
  then show ?case
    apply simp
    apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
     apply (simp add: possible_steps_q0)
  by (simp add: drinks2_q0_invalid)
next
  case (Cons e t)
  then show ?case
    apply simp
    apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
     apply (simp add: possible_steps_q0)
    by (simp add: drinks2_q0_invalid)
qed

lemma drinks2_singleton_q0_select: "is_singleton (possible_steps drinks2 q0 Map.empty (fst e) (snd e)) \<Longrightarrow>
       the_elem (possible_steps drinks2 q0 Map.empty (fst e) (snd e)) = (q1, aa) \<Longrightarrow> aa = select"
  using Drinks_Machine_2.possible_steps_q0 drinks2_singleton_q0 by auto

lemma coin_updates_2: "(EFSM.apply_updates (Updates coin)
       (case_vname (\<lambda>n. input2state (snd a) (Suc 0) (I n)) (\<lambda>n. if n = 2 then Some (Num 0) else if R n = R (Suc 0) then Some s else None))
       (\<lambda>a. if a = R 2 then Some (Num 0) else if a = R (Suc 0) then Some (hd (snd e)) else None)) =
       (\<lambda>u. if u = R 1 then Some s else if u = R 2 then value_plus (Some (Num 0)) (input2state (snd a) 1 (I 1)) else None)"
  apply (rule ext)
  by (simp add: coin_def)

lemma r_R2_none: "r (R 2) = None \<Longrightarrow> (possible_steps drinks2 q2 r ''vend'' []) = {}"
  apply (simp add: possible_steps_def)
  apply (rule allI)
  apply (rule allI)
  apply (case_tac a)
     apply (simp add: drinks2_def)
    apply (simp add: drinks2_def)
   apply (simp add: drinks2_def vend_fail_def coin_def connectives relations)
  by (simp add: drinks2_def vend_def connectives relations)

lemma drinks2_vend_insufficient2: "r (R 2) = Some (Num x1) \<Longrightarrow> ab = Num x1 \<Longrightarrow> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 q2 r (''vend'') [] = {(q2, vend_fail)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def vend_def connectives relations)
      apply (case_tac a)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def label_vend_not_coin relations connectives)
  by (simp_all add: drinks2_def vend_def vend_fail_def connectives relations)

lemma drinks2_vend_sufficient: "r (R 2) = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 q2 r (''vend'') [] = {(q3, vend)}"
  apply (simp add: possible_steps_def)
  apply safe
       apply (case_tac a)
          apply (simp add: drinks2_def)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def label_vend_not_coin vend_fail_def connectives relations)
       apply (simp add: drinks2_def)
      apply (case_tac a)
         apply (simp add: drinks2_def)
        apply (simp add: drinks2_def)
       apply (simp add: drinks2_def label_vend_not_coin vend_fail_def connectives relations)
  by (simp_all add: drinks2_def vend_def connectives relations)

lemma none_outputs_vend:  "r (R 1) = None \<Longrightarrow> apply_outputs (Outputs vend) r = []"
  by (simp add: vend_def)

lemma "\<forall>r. \<not> gets_us_to q1 drinks2 q2 r t"
proof (induct t)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply simp
    apply (case_tac "step drinks2 q2 r (fst a) (snd a)")
     apply simp
    apply simp
    apply (case_tac aa)
    apply simp

    apply (case_tac "a = (''vend'', [])")
     apply simp
     apply (case_tac "r (R 2)")
      apply (simp add: r_R2_none)
     apply (case_tac "ab")
      apply simp
      apply (case_tac "x1 < 100")
       apply (simp add: drinks2_vend_insufficient2)
      apply (simp add: drinks2_vend_sufficient)
      apply (case_tac "r (R 1)")
    apply (simp add: none_outputs_vend)



    apply (case_tac "fst a = ''coin'' \<and> length (snd a) = 1 ")
     apply simp
     apply (simp add: drinks2_q2_coin)
    oops

lemma " gets_us_to q1 drinks2 q1 <R (Suc 0) := hd (snd e), R 2 := Num 0> (xs @ [x]) \<Longrightarrow>
    \<not> gets_us_to q1 drinks2 q1 <R (Suc 0) := hd (snd e), R 2 := Num 0> xs \<Longrightarrow> False"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    apply simp
    apply (case_tac "a=(''vend'', [])")
     apply simp
     apply (simp add: drinks2_vend_insufficient apply_updates_vend_nothing)
    using Cons.hyps apply blast
    apply (case_tac "fst a = ''coin'' \<and> length (snd a) = 1 ")
    apply simp
     apply (simp add: drinks2_q1_coin)
     apply (simp add: coin_updates_2)
    oops



lemma "gets_us_to q1 drinks2 q0 Map.empty (xs @ [x]) \<Longrightarrow>
    EFSM.valid drinks2 q0 Map.empty (xs @ [x]) \<Longrightarrow>
     \<not> gets_us_to q1 drinks2 q0 Map.empty xs \<Longrightarrow> xs = []"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons e xs)
  then show ?case
    apply simp
    apply (case_tac "fst e = ''select'' \<and> length (snd e) = 1 ")
     apply (simp add: possible_steps_q0 updates_select)
    oops

lemma "gets_us_to q1 drinks2 q0 Map.empty (xs @ [e]) \<Longrightarrow>
    gets_us_to q1 drinks2 q0 Map.empty xs \<Longrightarrow>
    EFSM.valid drinks2 q0 Map.empty xs \<Longrightarrow> e = (''vend'', [])"
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case
    apply (case_tac "gets_us_to q1 drinks2 q0 Map.empty (xs @ [e])")
     apply simp
     apply (case_tac "gets_us_to q1 drinks2 q0 Map.empty xs")
      apply simp
      apply (case_tac "EFSM.valid drinks2 q0 Map.empty xs")
       apply simp
      apply (simp add: prefix_closure)
    apply simp
    oops


lemma gets_us_to_q1_anterior_context: "gets_us_to q1 drinks2 q0 <> p \<Longrightarrow> anterior_context drinks2 p = \<lbrakk>V (R 1) \<mapsto> Bc True, V (R 2) \<mapsto> Eq (Num 0)\<rbrakk>"
proof (induct p rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc e xs)
  then show ?case
    apply simp
    apply (simp add: anterior_context_def)
    apply (case_tac "gets_us_to q1 drinks2 q0 Map.empty xs")
     apply (case_tac "valid_trace drinks2 xs")
    apply simp
    sorry
qed

  

lemma "directly_subsumes drinks2 q1 vend_fail vend_nothing"
  apply (simp add: directly_subsumes_def)
  apply (simp add: gets_us_to_q1_anterior_context del: One_nat_def)
  using vend_fail_subsumes_vend_nothing
  by simp

lemma "choice vend_nothing vend"
  by (simp add: choice_symmetry choice_vend_vend_nothing)

lemma nondeterministic_transitions: "nondeterministic_transitions (merge_states q1 q2 (T drinks2)) = Some (q1, (q1, q3), vend_nothing, vend)"
  by (simp add: nondeterministic_transitions_def nondeterminisitic_pairs max_def)

lemma vend_doesnt_exit_q1: "\<not>exits_state drinks2 vend q1"
  apply (simp add: exits_state_def drinks2_def)
  using label_vend label_vend_not_coin vend_nothing_lt_vend by auto

lemma vend_nothing_exits_q1: "exits_state drinks2 vend_nothing q1"
  apply (simp add: exits_state_def drinks2_def)
  by auto

lemma merge_q1_q3: "let t' = merge_states q1 q2 (T drinks2)
        in merge_states q1 q3 t' = (\<lambda> (a,b) .
                      if (a, b) = (q0, q1) then {|select|} else
                      if (a, b) = (q1,q1) then {|vend_nothing, coin, vend_fail, vend|} else {||})"
  apply (simp add: merge_q1_q2)
  apply (rule ext)
  apply clarify
  apply (simp add: merge_states_def drinks2_def merge_with_def)
  by auto

lemma merge_q1_q3_2: "(merge_states q1 q3 (merge_states q1 q2 (T drinks2))) = (\<lambda> (a,b) .
                      if (a, b) = (q0, q1) then {|select|} else
                      if (a, b) = (q1,q1) then {|vend_nothing, coin, vend_fail, vend|} else {||})"
  using merge_q1_q3 by auto

lemma vend_nothing_vend_nondeterminism: "(q1, (q1, q1), (vend_nothing, vend)) \<in> {(origin, (dest1, dest2), t1, t2).
            t1 |\<in>|
            (if origin = q0 \<and> dest1 = q1 then {|select|}
             else if (origin, dest1) = (q1, q1) then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
            t2 |\<in>|
            (if origin = q0 \<and> dest2 = q1 then {|select|}
             else if (origin, dest2) = (q1, q1) then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
            t1 < t2 \<and> choice t1 t2}"
  by (simp add: choice_symmetry choice_vend_vend_nothing vend_nothing_lt_vend)

lemma vend_nothing_vend_fail_nondeterminsim: "(q1, (q1, q1), vend_nothing, vend_fail) \<in> {(origin, (dest1, dest2), t1, t2).
            t1 |\<in>|
            (if origin = q0 \<and> dest1 = q1 then {|select|}
             else if (origin, dest1) = (q1, q1) then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
            t2 |\<in>|
            (if origin = q0 \<and> dest2 = q1 then {|select|}
             else if (origin, dest2) = (q1, q1) then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
            t1 < t2 \<and> choice t1 t2}"
  by (simp add: choice_vend_nothing_vend_fail vend_nothing_lt_vend_fail)

lemma aux1: "\<And>a b c d aa ba.
       c |\<in>| (if aa = q1 then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
       d |\<in>| (if ba = q1 then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and> c < d \<and> choice c d \<Longrightarrow>
       x = (q1, (aa, ba), c, d) \<Longrightarrow>
       b = (aa, ba) \<Longrightarrow>
       a = q1 \<Longrightarrow> aa = q1 \<and> ba = q1 \<and> c = vend_nothing \<and> d = vend_fail \<or> aa = q1 \<and> ba = q1 \<and> c = vend_nothing \<and> d = vend"
proof -
  fix a :: statename and b :: "statename \<times> statename" and c :: transition and d :: transition and aa :: statename and ba :: statename
  assume a1: "c |\<in>| (if aa = q1 then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and> d |\<in>| (if ba = q1 then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and> c < d \<and> choice c d"
  have f2: "\<forall>t ta. \<not> (t::transition) < ta \<or> t \<noteq> ta"
    by blast
  have f3: "\<forall>f t. f \<noteq> {||} \<or> (t::transition) |\<notin>| f"
    by blast
  have f4: "(if aa = q1 then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<noteq> {||}"
    using a1 by blast
  then have f5: "c = vend_nothing \<or> c |\<in>| {|coin, vend_fail, vend|}"
    using a1 by (metis (full_types) finsert_iff)
  obtain zz :: "transition \<Rightarrow> transition \<Rightarrow> vname \<Rightarrow> value option" where
    "\<forall>x0 x1. (\<exists>v2. apply_guards (Guard x1) v2 \<and> apply_guards (Guard x0) v2) = (apply_guards (Guard x1) (zz x0 x1) \<and> apply_guards (Guard x0) (zz x0 x1))"
    by moura
  then have f6: "Label c = Label d \<and> Arity c = Arity d \<and> apply_guards (Guard c) (zz d c) \<and> apply_guards (Guard d) (zz d c)"
    using a1 by (simp add: choice_def)
have f7: "(if ba = q1 then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<noteq> {||}"
using a1 by blast
  have f8: "d = vend_nothing \<or> d |\<in>| {|coin, vend_fail, vend|}"
    using a1 by (metis (full_types) finsert_iff)
  have f9: "d |\<notin>| {||}"
    by blast
  have f10: "Label vend = Label vend_fail"
    by (simp add: label_vend label_vend_fail)
  have f11: "c = vend_fail \<longrightarrow> d = vend_fail \<or> d |\<in>| {|vend|}"
    using f8 f6 f2 a1 by (metis finsert_iff label_vend_fail label_vend_not_coin less_trans vend_nothing_lt_vend_fail)
    then have "d \<noteq> vend_fail \<and> c = vend_fail \<longrightarrow> Arity vend = Arity c"
using f9 f6 by (metis (no_types) finsert_iff)
  then have "d = vend_fail \<or> c \<noteq> vend_fail"
    using f11 f10 f6 choice_def no_choice_vend_vend_fail by blast
    then show "aa = q1 \<and> ba = q1 \<and> c = vend_nothing \<and> d = vend_fail \<or> aa = q1 \<and> ba = q1 \<and> c = vend_nothing \<and> d = vend"
      using f8 f7 f6 f5 f4 f3 f2 a1 by (metis finsert_iff label_vend label_vend_fail label_vend_not_coin label_vend_nothing less_trans no_choice_vend_vend_fail vend_nothing_lt_vend)
  qed

lemma only_2_nondeterministic_transitions: "x \<in> {(origin, (dest1, dest2), t1, t2).
            t1 |\<in>|
            (if origin = q0 \<and> dest1 = q1 then {|select|}
             else if (origin, dest1) = (q1, q1) then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
            t2 |\<in>|
            (if origin = q0 \<and> dest2 = q1 then {|select|}
             else if (origin, dest2) = (q1, q1) then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
            t1 < t2 \<and> choice t1 t2} \<Longrightarrow> x = (q1, (q1, q1), vend_nothing, vend_fail) \<or> x = (q1, (q1, q1), (vend_nothing, vend))"
  apply (cases x)
  apply (case_tac b)
  apply simp
  apply (case_tac a)
     apply simp
     apply (smt fempty_iff fsingleton_iff not_less_iff_gr_or_eq prod.inject)
    apply simp
  using aux1
    apply simp
   apply simp
  by simp

lemma nondeterministic_transitions_2: "{(origin, (dest1, dest2), t1, t2).
            t1 |\<in>|
            (if origin = q0 \<and> dest1 = q1 then {|select|}
             else if (origin, dest1) = (q1, q1) then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
            t2 |\<in>|
            (if origin = q0 \<and> dest2 = q1 then {|select|}
             else if (origin, dest2) = (q1, q1) then {|vend_nothing, coin, vend_fail, vend|} else {||}) \<and>
            t1 < t2 \<and> choice t1 t2} = {(q1, (q1, q1), (vend_nothing, vend)), (q1, (q1, q1), vend_nothing, vend_fail)}"
  using only_2_nondeterministic_transitions vend_nothing_vend_fail_nondeterminsim vend_nothing_vend_nondeterminism
  by blast

lemma nondet_pairs_simpler:  "nondeterministic_pairs (merge_states q1 q3 (merge_states q1 q2 (T drinks2))) = {(q1, (q1, q1), (vend_nothing, vend)), (q1, (q1, q1), vend_nothing, vend_fail)}"
  by (simp add: nondeterministic_pairs_def merge_q1_q3_2 nondeterministic_transitions_2)
  
lemma vend_fail_leq_vend: "vend_fail \<le> vend"
  by (simp add: less_eq_transition_ext_def less_transition_ext_def transitions)

lemma max_nondeterministic_transitions: "max (q1, (q1, q1), vend_nothing, vend) (q1, (q1, q1), vend_nothing, vend_fail) = (q1, (q1, q1), vend_nothing, vend)"
  apply (simp add: max_def)
  by (simp add: antisym vend_fail_leq_vend)

lemma merge_states_2_nondeterminism: "nondeterministic_transitions (merge_states q1 q3 (merge_states q1 q2 (T drinks2))) = Some (q1, (q1, q1), vend_nothing, vend)"
  apply (simp add: nondeterministic_transitions_def nondeterministic_pairs_def)
  apply (simp add: merge_q1_q3_2)
  apply safe
              apply (metis choice_vend_nothing_vend_fail vend_nothing_lt_vend_fail)
  using choice_def label_vend_not_coin label_vend_nothing apply auto[1]
  using vend_nothing_lt_vend_fail apply auto[1]
  using vend_nothing_lt_vend apply auto[1]
  using choice_def label_vend_not_coin label_vend_nothing apply auto[1]
         apply (simp add: nondeterministic_transitions_2 max_nondeterministic_transitions)
        apply (simp add: nondeterministic_transitions_2 max_nondeterministic_transitions)
       apply (simp add: nondeterministic_transitions_2 max_nondeterministic_transitions)
      apply (simp add: nondeterministic_transitions_2 max_nondeterministic_transitions)
     apply (simp add: nondeterministic_transitions_2 max_nondeterministic_transitions)
    apply (simp add: nondeterministic_transitions_2 max_nondeterministic_transitions)
   apply (simp add: nondeterministic_transitions_2 max_nondeterministic_transitions)
  by (simp add: nondeterministic_transitions_2 max_nondeterministic_transitions)

lemma vend_exits_q1: "exits_state \<lparr>s0 = q0, T = merge_states q1 q2 (T drinks2)\<rparr> vend q1"
  apply (simp add: exits_state_def merge_q1_q2)
  by auto

lemma vend_nothing_exits_q1_2: "exits_state \<lparr>s0 = q0, T = merge_states q1 q2 (T drinks2)\<rparr> vend_nothing q1"
  apply (simp add: exits_state_def merge_q1_q2)
  by auto

lemma not_subset: "\<not>{(q1, (q1, q3), vend_nothing, vend), (q1, (q1, q1), vend_nothing, vend_fail)}
        \<subseteq> {Max {(q1, (q1, q3), vend_nothing, vend), (q1, (q1, q1), vend_nothing, vend_fail)}}"
  by simp

lemma not_subset_2: "\<not> {(q1, (q1, q1), vend_nothing, vend), (q1, (q1, q1), vend_nothing, vend_fail)}
     \<subseteq> {Max {(q1, (q1, q1), vend_nothing, vend), (q1, (q1, q1), vend_nothing, vend_fail)}}"
  using choice_def choice_vend_vend_nothing no_choice_vend_vend_fail nondeterministic_transitions_2 by auto

lemma nondeterminism_merge_q1_q2: "nondeterminism (merge_states q1 q2 (T drinks2))"
  by (simp add: nondeterminism_def vend_vend_nothing_nondeterminism)

lemma max_nondeterminism: "max (q1, (q1, q3), vend_nothing, vend) (q1, (q1, q1), vend_nothing, vend_fail) = (q1, (q1, q3), vend_nothing, vend)"
  by (simp add: max_def)

lemma apply_guards_vend_nothing:  "\<forall>i r. apply_guards (Guard vend_nothing) (join_ir i r)"
  by (simp add: guard_vend_nothing)

lemma consistent_posterior_vend_nothing: "consistent c \<Longrightarrow> consistent (posterior c vend_nothing)"
  apply (simp add: posterior_def guard_vend_nothing updates_vend_nothing)
  apply (simp add: consistent_def)
  by auto

lemma consistent_posterior_vend_nothing_2: "\<not>consistent c \<Longrightarrow> \<not>consistent (posterior c vend_nothing)"
  apply (simp add: posterior_def guard_vend_nothing updates_vend_nothing)
  by (simp add: consistent_def)

lemma outputs_vend_neq_vend_nothing: "(\<exists>i r. [] \<noteq> apply_outputs (Outputs vend) (case_vname (\<lambda>n. input2state i (Suc 0) (I n)) (\<lambda>n. r (R n))))"
  apply (rule_tac x="[]" in exI)
  apply (rule_tac x="<R 1 := Str ''coke''>" in exI)
  by (simp add: vend_def)

lemma vend_doesnt_subsume_vend_nothing: "\<not> subsumes c vend vend_nothing"
  apply (simp add: subsumes_def apply_guards_vend_nothing)
  apply (simp add: guard_vend_nothing outputs_vend_nothing)
  using outputs_vend_neq_vend_nothing
  by simp

lemma vend_doesnt_directly_subsume_vend_nothing: "\<not>directly_subsumes drinks2 q2 vend vend_nothing"
  apply (simp add: directly_subsumes_def vend_doesnt_subsume_vend_nothing)
  apply (simp add: gets_us_to_def)
  apply (rule_tac x="[(''select'', [Str ''coke'']), (''coin'', [Num 100])]" in exI)
  apply simp
  apply (simp add: possible_steps_q0)
  by (simp add: possible_steps_q1)

lemma vend_nothing_doesnt_directly_subsume_vend: "directly_subsumes drinks2 q1 vend_nothing vend"
  sorry

lemma nondeterminsm_merge_q1_q3: "nondeterminism (merge_states q1 q3 (merge_states q1 q2 (T drinks2)))"
  apply (simp add: nondeterminism_def)
  by (simp add: nondet_pairs_simpler)

lemma outputs_vend_neq_vend_nothing_2: "(\<exists>i r. apply_guards (Guard vend) (case_vname (\<lambda>n. input2state i (Suc 0) (I n)) (\<lambda>n. r (R n))) \<and>
           apply_outputs (Outputs vend) (case_vname (\<lambda>n. input2state i (Suc 0) (I n)) (\<lambda>n. r (R n))) \<noteq> [])"
  apply (rule_tac x="[]" in exI)
  apply (rule_tac x="<R 1 := Str ''coke'', R 2 := Num 100>" in exI)
  by (simp add: transitions)

lemma vend_doesnt_subsume_vend_nothing_2: "\<not> subsumes c vend_nothing vend"
  apply (simp add: subsumes_def apply_guards_vend_nothing)
  apply (simp add: guard_vend_nothing outputs_vend_nothing)
  using outputs_vend_neq_vend_nothing_2
  by simp

lemma possible_steps_q0_2: "(possible_steps \<lparr>s0 = q0, T = merge_states q1 q2 (T drinks2)\<rparr> q0 Map.empty ''select'' [Str ''coke'']) = {(q1, select)}"
  apply (simp add: possible_steps_def)
  apply safe
  using Pair_inject merge_q1_q2 apply force
      apply (smt finsert_fminus finsert_not_fempty fsingleton_iff merge_q1_q2 old.prod.case prod.inject statename.distinct(1))
  by (simp_all add: transitions merge_q1_q2)

lemma vend_doesnt_directly_subsume_vend_nothing_2: "\<not>directly_subsumes \<lparr>s0 = q0, T = merge_states q1 q2 (T drinks2)\<rparr> q1 vend_nothing vend"
  apply (simp add: directly_subsumes_def vend_doesnt_subsume_vend_nothing_2)
  apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
  by (simp add: gets_us_to_def possible_steps_q0_2)

lemma subset_nondet: "{(q1, (q1, q3), vend_nothing, vend), (q1, (q1, q1), vend_nothing, vend_fail)} -
     {max (q1, (q1, q3), vend_nothing, vend) (q1, (q1, q1), vend_nothing, vend_fail)}
     \<subseteq> {Max ({(q1, (q1, q3), vend_nothing, vend), (q1, (q1, q1), vend_nothing, vend_fail)} -
              {max (q1, (q1, q3), vend_nothing, vend) (q1, (q1, q1), vend_nothing, vend_fail)})}"
  by (simp add: max_nondeterminism)

lemma vend_nothing_doesnt_directly_subsume_vend_nothing_2: "\<not>directly_subsumes drinks2 q1 vend_nothing vend"
  apply (simp add: directly_subsumes_def vend_doesnt_subsume_vend_nothing_2)
  apply (rule_tac x="[(''select'', [Str ''coke''])]" in exI)
  by (simp add: gets_us_to_def possible_steps_q0)

lemma vend_doesnt_directly_subsume_vend_nothing_3: "\<not> directly_subsumes \<lparr>s0 = q0, T = merge_states q1 q2 (T drinks2)\<rparr> q1 vend vend_nothing"
  using vend_nothing_doesnt_directly_subsume_vend vend_nothing_doesnt_directly_subsume_vend_nothing_2 by auto

lemma good_max: "Max ({(q1, (q1, q3), vend_nothing, vend), (q1, (q1, q1), vend_nothing, vend_fail)} -
               {max (q1, (q1, q3), vend_nothing, vend) (q1, (q1, q1), vend_nothing, vend_fail)}) = (q1, (q1, q1), vend_nothing, vend_fail)"
  by (simp add: max_def)

lemma vend_fail_doesnt_exit_q1: "\<not>exits_state drinks2 vend_fail q1"
  using vend_nothing_doesnt_directly_subsume_vend vend_nothing_doesnt_directly_subsume_vend_nothing_2 by auto

lemma coin_posterior: "posterior \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> cexp.Eq (Num 0)\<rbrakk> coin = \<lbrakk>V (R (Suc 0)) \<mapsto> cexp.Bc True, V (R 2) \<mapsto> Bc True\<rbrakk>"
  using posterior_coin_first by auto

lemma vend_nothing_doesnt_directly_subsume_vend_2: "\<not>directly_subsumes drinks2 q2 vend_fail vend_nothing"
  using vend_nothing_doesnt_directly_subsume_vend vend_nothing_doesnt_directly_subsume_vend_nothing_2 by auto

lemma vend_nothing_directly_subsumes_vend_fail: "directly_subsumes drinks2 q1 vend_nothing vend_fail"
  using vend_nothing_doesnt_directly_subsume_vend vend_nothing_doesnt_directly_subsume_vend_nothing_2 by auto

lemma finsert_vend_nothing: "finsert vend_nothing ({|vend_nothing, coin, vend_fail|} |-| {|vend_fail|}) = {|coin, vend_nothing|}"
  apply (simp add: transitions)
  by auto

definition coin50 :: "transition" where
"coin50 \<equiv> \<lparr>
        Label = ''coin'',
        Arity = 1,
        Guard = [(gexp.Eq (V (I 1)) (L (Num 50)))],
        Outputs = [Plus (V (R 2)) (V (I 1))],
        Updates = [
                    (R 1, V (R 1)),
                    (R 2, Plus (V (R 2)) (V (I 1)))
                  ]
      \<rparr>"

lemma "merge_2 drinks2 q1 q2 = Some (\<lambda> (a,b) .
  if (a, b) = (q0, q1) then {|select|} else
  if (a, b) = (q1,q1) then {|vend_nothing, coin|} else
  if (a, b) = (q1, q3) then {|vend|} else {||})"
  apply simp
  apply (case_tac "nondeterministic_transitions (merge_states q1 q2 (T drinks2))")
   apply (simp add: nondeterministic_transitions)
  apply (simp add: nondeterministic_transitions)
  apply (case_tac a)
  apply (case_tac b)
  apply simp
  apply (simp add: Let_def)
  apply clarify
  apply (simp only: nondeterminisitic_pairs not_subset)
  apply simp
  apply (simp add: nondeterminism_merge_q1_q2)
  apply (simp only: max_nondeterminism)
  apply simp
  apply (simp add: vend_doesnt_exit_q1 vend_nothing_exits_q1)
  apply (simp add: nondeterminsm_merge_q1_q3 nondet_pairs_simpler)
  apply (simp add: max_nondeterministic_transitions)
  apply (simp add: vend_exits_q1 vend_nothing_exits_q1_2)
  apply (simp add: merge_transitions.simps)
  apply (simp add: subset_nondet)
  apply (simp add: vend_doesnt_directly_subsume_vend_nothing_2)
  apply (simp add: vend_doesnt_directly_subsume_vend_nothing)
  apply (simp add: vend_nothing_doesnt_directly_subsume_vend_nothing_2)
  apply (simp add: vend_doesnt_directly_subsume_vend_nothing_3)
  apply (simp add: good_max)

  apply (simp add: vend_nothing_directly_subsumes_vend_fail)
  apply (simp add: replace_transition_def merge_q1_q2)
  apply (simp add: vend_nothing_exits_q1)

  apply (rule ext)
  apply (simp add: finsert_vend_nothing)
  by force

end