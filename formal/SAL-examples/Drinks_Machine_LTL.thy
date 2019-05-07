theory Drinks_Machine_LTL
imports "../examples/Drinks_Machine" EFSM_LTL
begin

declare One_nat_def [simp del]

lemma LTL_r2_not_always_gt_100: "not (alw (checkInx rg 2 ValueGt (Some (Num 100)))) (watch drinks i)"
  apply (simp add: not_alw_iff watch_def)
  apply (rule ev.base)
  by (simp add: ValueGt_def)

lemma apply_updates_select: "length b = 1 \<Longrightarrow> EFSM.apply_updates (Updates select) (case_vname (\<lambda>n. input2state b 1 (I n)) Map.empty) Map.empty = <R 1 := hd b, R 2 := Num 0>"
  apply (rule ext)
  by (simp add: select_def hd_input2state)

lemma possible_steps_select_wrong_arity: "a = STR ''select'' \<Longrightarrow>
       length b \<noteq> 1 \<Longrightarrow>
       possible_steps drinks 0 Map.empty a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma possible_steps_0_not_select: "a \<noteq> STR ''select'' \<Longrightarrow>
       possible_steps drinks 0 Map.empty a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma LTL_nxt_2_means_vend: "alw (nxt (StateEq (Some 2)) impl (StateEq (Some 1))) (watch drinks i)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: watch_def)
    apply (case_tac "shd i")
    apply simp
    apply (case_tac "a = STR ''select''")
     apply (case_tac "length b = 1")
      apply (simp add: possible_steps_0 apply_updates_select)
      defer
      apply (simp add: possible_steps_select_wrong_arity)
      apply (metis (no_types, lifting) once_none_always_none StateEq_def alw.cases alw.coinduct option.distinct(1))
     apply (simp add: possible_steps_0_not_select)
     apply (metis (no_types, lifting) once_none_always_none StateEq_def alw.cases alw.coinduct option.distinct(1))
    apply standard
     apply (simp add: StateEq_def)
    apply (rule disjI2)
    oops

lemma LTL_costsMoney_aux: "(alw ((not (checkInx rg 2 ValueGt (Some (Num 100)))) impl (not (nxt (StateEq (Some 2)))))) (watch drinks i)"
  oops

  (* costsMoney: THEOREM drinks |- G(X(cfstate=State_2) => gval(value_ge(r_2, Some(NUM(100))))); *)
lemma LTL_costsMoney: "(alw ((nxt (StateEq (Some 2))) impl ((checkInx rg 2 ValueGt (Some (Num 100)))))) (watch drinks i)"
  oops

(* neverReachS2: THEOREM drinks |- label=select AND I(1) = STR(String_coke) AND
                                X(label=coin AND I(1) = NUM(100)) AND
                                X(X(label=vend AND I=InputSequence !empty)) => X(X(X(cfstate=State_2)));;*)
lemma LTL_neverReachS2:"(((((LabelEq ''select'') aand (checkInx ip 1 ValueEq (Some (Str ''coke''))))
                    aand
                    (nxt ((LabelEq ''coin'') aand (checkInx ip 1 ValueEq (Some (Num 100))))))
                    aand
                    (nxt (nxt((LabelEq ''vend'' aand (InputEq []))))))
                    impl
                    (nxt (nxt (nxt (StateEq (Some 2))))))
                    (watch drinks i)"
  oops

end