theory Coin_Choc_Broken
  imports EFSM_LTL
begin

declare One_nat_def [simp del]
declare ValueLt_def [simp]

definition init :: transition where
"init \<equiv> \<lparr>
        Label = (STR ''init''),
        Arity = 0,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (L (Num 0)))]
      \<rparr>"

definition coin :: transition where
"coin \<equiv> \<lparr>
        Label = (STR ''coin''),
        Arity = 0,
        Guard = [],
        Outputs = [],
        Updates = [(R 1, (Plus (V (R 1)) (L (Num 1))))]
      \<rparr>"

definition vend :: transition where
"vend \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guard = [GExp.Ge (V (R 1)) (L (Num 0))],
        Outputs = [],
        Updates = [(R 1, (Minus (V (R 1)) (L (Num 1))))]
      \<rparr>"

definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
          ((0,1), init),
          ((1,1), coin),
          ((1,2), vend)
          |}"

lemma "(not (LabelEq ''vend'') until (LabelEq ''coin'')) (watch drinks t)"
  oops

lemma possible_steps_init: "possible_steps drinks 0 Map.empty STR ''init'' [] = {|(1, init)|}"
    apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def drinks_def)
    apply safe
  by (simp_all add: init_def)

lemma possible_steps_not_init: "\<not> (a = STR ''init'' \<and> b = []) \<Longrightarrow> possible_steps drinks 0 Map.empty a b = {||}"
    apply (simp add: possible_steps_def Abs_ffilter Set.filter_def drinks_def)
    apply clarify
    by (simp add: init_def)

lemma aux1: "\<not> StateEq (Some 2)
        (make_full_observation drinks (fst (ltl_step drinks (Some 0) Map.empty (shd t)))
          (snd (snd (ltl_step drinks (Some 0) Map.empty (shd t)))) (stl t))"
proof-
  show ?thesis
    apply (case_tac "shd t")
    apply simp
    apply (case_tac "a = STR ''init'' \<and> b = []")
     apply (simp add: possible_steps_init StateEq_def)
    by (simp add: StateEq_def possible_steps_not_init)
qed

lemma make_full_obs_neq: "make_full_observation drinks (fst (ltl_step drinks (Some 0) Map.empty (shd t))) (snd (snd (ltl_step drinks (Some 0) Map.empty (shd t))))
     (stl t) \<noteq>
    make_full_observation drinks (Some 0) Map.empty t"
  apply (case_tac "ltl_step drinks (Some 0) Map.empty (shd t)")
  apply (case_tac "shd t")
    apply simp
    apply (case_tac "aa = STR ''init'' \<and> ba = []")
   apply (simp add: possible_steps_init init_def)
  apply (metis (no_types, lifting) make_full_observation.simps(1) option.inject state.ext_inject stream.sel(1) zero_neq_one)
  apply (simp add: possible_steps_not_init)
  by (metis make_full_observation.simps(1) option.simps(3) state.ext_inject stream.sel(1))

lemma state_none: "((StateEq None) impl nxt (StateEq None)) (make_full_observation e s r t)"
  by (simp add: StateEq_def)

lemma shd_state_is_none: "(StateEq None) (make_full_observation e None r t)"
  by (simp add: StateEq_def)

lemma state_none_2: "(StateEq None) (make_full_observation e s r t) \<Longrightarrow> (StateEq None) (make_full_observation e s r (stl t))"
  by (simp add: StateEq_def)

lemma alw_ev: "alw f = not (ev (\<lambda>s. \<not>f s))"
  by simp

lemma StateEq_alt: "alw (StateEq s) s' = alw (\<lambda>x. shd x = s) (smap (\<lambda>x. statename x) s')"
  apply standard
  apply (simp add: StateEq_def alw_iff_sdrop)
  by (simp add: StateEq_def alw_mono alw_smap)

lemma test: "statename (shd (make_full_observation e None r t)) = None"
  by simp

lemma "alw (nxt (StateEq (Some 2)) impl (LabelEq ''vend'')) (watch drinks t)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd t")
    apply (case_tac "a = STR ''init'' \<and> b = []")
     defer
     apply (simp add: possible_steps_not_init)
    oops


lemma "alw (\<lambda>s. StateEq None (stl s)) (make_full_observation drinks None Map.empty t)"
  by (metis alw_iff_sdrop once_none_always_none sdrop_simps(2))

lemma no_possible_steps: "possible_steps e s r (fst t) (snd t) = {||} \<Longrightarrow> ltl_step e (Some s) r t = (None, [], r)"
proof -
  assume "possible_steps e s r (fst t) (snd t) = {||}"
  then have "ltl_step e (Some s) r (fst t, snd t) = (None, [], r)"
    using ltl_step.simps(2) by presburger
  then show ?thesis
    by simp
qed

lemma no_possible_steps_not_init:"t \<noteq> (STR ''init'', []) \<Longrightarrow> possible_steps drinks 0 r (fst t) (snd t) = {||}"
  apply (simp add: possible_steps_def ffilter_def Set.filter_def drinks_def fset_both_sides Abs_fset_inverse)
  by (metis init_def length_0_conv less_numeral_extra(1) prod.collapse transition.ext_inject transition.surjective)

lemma step_not_init: "t \<noteq> (STR ''init'', []) \<Longrightarrow> ltl_step drinks (Some 0) r t = (None, [], r)"
  using no_possible_steps_not_init no_possible_steps
  by simp

lemma updates_init: "apply_updates (Updates init) (case_vname Map.empty Map.empty) Map.empty = <R 1 := Num 0>"
  apply (rule ext)
  by (simp add: init_def)

lemma ltl_step_alt [simp]:  "ltl_step e (Some s) r t = (let possibilities = possible_steps e s r (fst t) (snd t) in
                   if possibilities = {||} then (None, [], r)
                   else
                     let (s', t') = Eps (\<lambda>x. x |\<in>| possibilities) in
                     (Some s', (apply_outputs (Transition.Outputs t') (join_ir (snd t) r)), (apply_updates (Updates t') (join_ir (snd t) r) r))
                  )"
  apply (case_tac t)
  by (simp add: Let_def)

lemma possible_steps_coin: "possible_steps drinks 1 r STR ''coin'' [] = {|(1, coin)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def)

lemma possible_steps_vend_insufficient: "n \<le> 0 \<Longrightarrow> possible_steps drinks 1 <R 1 := Num n> STR ''vend'' [] = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def gval.simps ValueGt_def)

lemma possible_steps_vend_sufficient: "n > 0 \<Longrightarrow> possible_steps drinks 1 <R 1 := Num n> STR ''vend'' [] = {|(2, vend)|}"
  apply (simp add: possible_steps_alt ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: vend_def coin_def gval.simps ValueGt_def)

lemma invalid_possible_steps_1: "shd t \<noteq> (STR ''coin'', []) \<Longrightarrow>
    shd t \<noteq> (STR ''vend'', []) \<Longrightarrow> possible_steps drinks 1 r (fst (shd t)) (snd (shd t)) = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks_def Set.filter_def)
  by (metis coin_def length_0_conv prod.collapse transition.ext_inject transition.surjective vend_def)

lemma updates_coin: "(apply_updates (Updates coin) (case_vname Map.empty (\<lambda>na. if na = 1 then Some (Num n) else None)) <R 1 := Num n>) = <R 1 := Num (n + 1)>"
  apply (rule ext)
  by (simp add: coin_def)

lemma updates_vend: "(apply_updates (Updates vend) (case_vname Map.empty (\<lambda>na. if na = 1 then Some (Num n) else None)) <R 1 := Num n>) = <R 1 := Num (n - 1)>"
  apply (rule ext)
  by (simp add: vend_def)

lemma less_than_zero_not_nxt_2: "n \<le> 0 \<Longrightarrow> \<not>statename (shd (stl (make_full_observation drinks (Some 1) <R 1 := Num n> t))) = Some 2"
  apply (case_tac "shd t = (STR ''coin'', [])")
      apply (simp add: possible_steps_coin)
  apply (case_tac "shd t = (STR ''vend'', [])")
      apply (simp add: possible_steps_vend_insufficient ValueGt_def)
  by (simp add: invalid_possible_steps_1 StateEq_def)

lemma possible_steps_2: "possible_steps drinks 2 r (fst (shd t)) (snd (shd t)) = {||}"
  by (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)

lemma stop_at_2_old: "alw (\<lambda>xs. statename (shd (stl xs)) = Some 2 \<longrightarrow> MaybeBoolInt (\<lambda>x y. y < x) (datastate (shd xs) (R 1)) (Some (Num 0)) = trilean.true)
     (make_full_observation drinks (Some 2) <R 1 := Num (n - 1)> t)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: possible_steps_2)
    using once_none_always_none
    by (simp add: StateEq_def alw_iff_sdrop)
qed

lemma reg_simp: "(\<lambda>a. if a = R 1 then Some (Num n) else None) = <R 1 := Num n>"
  by (rule ext, simp)

lemma once_none_no_change_data: "alw (\<lambda>xs. (datastate (shd xs)) = r) (make_full_observation e None r t)"
proof(coinduction)
  case alw
  then show ?case
    apply simp
    by (simp add: all_imp_alw alw_inv)
qed

lemma shd_not_lt_zero: "0 \<le> n \<Longrightarrow> (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) (R 1)) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks None <R 1 := Num n> t)"
  by simp

lemma nxt_not_lt_zero: "0 \<le> n \<Longrightarrow> nxt (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) (R 1)) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks None <R 1 := Num n> t)"
  by simp

lemma once_none_remains_not_lt_zero: "0 \<le> n \<Longrightarrow> alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) (R 1)) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks None <R 1 := Num n> t)"
  using once_none_no_change_data
  by (simp add: alw_iff_sdrop)

lemma once_none_null_remains_not_lt_zero: "alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) (R 1)) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks None Map.empty t)"
  using once_none_no_change_data
  by (simp add: alw_iff_sdrop)

lemma stop_at_2: "0 \<le> n \<Longrightarrow>
      alw (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) (R 1)) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks (Some 2) <R 1 := Num n> t)"
proof(coinduction)
  case alw
  then show ?case
    by (simp add: possible_steps_2 once_none_remains_not_lt_zero)
qed

lemma next_not_lt_zero: "n \<ge> 0 \<Longrightarrow> nxt (\<lambda>xs. MaybeBoolInt (<) (datastate (shd xs) (R 1)) (Some (Num 0)) \<noteq> trilean.true) (make_full_observation drinks (Some 1) <R 1 := Num n> t)"
    apply simp
    apply (case_tac "shd t = (STR ''vend'', [])")
    apply (case_tac "n = 0")
      apply (simp add: possible_steps_vend_insufficient)
     apply (simp add: possible_steps_vend_sufficient updates_vend)
    apply (case_tac "shd t = (STR ''coin'', [])")
    defer
     apply (simp add: invalid_possible_steps_1)
  by (simp add: possible_steps_coin updates_coin)

lemma StateEq_None_not_Some: "StateEq None s \<Longrightarrow> \<not> StateEq (Some n) s"
  by (simp add: StateEq_def)

lemma not_initialised: "alw (\<lambda>xs. StateEq (Some 1) xs \<and>
              MaybeBoolInt (<) (datastate (shd xs) (R 1)) (Some (Num 0)) = trilean.true \<and> LabelEq ''vend'' xs \<and> InputEq [] xs \<longrightarrow>
              StateEq (Some 2) (stl xs))
     (make_full_observation drinks None Map.empty t)"
  using once_none_always_none StateEq_None_not_Some
  by (simp add: alw_iff_sdrop)

lemma implode_init: "String.implode ''init'' = STR ''init''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma not_init: "shd t \<noteq> (STR ''init'', []) \<Longrightarrow>
    LabelEq ''init'' (watch drinks t) \<Longrightarrow> \<not> InputEq [] (watch drinks t)"
  apply (simp add: LabelEq_def InputEq_def implode_init watch_def)
  by (metis prod.collapse)

lemma implode_vend: "String.implode ''vend'' = STR ''vend''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coin: "String.implode ''coin'' = STR ''coin''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma LTL_label_vend_not_2: "((LabelEq ''vend'') impl (not (ev (StateEq (Some 2))))) (watch drinks t)"
  apply (simp only: watch_label implode_vend not_ev_iff)
  apply (simp add: watch_def)
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: StateEq_def possible_steps_not_init)
    apply (rule disjI2)
    using once_none_always_none
    unfolding StateEq_def
    by (simp add: alw_iff_sdrop)
qed

lemma possible_steps_0: "possible_steps drinks 0 Map.empty l i = finsert x S' \<Longrightarrow> finsert x S' = {|(1, init)|}"
  apply (case_tac "l = STR ''init''")
   apply (case_tac "i = []")
    apply (simp add: possible_steps_init)
  using possible_steps_not_init
  by auto

lemma vend_insufficient: "possible_steps drinks 1 <R 1 := Num 0> STR ''vend'' i = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
   apply (simp add: coin_def)
  by (simp add: vend_def gval.simps ValueGt_def)

lemma LTL_aux2: "((nxt (LabelEq ''vend'')) impl not (ev (StateEq (Some 2)))) (watch drinks t)"
  apply (simp add: watch_def LabelEq_def implode_vend not_ev_iff)
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: StateEq_def)
    apply (case_tac "shd t = (STR ''init'', [])")
     defer
    using possible_steps_not_init alw_not_some
     apply (simp add: no_possible_steps_not_init)
    apply (simp add: possible_steps_init updates_init)
    apply (rule disjI2)
  proof(coinduction)
    case alw
    then show ?case
      apply (simp add: vend_insufficient)
      apply (rule disjI2)
      using alw_not_some
      by simp
  qed
qed

lemma LTL_init_makes_r_1_zero: "((LabelEq ''init'' aand InputEq []) impl nxt (checkInx rg 1 ValueEq (Some (Num 0)))) (watch drinks t)"
  apply (case_tac "shd t = (STR ''init'', [])")
   apply (simp add: possible_steps_init updates_init ValueEq_def watch_def)
  apply clarify
  using not_init
  by simp

lemma LTL_must_pay_wrong: "((not (LabelEq ''vend'' suntil LabelEq ''coin'')) suntil StateEq None) (watch drinks t)"
  oops

lemma shd_not_init: "shd t \<noteq> (STR ''init'', []) \<Longrightarrow> \<not> ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 0) Map.empty t)"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply (case_tac "shd t")
    apply simp
    by (simp add: possible_steps_not_init alw_not_some)
qed

lemma vend_gets_stuck: "stl t = (STR ''vend'', []) ## x2 \<Longrightarrow> \<not>ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 1) <R 1 := Num 0> ((STR ''vend'', []) ## x2))"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    by (simp add: vend_insufficient alw_not_some)
qed

lemma possible_steps_1_invalid: "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
       x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
       possible_steps drinks 1 <R 1 := Num 0> (fst x1) (snd x1) = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse drinks_def Set.filter_def)
  apply safe
   apply (simp add: coin_def)
   apply (metis prod.collapse)
  by (simp add: vend_def gval.simps ValueGt_def)


lemma invalid_gets_stuck: "x1 \<noteq> (STR ''coin'', []) \<Longrightarrow>
                           x1 \<noteq> (STR ''vend'', []) \<Longrightarrow>
                           \<not>ev (\<lambda>s. statename (shd s) = Some 2) (make_full_observation drinks (Some 1) <R 1 := Num 0> (x1 ## x2))"
  apply (simp add: not_ev_iff)
proof(coinduction)
  case alw
  then show ?case
    by (simp add: possible_steps_1_invalid alw_not_some)
qed

lemma LTL_vend_no_coin: "((nxt (LabelEq ''vend'' aand InputEq [])) impl not (ev (StateEq (Some 2)))) (watch drinks t)"
  apply (simp add: not_ev_iff event_components implode_vend watch_def StateEq_def)
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply (case_tac "shd t = (STR ''init'', [])")
     defer
    apply (simp add: decompose_pair)
     apply (simp add: possible_steps_not_init alw_not_some)
    apply (simp add: possible_steps_init updates_init)
    apply (rule disjI2)
  proof(coinduction)
    case alw
    then show ?case
      apply (simp add: vend_insufficient)
     by (simp add: possible_steps_not_init alw_not_some)
  qed
qed

lemma LTL_invalid_gets_stuck_2:
  "(((nxt (not (LabelEq ''coin'' aand InputEq []))) aand
   (nxt (not (LabelEq ''vend'' aand InputEq [])))) impl
   (not (ev (StateEq (Some 2))))) (watch drinks t)"
  apply (simp add: not_ev_iff event_components)
  unfolding watch_def StateEq_def LabelEq_def InputEq_def
  apply clarify
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: implode_coin implode_vend)
    apply (case_tac "shd t = (STR ''init'', [])")
     defer
     apply (simp only: decompose_pair)
    using possible_steps_not_init alw_not_some
     apply simp
    apply (simp add: possible_steps_init updates_init)
    apply (rule disjI2)
    using invalid_gets_stuck[of "shd (stl t)" "stl (stl t)"]
    by (simp add: alw_ev)
qed


(* Ramsay, this is the proof you want!
   I'll convert it to an Isabelle code snippet for the actual paper to make it really pretty but for
   now, just use a screenshot image or something... *)
lemma LTL_must_pay_correct: "((ev (StateEq (Some 2))) impl (not(LabelEq ''vend'') suntil LabelEq ''coin'')) (watch drinks t)"
  apply clarify
  unfolding LabelEq_def StateEq_def implode_vend implode_coin
  apply (simp add: watch_def)
  apply (case_tac "shd t = (STR ''init'', [])")
   defer
   apply (simp add: shd_not_init)
  apply (rule suntil.step)
   apply simp
  apply (simp add: possible_steps_init updates_init)
  apply (case_tac "shd (stl t) = (STR ''coin'', [])")
   apply (simp add: suntil.base)
  apply (case_tac "shd (stl t) = (STR ''vend'', [])")
   apply (rule suntil.step)
  using LTL_vend_no_coin[of t]
  apply (simp add: event_components implode_vend StateEq_def watch_def ev_mono)
  using LTL_vend_no_coin[of t]
  apply (simp add: event_components implode_vend StateEq_def watch_def ev_mono)
  using LTL_invalid_gets_stuck_2[of t]
  by (simp add: event_components implode_vend implode_coin StateEq_def watch_def ev_mono)

end
