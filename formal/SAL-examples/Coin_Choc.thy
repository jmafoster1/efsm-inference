theory Coin_Choc
imports EFSM_LTL
begin

declare One_nat_def [simp del]

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
        Label = (STR ''coin''),
        Arity = 0,
        Guard = [Gt (V (R 1)) (L (Num 0))],
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

(* make_full_observation drinks (Some 0) Map.empty t *)
lemma make_full_observation_unfold: "make_full_observation drinks (Some 0) Map.empty t = (let (s', o', d') =
                                     ltl_step drinks (Some 0) Map.empty (shd t) in
                                      \<lparr>statename = (Some 0), datastate = Map.empty, event=(shd t), output = o'\<rparr>##(make_full_observation drinks s' d' (stl t)))"
  using make_full_observation.code by blast

lemma make_full_obs_neq: "make_full_observation drinks (fst (ltl_step drinks (Some 0) Map.empty (shd t))) (snd (snd (ltl_step drinks (Some 0) Map.empty (shd t))))
     (stl t) \<noteq>
    make_full_observation drinks (Some 0) Map.empty t"
  apply (simp add: make_full_observation_unfold)
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

lemma unfold_observe_none: "make_full_observation e None d t = (\<lparr>statename = None, datastate = d, event=(shd t), output = []\<rparr>##(make_full_observation e None d (stl t)))"
  by (simp add: stream.expand)


lemma "alw (StateEq None) (make_full_observation e None r t)"
  using alw_coinduct[of "StateEq None" "make_full_observation e None r t" "StateEq None"]
  apply simp
  oops


lemma "alw (nxt (StateEq (Some 2)) impl (LabelEq ''vend'')) (watch drinks t)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd t")
    apply (case_tac "a = STR ''init'' \<and> b = []")
     defer
    apply (simp add: possible_steps_not_init)
    apply (simp add: possible_steps_init)
qed


lemma "alw (\<lambda>s. StateEq None (stl s)) (make_full_observation drinks None Map.empty t)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: StateEq_def)
    oops

lemma "alw (nxt (StateEq (Some 2)) impl checkInx rg 2 ValueGt (Some (Num 100))) (watch drinks t)"
  apply (simp only: alw_ev)
  apply simp
  apply safe
  apply (rule ev.cases)
    apply simp
  using Coin_Choc.aux1 apply auto[1]
  apply simp
  apply clarify
  apply simp
  apply (case_tac "shd t")
    apply (case_tac "a = STR ''init'' \<and> b = []")
   apply (simp add: possible_steps_init)
   defer
  apply (simp add: possible_steps_not_init)

lemma "alw (nxt (StateEq (Some 2)) impl checkInx rg 2 ValueGt (Some (Num 100))) (watch drinks t)"
proof(coinduction)
  case alw
  then show ?case
    apply simp
    apply standard
     apply (simp add: ValueGt_def aux1)
    apply (simp add: make_full_obs_neq)
    apply (case_tac "shd t")
    apply simp
    apply (case_tac "a = STR ''init'' \<and> b = []")
     apply (simp add: possible_steps_init)
     defer
     apply (simp add: possible_steps_not_init)

qed


end