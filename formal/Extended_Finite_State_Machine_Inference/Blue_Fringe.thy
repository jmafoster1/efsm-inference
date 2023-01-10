theory Blue_Fringe
imports Inference EFSM_Dot SelectionStrategies
begin

unbundle finfun_syntax

datatype colour = Red | Blue | White

fun show_colour :: "colour \<Rightarrow> String.literal" where
  "show_colour Red = STR ''red''" |
  "show_colour Blue = STR ''royalblue''" |
  "show_colour White = STR ''white''"

definition score_state_pair :: "tids fset \<Rightarrow> tids fset \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> nat" where
  "score_state_pair tids tids' e strat = fSum (fimage (\<lambda>(t, t'). strat t t' e) (tids |\<times>| tids'))"

definition score_merge_size :: strategy where
  "score_merge_size rt bt e = (if naive_score rt bt e = 0 then 0 else size e - (size (merge {} e (origin rt e) (origin bt e) (\<lambda> _ _ _ _ _ _ _. None) (\<lambda>_. True) nondeterministic_pairs)))"

(*function resolve_nondeterminism :: "(cfstate \<times> cfstate) set \<Rightarrow> nondeterministic_pair list \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> (iEFSM option \<times> (cfstate \<times> cfstate) set)" where*)
definition score :: "(cfstate \<Rightarrow>f colour) \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> scoreboard" where
  "score f e strat = (
    let
      states_transitions = fimage (\<lambda>s. (s, fimage (snd \<circ> snd) (outgoing_transitions s e))) (S e);
      red = ffilter (\<lambda>(s, _). f $ s = Red) states_transitions;
      blue = ffilter (\<lambda>(s, _). f $ s = Blue) states_transitions;
      pairs = red |\<times>| blue;
      bonus_scores = bonus_score e
    in
      ffilter (\<lambda>s. Score s > 0) (scoreboard_add bonus_scores (fimage (\<lambda>((rs, rt), (bs, bt)). \<lparr>Score=score_state_pair rt bt e strat, S1=rs, S2=bs\<rparr>) pairs))
  )"

definition update_red_blue :: "(cfstate \<times> cfstate) set \<Rightarrow> score fset \<Rightarrow> (cfstate \<Rightarrow>f colour) \<Rightarrow> (cfstate \<Rightarrow>f colour)" where
  "update_red_blue failed_merges scores f = fold (\<lambda>(red, blue) acc. if \<exists>s |\<in>| scores. S2 s = blue \<and> acc $ (S1 s) = Red \<and> acc $ (S2 s) = Blue then acc else acc(blue $:= Blue)) (sorted_list_of_set failed_merges) f"

lemma card_ffilter: "card (fset (ffilter f s)) \<le> card (fset s)"
  by (simp add: card_mono)

(* inference_step - attempt dest carry out a single step of the inference process by merging the  *)
(* @param e - an iEFSM dest be generalised                                                        *)
(* @param ((s, s1, s2)#t) - a list of triples of the form (score, state, state) dest be merged    *)
(* @param m     - an update modifier function which tries dest generalise transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
function inference_step :: "(cfstate \<Rightarrow>f colour) \<Rightarrow> iEFSM \<Rightarrow> score fset \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "inference_step f e scores m check np = (
    if scores = {||} then e else
    let
      scores = ffilter (\<lambda>s. S1 s |\<in>| S e \<and> S2 s |\<in>| S e) scores
    in if scores = {||} then e else
    let
      h = fMin scores;
      t = scores - {|h|}
    in
    case merge {} e (S1 h) (S2 h) m check np of
      (Some new, _) \<Rightarrow> inference_step f new t m check np |
      (None, _) \<Rightarrow> inference_step f e t m check np
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(_, _, s, _, _, _). size s]")
    apply simp
   apply simp
   apply (metis (no_types, lifting) card_ffilter card_minus_fMin card.insert_remove card_Diff1_less_iff filter_fset insert_Diff insert_Diff_single le_imp_less_Suc not_le)
  apply simp
  by (metis (no_types, lifting) card_ffilter card_minus_fMin card.insert_remove card_Diff1_less_iff filter_fset insert_Diff insert_Diff_single le_imp_less_Suc not_le)

definition iefsm2dot_red_blue :: "iEFSM \<Rightarrow> (cfstate \<Rightarrow>f colour) \<Rightarrow> String.literal" where
  "iefsm2dot_red_blue e f = STR ''digraph EFSM{''+newline+
                 STR ''  graph [rankdir=''+quote+(STR ''LR'')+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                 STR ''  node [color=''+quote+(STR ''black'')+quote+STR '', fillcolor=''+quote+(STR ''white'')+quote+STR '', shape=''+quote+(STR ''circle'')+quote+STR '', style=''+quote+(STR ''filled'')+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
                 STR ''  edge [fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+newline+
                  STR ''  s0[fillcolor=''+quote+show_colour (f $ 0)+quote+STR '', label=<s<sub>0</sub>>];''+newline+
                  (join (map (\<lambda>s. STR ''  s''+show_nat s+STR ''[fillcolor=''+quote+show_colour (f $ s)+quote+STR ''label=<s<sub>'' +show_nat s+ STR ''</sub>>];'') (sorted_list_of_fset (S e - {|0|}))) (newline))+newline+newline+
                  (join ((map (\<lambda>(uid, (from, to), t). STR ''  s''+(show_nat from)+STR ''->s''+(show_nat to)+STR ''[label=<<i> [''+show_nats (sort uid)+STR '']''+(transition2dot t)+STR ''</i>>];'') (sorted_list_of_fset e))) newline)+newline+
                STR ''}''"

definition logStates :: "iEFSM \<Rightarrow> (cfstate \<Rightarrow>f colour) \<Rightarrow> nat \<Rightarrow> unit" where
  "logStates _ _  _ = ()"

(* Takes an iEFSM and iterates inference_step until no further states can be successfully merged  *)
(* @param failedMerges - a set of states which cannot be merged                                   *)
(* @param k - an iEFSM dest be generalised                                                        *)
(* @param e - an iEFSM dest be generalised                                                        *)
(* @param r - a strategy dest identify and prioritise pairs of states dest merge                  *)
(* @param m     - an update modifier function which tries dest generalise transitions             *)
(* @param check - a function which takes an EFSM and returns a bool dest ensure that certain
                  properties hold in the new iEFSM                                                *)
function infer :: "(cfstate \<Rightarrow>f colour) \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "infer f e r m check np = (
    let
      dotstring = iefsm2dot_red_blue e f;
      scores = score f e r;
      new = inference_step f e scores m check np;
      all_red = fold (\<lambda>c acc. acc(c $:= Red)) (finfun_to_list f) f;
      new_blue_states =  fimage fst (fold (|\<union>|) (map (\<lambda>s. outgoing_transitions s e) (finfun_to_list all_red)) {||});
      new_blue_children = fold (\<lambda>s acc. if acc $ s = White then acc(s $:= Blue) else acc) (sorted_list_of_fset new_blue_states) all_red;
      temp2 = logStates new new_blue_children (size (Inference.S e))
    in
    if (ffilter (\<lambda>s. new_blue_children $ s = White) (S new)) |\<subset>| (ffilter (\<lambda>s. f $ s = White) (S e)) then infer new_blue_children new r m check np else e
  )"
  by auto
termination
  apply (relation "measures [\<lambda>( f, e, _). size (ffilter (\<lambda>s. f $ s = White) (S e))]")
   apply simp
  apply (thin_tac "x = iefsm2dot_red_blue e f")
  apply (thin_tac "xa = score f e r")
  apply (thin_tac "xb = Blue_Fringe.inference_step f e xa m check np")
  apply (thin_tac "xc = fold (\<lambda>c acc. acc(c $:= Red)) (finfun_to_list f) f")
  apply (thin_tac "xd = fst |`| fold (|\<union>|) (map (\<lambda>s. Inference.outgoing_transitions s e) (finfun_to_list xc)) {||}")
  apply (thin_tac "xe = fold (\<lambda>s acc. if acc $ s = White then acc(s $:= Blue) else acc) (sorted_list_of_fset xd) xc")
  apply (thin_tac "xf = logStates xb xe (size (Inference.S e))")
  by (simp, metis Abs_ffilter filter_fset size_ffilter_card size_fsubset)

definition learn :: "nat \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "learn n pta l r m np = (
     let
        check = accepts_log (set l);
        blue_states = fimage fst (outgoing_transitions 0 pta);
        colours = fold (\<lambda>s acc. acc(s $:= Blue)) (sorted_list_of_fset blue_states) ((K$ White)(0 $:= Red))
     in
         (infer colours pta r m check np)
   )"
unbundle no_finfun_syntax

end