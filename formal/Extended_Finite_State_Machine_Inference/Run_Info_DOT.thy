theory Run_Info_DOT
imports "heuristics/PTA_Generalisation" EFSM_Dot
begin

code_printing
  constant "show_nat" \<rightharpoonup> (Scala) "Code'_Numeral.integer'_of'_nat((_)).toString()"
  | constant "show_int" \<rightharpoonup> (Scala) "Code'_Numeral.integer'_of'_int((_)).toString()"
  | constant "join" \<rightharpoonup> (Scala) "_.mkString((_))"

definition show_finfun :: "registers \<Rightarrow> String.literal" where
  "show_finfun l = STR ''''"

definition show_finfun_list :: "registers list \<Rightarrow> String.literal" where
  "show_finfun_list l = STR ''['' + (join (map (\<lambda>f. show_finfun f) l) STR '', '') + STR '']''"

code_printing constant "show_finfun" \<rightharpoonup> (Scala) "PrettyPrinter.dot((_))"

definition runinfo2dot :: "iEFSM \<Rightarrow> targeted_run_info \<Rightarrow> String.literal" where
"runinfo2dot e run_info = (
  let
    state_targets = map (\<lambda>(target, (state, _)). (state, target)) run_info;
    state_targets = foldr (\<lambda>(state, target) acc. acc(state := target#(acc state))) state_targets (\<lambda>x. [])
  in
  STR ''digraph EFSM{''+newline+
  STR ''  graph [rankdir=''+quote+(STR ''LR'')+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
  STR ''  node [color=''+quote+(STR ''black'')+quote+STR '', fillcolor=''+quote+(STR ''white'')+quote+STR '', shape=''+quote+(STR ''circle'')+quote+STR '', style=''+quote+(STR ''filled'')+quote+STR '', fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+
  STR ''  edge [fontname=''+quote+STR ''Latin Modern Math''+quote+STR ''];''+newline+newline+
   (join (map (\<lambda>s. STR ''  s''+show_nat s+STR ''[label=<s<sub>'' +show_nat s+ STR ''</sub><br/>'' + show_finfun_list (state_targets s) + STR ''>];'') (sorted_list_of_fset (S e))) (newline))+newline+newline+
   (join ((map (\<lambda>(uid, (from, to), t). STR ''  s''+(show_nat from)+STR ''->s''+(show_nat to)+STR ''[label=<<i> [''+show_nats (sort uid)+STR '']''+(transition2dot t)+STR ''</i>>];'') (sorted_list_of_fset e))) newline)+newline+
  STR ''}''
)"



end