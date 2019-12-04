theory PTA_Generalisation
  imports "Symbolic_Regression"
begin

definition same_structure :: "'a transition_ext \<Rightarrow> 'a transition_ext \<Rightarrow> bool" where
  "same_structure t1 t2 = (
    Label t1 = Label t2 \<and>
    Arity t1 = Arity t2 \<and>
    length (Outputs t1) = length (Outputs t2)
  )"

primrec insert_into_group :: "(tids \<times> 'a transition_ext) list list \<Rightarrow> (tids \<times> 'a transition_ext) \<Rightarrow> (tids \<times> 'a transition_ext) list list" where
  "insert_into_group [] pair = [[pair]]" |
  "insert_into_group (h#t) pair = (
    if \<forall>(_, t) \<in> set h. same_structure (snd pair) t then
      ((List.insert pair h))#t
    else
      h#(insert_into_group t pair)
    )"

definition transition_groups :: "iEFSM \<Rightarrow> (tids \<times> transition) list list" where
  "transition_groups e = fold (\<lambda>(tid, _, transition) acc. insert_into_group acc (tid, transition)) (sorted_list_of_fset e) []"

(* Assign registers and inputs with associated outputs to the correct training set based on       *)
(* transition id                                                                                  *)
definition assign_training_set :: "(((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list \<Rightarrow> tids \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> value list \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list" where
  "assign_training_set data tids label inputs registers outputs = map (\<lambda>gp. 
    let (transitions, trainingSet) = gp in
    if \<exists>(tids', _) \<in> set transitions. tids' = tids then
      (transitions, (registers, inputs, outputs)#trainingSet)
    else
      gp
  ) data"

fun trace_training_set :: "iEFSM \<Rightarrow> execution \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list" where
  "trace_training_set _ [] _ _ ts = ts" |
  "trace_training_set e ((label, inputs, outputs)#t) s r ts = (
    let (id, s', transition) = fthe_elem (i_possible_steps e s r label inputs) in
    trace_training_set e t s' (apply_updates (Updates transition) (join_ir inputs r) r) (assign_training_set ts id label inputs r outputs)
  )"

primrec log_training_set :: "iEFSM \<Rightarrow> log \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list" where
  "log_training_set _ [] ts = ts" |
  "log_training_set e (h#t) ts = log_training_set e t (trace_training_set e h 0 <> ts)"

(* This will generate the training sets in the same order that the PTA was built, i.e. traces     *)
(* that appear earlier in the logs will appear earlier in the list of training sets. This allows  *)
(* us to infer register updates according to trace precidence so  we won't get redundant updates  *)
(* on later transitions which spoil the data state                                                *)
definition make_training_set :: "iEFSM \<Rightarrow> log \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list" where
  "make_training_set e l = log_training_set e l (map (\<lambda>x. (x, [])) (transition_groups e))"

\<comment> \<open>This will be replaced by symbolic regression in the executable\<close>
definition get_output :: "nat \<Rightarrow> value list \<Rightarrow> inputs list \<Rightarrow> registers list \<Rightarrow> value list \<Rightarrow> (aexp \<times> (vname \<Rightarrow>f String.literal)) option" where
  "get_output maxReg values I r P = (let
    possible_funs = {a. \<forall>(i, r, p) \<in> set (zip I (zip r P)). aval a (join_ir i r) = Some p}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs), (K$ STR ''int''))
  )"
declare get_output_def [code del]
code_printing constant get_output \<rightharpoonup> (Scala) "Dirties.getOutput"

definition get_outputs :: "nat \<Rightarrow> value list \<Rightarrow> inputs list \<Rightarrow> registers list \<Rightarrow> value list list \<Rightarrow> (aexp \<times> (vname \<Rightarrow>f String.literal)) option list" where
  "get_outputs maxReg values I r outputs = map (\<lambda>ps. get_output maxReg values I r ps) (transpose outputs)" 

fun put_outputs :: "(((aexp \<times> (vname \<Rightarrow>f String.literal)) option) \<times> aexp) list \<Rightarrow> aexp list" where
  "put_outputs [] = []" |
  "put_outputs ((None, p)#t) = p#(put_outputs t)" |
  "put_outputs ((Some (p, _), _)#t) = p#(put_outputs t)"

type_synonym output_types = "(nat \<times> (aexp \<times> vname \<Rightarrow>f String.literal) option) list"

(*This is where the types stuff originates*)
definition generalise_outputs :: "value list \<Rightarrow> ((tids \<times> transition) list \<times> (registers \<times> value list \<times> value list) list) list \<Rightarrow> (tids \<times> transition \<times> output_types) list list" where
  "generalise_outputs values groups = map (\<lambda>(maxReg, group).
    let
      I = map (\<lambda>(regs, ins, outs).ins) (snd group);
      R = map (\<lambda>(regs, ins, outs).regs) (snd group);
      P = map (\<lambda>(regs, ins, outs).outs) (snd group);
      outputs = get_outputs maxReg values I R P
    in
    map (\<lambda>(id, tran). (id, \<lparr>Label = Label tran, Arity = Arity tran, Guard = Guard tran, Outputs = put_outputs (zip outputs (Outputs tran)), Updates = Updates tran\<rparr>, enumerate 0 outputs)) (fst group)
  ) (enumerate 0 groups)"

definition replace_transition :: "iEFSM \<Rightarrow> tids \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace_transition e uid new = (fimage (\<lambda>(uids, (from, to), t). if set uid \<subseteq> set uids then (uids, (from, to), new) else (uids, (from, to), t)) e)"

primrec replace_groups :: "(tids \<times> transition) list list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "replace_groups [] e = e" |
  "replace_groups (h#t) e = (replace_groups t (fold (\<lambda>(id, t) acc. replace_transition acc id t) h e))"

definition pta_generalise_outputs :: "log \<Rightarrow> (iEFSM \<times> ((tids \<times> transition \<times> output_types) list list))" where
  "pta_generalise_outputs log = (
    let
      values = enumerate_log_values log;
      pta = make_pta log {||};
      training_set = make_training_set pta log;
      generalised_outs = generalise_outputs values training_set
    in (replace_groups (map (\<lambda>lst. map (\<lambda>(tids, tran, types). (tids, tran)) lst) generalised_outs) pta, generalised_outs)
  )"

definition insert_updates :: "transition \<Rightarrow> update_function list \<Rightarrow> transition" where
  "insert_updates t u = (
    let
      \<comment> \<open>Need to derestrict variables which occur in the updates but keep unrelated ones to avoid \<close>
      \<comment> \<open>nondeterminism creeping in too early in the inference process                            \<close>
      relevant_vars = image V (fold (\<lambda>(r, u) acc. acc \<union> (AExp.enumerate_vars u)) u {});
      \<comment> \<open>Want to filter out null updates of the form rn := rn. It doesn't affect anything but it  \<close>
      \<comment> \<open>does make things look cleaner                                                            \<close>
      necessary_updates = filter (\<lambda>(r, u). u \<noteq> V (R r)) u
    in
    \<lparr>Label = Label t, Arity = Arity t, Guard = (Guard t), Outputs = Outputs t, Updates = (filter (\<lambda>(r, _). r \<notin> set (map fst u)) (Updates t))@necessary_updates\<rparr>
  )"

fun add_groupwise_updates :: "(tids \<times> update_function list) option list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "add_groupwise_updates [] e = e" |
  "add_groupwise_updates (None#t) e = add_groupwise_updates t e" |
  "add_groupwise_updates (Some (tids, u)#t) e = (
    let
      newTransitions = map (\<lambda>tid. (insert_updates (get_by_id e tid) u)) tids;
      replacements = zip (map (\<lambda>id. [id]) tids) newTransitions
    in
    add_groupwise_updates t (replace_transitions e replacements)
  )"

fun put_updates :: "log \<Rightarrow> value list \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> arity \<Rightarrow> output_types \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_updates _ _ _ _ _ [] e = Some e" |
  "put_updates _ _ _ _ _ ((_, None)#_) _ = None" |
  "put_updates log values label ia oa ((o_inx, (Some (op, types)))#ops) lit = (
    let
      walked = everything_walk_log op o_inx types log lit label ia oa;
      targeted = map (\<lambda>w. rev (target <> (rev w))) walked;
      groups = group_by_structure (fold List.union targeted []) [];
      group_updates = groupwise_updates values groups;
      updated = make_distinct (add_groupwise_updates group_updates lit)
    in
      put_updates log values label ia oa ops updated
  )"

fun update_groups :: "log \<Rightarrow> value list \<Rightarrow> (transition \<times> output_types) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "update_groups _ _ [] e = e" |
  "update_groups log values ((tran, types)#lst) e = (
    case put_updates log values (Label tran) (Arity tran) (length (Outputs tran)) types e of
      None \<Rightarrow> update_groups log values lst e |
      Some e' \<Rightarrow> update_groups log values lst e'
  )"

definition strip_redundant_updates :: "nat list \<Rightarrow> tids \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "strip_redundant_updates regs tids e = fimage (\<lambda>(id, tf, tran).
    if id = tids then
      (id, tf, tran\<lparr>Updates := filter (\<lambda>(r, _). r \<notin> set regs) (Updates tran)\<rparr>)
    else
      (id, tf, tran)
  ) e"

fun remove_redundant_updates :: "iEFSM \<Rightarrow> execution \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> iEFSM" where
  "remove_redundant_updates e [] _ _ = e" |
  "remove_redundant_updates e ((l, i, _)#t) s r = (
    let
      (tid, s', tran) = fthe_elem (i_possible_steps e s r l i);
      r' = apply_updates (Updates tran) (join_ir i r) r;
      redundantly_updated = map fst (filter (\<lambda>(rx, _). r $ rx = r' $ rx) (Updates tran))
    in
    remove_redundant_updates (strip_redundant_updates redundantly_updated tid e) t s' r'
  )"

primrec remove_redundant_updates_log :: "iEFSM \<Rightarrow> log \<Rightarrow> iEFSM" where
  "remove_redundant_updates_log e [] = e" |
  "remove_redundant_updates_log e (h#t) = remove_redundant_updates_log (remove_redundant_updates e h 0 <>) t"

definition normalised_pta :: "log \<Rightarrow> iEFSM" where
  "normalised_pta log = (
    let
      values = enumerate_log_values log;
      (output_funs, types) = pta_generalise_outputs log;
      group_details = map (snd \<circ> hd) types;
      updated = update_groups log values (rev group_details) output_funs
    in
      remove_redundant_updates_log updated log
  )"

end