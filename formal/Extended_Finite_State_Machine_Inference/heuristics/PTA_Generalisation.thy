section\<open>PTA Generalisation\<close>
text\<open>The problem with the simplistic heuristics of \cite{foster2019} is that the performance of the
Inference technique is almost entirely dependent on the quality and applicability of the heuristics
provided to it. Producing high quality heuristics often requires some inside knowledge of the system
under inference. If the user has this knowledge already, they are unlikely to require automated
inference. Ideally, we would like something more generally applicable. This theory presents a more
abstract \emph{metaheuristic} which can be implemented with genetic programming.\<close>

theory PTA_Generalisation
  imports "../Inference" Same_Register Group_By "HOL-Library.Sublist"
begin

hide_const I

datatype value_type = I | R | S

instantiation value_type :: linorder begin
fun less_value_type :: "value_type \<Rightarrow> value_type \<Rightarrow> bool" where
  "less_value_type I I = False" |
  "less_value_type I _ = True" |
  "less_value_type R S = True" |
  "less_value_type R _ = False" |
  "less_value_type S _ = False"

definition less_eq_value_type :: "value_type \<Rightarrow> value_type \<Rightarrow> bool" where
 "less_eq_value_type v1 v2 \<equiv> (v1 < v2 \<or> v1 = v2)"

instance
  apply standard
  apply (metis less_eq_value_type_def less_value_type.elims(2) less_value_type.simps(5) value_type.distinct(3) value_type.distinct(5))
     apply (simp add: less_eq_value_type_def)
    apply (metis less_eq_value_type_def less_value_type.elims(2) less_value_type.simps(3))
  apply (metis less_eq_value_type_def less_value_type.elims(2) less_value_type.simps(5))
  by (metis (full_types) less_eq_value_type_def less_value_type.simps(2) less_value_type.simps(3) less_value_type.simps(4) value_type.exhaust)
end

fun type_signature :: "value \<Rightarrow> value_type" where
  "type_signature (value.Str _) = S" |
  "type_signature (value.Int _) = I" |
  "type_signature (value.Real _) = R"


\<comment> \<open>This is a very hacky way of making sure that things with differently typed outputs don't get
    lumped together.\<close>
fun typeSig :: "output_function \<Rightarrow> value_type" where
  "typeSig (L v) = type_signature v" |
  "typeSig _ = R"


definition same_structure :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "same_structure t1 t2 = (
    Label t1 = Label t2 \<and>
    Arity t1 = Arity t2 \<and>
    map typeSig (Outputs t1) = map typeSig (Outputs t2)
  )"
hide_const S
hide_const I
hide_const R

type_synonym abstract_event = "(String.literal \<times> value_type list \<times> value_type list)"

definition event_structure :: "event \<Rightarrow> abstract_event" where
  "event_structure e = (let (l, i, p) = e in (l, map type_signature i, map type_signature p))"

fun events_transitions :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (tids \<times> abstract_event) list \<Rightarrow> (tids \<times> abstract_event) list" where
  "events_transitions _ _ _ [] tt = rev tt" |
  "events_transitions e s r ((l, i, p)#trace) tt = (
  let
    (id, s', t) = fthe_elem (i_possible_steps e s r l i);
    r' = evaluate_updates t i r
  in
    events_transitions e s' r' trace ((id, event_structure (l, i, p))#tt)
  )"

(*
fun trace_history :: "(tids \<times> abstract_event) list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list" where
  "trace_history [] acc = rev acc" |
  "trace_history ((tids, structure)#t) [] = trace_history t [(tids, structure, [])]" |
  "trace_history ((tids, structure)#t) ((tids', prev_structure, history)#t') = (
    if structure = prev_structure then
      trace_history t ((tids, structure, history)#(tids', prev_structure, history)#t')
    else
      trace_history t ((tids, structure, prev_structure#history)#(tids', structure, history)#t')
  )"
*)

fun remove_consecutive_duplicates :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_consecutive_duplicates [] acc = rev acc" |
  "remove_consecutive_duplicates (h#t) [] = remove_consecutive_duplicates t [h]" |
  "remove_consecutive_duplicates (h#t) (h'#t') = (
    if h = h' then
      remove_consecutive_duplicates t (h'#t')
    else
      remove_consecutive_duplicates t (h#h'#t')
  )"

definition trace_history :: "(tids \<times> abstract_event) list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list" where
  "trace_history l = (
    let
      transition_ids = map fst l;
      abstract_events = map snd l;
      groups = group_by (=) abstract_events;
      group_histories = prefixes (remove_consecutive_duplicates abstract_events []);
      group_lengths = map length groups;
      repeats = foldr (@) (map (\<lambda>(x, y). repeat x y) (zip group_lengths group_histories)) []
    in
      zip transition_ids (zip abstract_events repeats)
  )"

definition trace_history2 :: "(tids \<times> abstract_event) list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list" where
  "trace_history2 l = (
    let
      transition_ids = map fst l;
      abstract_events = map snd l;
      group_histories = map (\<lambda>l. remove_consecutive_duplicates l []) (prefixes abstract_events)
  in
      zip transition_ids (zip abstract_events group_histories)
  )"


(*
definition trace_history :: "(tids \<times> abstract_event) list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list" where
  "trace_history l = (
    let
      transition_ids = map fst l;
      abstract_events = map snd l;
      distinct_prefixes = map remdups (prefixes abstract_events)
    in
      zip transition_ids (zip abstract_events distinct_prefixes)
  )"
*)

type_synonym transition_group = "(tids \<times> transition) list"

definition historical_groups :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group list" where
  "historical_groups e log = (
    let
      observed = map (\<lambda>t. events_transitions e 0 <> t []) log;
      histories = map (\<lambda>t. trace_history t) observed;
      flat = fold (@) histories [];
      groups_fun = fold (\<lambda>(id, structure, history) gps. gps((structure, history) $:= id # (gps $ (structure, history)))) flat (K$ []);
      groups = sort (map (\<lambda>k. let (structure, history) = k in (length history, history, groups_fun $ k)) (finfun_to_list groups_fun))
    in
    sort (map sort (map remdups (map (\<lambda>(_, history, tids). map (\<lambda>id. (id, get_by_ids e id)) tids) groups)))
  )"

definition historical_groups2 :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group list" where
  "historical_groups2 e log = (
    let
      observed = map (\<lambda>t. events_transitions e 0 <> t []) log;
      histories = map (\<lambda>t. trace_history2 t) observed;
      flat = fold (@) histories [];
      groups_fun = fold (\<lambda>(id, structure, history) gps. gps((structure, history) $:= id # (gps $ (structure, history)))) flat (K$ []);
      groups = sort (map (\<lambda>k. let (structure, history) = k in (length history, history, groups_fun $ k)) (finfun_to_list groups_fun))
    in
    map (\<lambda>(_, history, tids). map (\<lambda>id. (id, get_by_ids e id)) tids) groups
  )"

lemma same_structure_equiv:
  "Outputs t1 = [L (value.Int m)] \<Longrightarrow> Outputs t2 = [L (value.Int n)] \<Longrightarrow>
   same_structure t1 t2 = Transition.same_structure t1 t2"
  by (simp add: same_structure_def Transition.same_structure_def)

fun place_in_group :: "(tids \<times> abstract_event \<times> abstract_event list) \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list list" where
  "place_in_group e closed [] = closed@[[e]]" |
  "place_in_group e closed (gp#groups) = (
    let
      (ids, abs_event, history) = e;
      (ids', abs_event', history') = hd gp
    in
    if abs_event = abs_event' \<and> history = history' then
      ((e#gp)#groups)
    else
      place_in_group e (gp#closed) groups
  )"

fun group_transitions :: "(tids \<times> abstract_event \<times> abstract_event list) list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list list \<Rightarrow> (tids \<times> abstract_event \<times> abstract_event list) list list" where
  "group_transitions [] gs = gs" |
  "group_transitions (h#t) gs = group_transitions t (place_in_group h [] gs)"

\<comment>\<open>TODO: Codegen this and test it
definition historical_groups :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group list" where
  "historical_groups e log = (
    let
      observed = map (\<lambda>t. events_transitions e 0 <> t []) log;
      histories = map trace_history observed;
      groups = fold (\<lambda>history acc. group_transitions history acc) histories [];
      ids = map (map fst) groups
    in
     map (map (\<lambda>id. (id, get_by_ids e id))) ids
  )"
\<close>
fun observe_all :: "iEFSM \<Rightarrow>  cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> transition_group" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r ((l, i, _)#es)  =
    (case random_member (i_possible_steps e s r l i)  of
      (Some (ids, s', t)) \<Rightarrow> (((ids, t)#(observe_all e s' (evaluate_updates t i r) es))) |
      _ \<Rightarrow> []
    )"

fun same_types :: "value \<times> value \<Rightarrow> bool" where
  "same_types (value.Int _, value.Int _) = True" |
  "same_types (value.Str _, value.Str _) = True" |
  "same_types (value.Real _, value.Real _) = True" |
  "same_types _ = False"

fun same_event_structure :: "event \<Rightarrow> event \<Rightarrow> bool" where
  "same_event_structure (l1, i1, o1) (l2, i2, o2) = (
    l1 = l2 \<comment>\<open>Same label\<close>
    \<and> length i1 = length i2 \<and> (\<forall>ip \<in> set (zip i1 i2). same_types ip)  \<comment>\<open>Same number and types of inputs\<close>
    \<and> length o1 = length o2 \<and> (\<forall>op \<in> set (zip o1 o2). same_types op)  \<comment>\<open>Same number and types of outputs\<close>
  )"

definition transition_groups_exec :: "iEFSM \<Rightarrow> trace \<Rightarrow> (nat \<times> tids \<times> transition) list list" where
  "transition_groups_exec e t = map (\<lambda>l. map snd l)
                                (group_by (\<lambda>(e1, _, _, t1) (e2, _, _, t2). same_event_structure e1 e2)
                                (zip t (enumerate 0 (observe_all e 0 <> t))))"

type_synonym struct = "(label \<times> arity \<times> value_type list)"

text\<open>We need to take the list of transition groups and tag them with the last transition that was
taken which had a different structure.\<close>
fun tag :: "struct option \<Rightarrow> (nat \<times> tids \<times> transition) list list \<Rightarrow> (struct option \<times> struct \<times> (nat \<times> tids \<times> transition) list) list" where
  "tag _ [] = []" |
  "tag t (g#gs) = (
    let
      (_, _, head) = hd g;
      struct = (Label head, Arity head, map typeSig (Outputs head))
    in
    (t, struct, g)#(tag (Some struct) gs)
  )"

text\<open>We need to group transitions not just by their structure but also by their history - i.e. the
last transition which was taken which had a different structure. We need to order these groups by
their relative positions within the traces such that output and update functions can be inferred in
the correct order.\<close>
definition transition_groups :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group list" where
  "transition_groups e l = (
    let
      trace_groups = map (transition_groups_exec e) l;
      tagged = map (tag None) trace_groups;
      flat =  sort (fold (@) tagged []);
      group_fun = fold (\<lambda>(tag, s, gp) f. f((tag, s) $:= gp@(f$(tag, s)))) flat (K$ []);
      grouped = map (\<lambda>x. group_fun $ x) (finfun_to_list group_fun);
      inx_groups = map (\<lambda>gp. (Min (set (map fst gp)), map snd gp)) grouped
    in
      map snd (sort inx_groups)
  )"

text\<open>For a given trace group, log, and EFSM, we want to build the training set for that group. That
is, the set of inputs, registers, and expected outputs from those transitions. To do this, we must
walk the traces in the EFSM to obtain the register values.\<close>
fun trace_group_training_set :: "transition_group \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (inputs \<times> registers \<times> value list) list \<Rightarrow> (inputs \<times> registers \<times> value list) list" where
  "trace_group_training_set _ _ _ _ [] train = train" |
  "trace_group_training_set gp e s r ((l, i, p)#t) train = (
    let
      (ids, s', transition) = fthe_elem (i_possible_steps e s r l i)
    in
    if \<exists>(ids', _) \<in> set gp. ids' = ids then
      \<comment>\<open>If we've got consecutive transitions, these *might* be update a register without us knowing\<close>
      if \<exists>(prev_ids, _) \<in> set gp. \<exists>id \<in> set ids. \<exists>id' \<in> set prev_ids. id' = id - 1 then
        trace_group_training_set gp e s' (evaluate_updates transition i r) t ((i, <>, p)#train)
      else
        trace_group_training_set gp e s' (evaluate_updates transition i r) t ((i, r, p)#train)
    else
      trace_group_training_set gp e s' (evaluate_updates transition i r) t train
  )"

definition make_training_set :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group \<Rightarrow> (inputs \<times> registers \<times> value list) list" where
  "make_training_set e l gp = fold (\<lambda>h a. trace_group_training_set gp e 0 <> h a) l []"

lemma trace_group_training_set_empty: "trace_group_training_set [] e s r l acc = acc"
proof(induct l arbitrary: e s r)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by (cases a, simp)
qed

primrec replace_groups :: "transition_group list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "replace_groups [] e = e" |
  "replace_groups (h#t) e = replace_groups t (fold (\<lambda>(id, t) acc. replace_transition acc id t) h e)"

lemma replace_groups_fold [code]:
  "replace_groups xs e = fold (\<lambda>h acc'. (fold (\<lambda>(id, t) acc. replace_transition acc id t) h acc')) xs e"
  by (induct xs arbitrary: e,  auto)

definition insert_updates :: "transition \<Rightarrow> update_function list \<Rightarrow> transition" where
  "insert_updates t u = (
    let
      \<comment> \<open>Want to filter out null updates of the form rn := rn. It doesn't affect anything but it  \<close>
      \<comment> \<open>does make things look cleaner. We also don't want duplicate update functions.            \<close>
      necessary_updates = filter (\<lambda>(r, u). u \<noteq> V (R r)) u
    in
    t\<lparr>Updates := (filter (\<lambda>(r, _). r \<notin> set (map fst u)) (Updates t))@necessary_updates\<rparr>
  )"

fun add_groupwise_updates_trace :: "trace  \<Rightarrow> (tids \<times> update_function list) list \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> iEFSM" where
  "add_groupwise_updates_trace [] _ e _ _ = e" |
  "add_groupwise_updates_trace ((l, i, _)#trace) funs e s r = (
    let
      (id, s', t) = fthe_elem (i_possible_steps e s r l i);
      updated = evaluate_updates t i r;
      newUpdates = List.maps snd (filter (\<lambda>(tids, _). set id \<subseteq> set tids) funs);
      t' = insert_updates t newUpdates;
      updated' = apply_updates (Updates t') (join_ir i r) r;
      necessaryUpdates = filter (\<lambda>(r, _). updated $ r \<noteq> updated' $ r) newUpdates;
      t'' = insert_updates t necessaryUpdates;
      e' = replace_transition e id t''
    in
    add_groupwise_updates_trace trace funs e' s' updated'
  )"

primrec add_groupwise_updates :: "log  \<Rightarrow> (tids \<times> update_function list) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "add_groupwise_updates [] _ e = e" |
  "add_groupwise_updates (h#t) funs e = add_groupwise_updates t funs (add_groupwise_updates_trace h funs e 0 <>)"

lemma fold_add_groupwise_updates [code]:
  "add_groupwise_updates log funs e = fold (\<lambda>trace acc. add_groupwise_updates_trace trace funs acc 0 <>) log e"
  by (induct log arbitrary: e, auto)

\<comment> \<open>This will be replaced to calls to Z3 in the executable\<close>
definition get_regs :: "(vname \<Rightarrow>f String.literal) \<Rightarrow> inputs \<Rightarrow> vname aexp \<Rightarrow> value \<Rightarrow> registers" where
  "get_regs types inputs expression output = Eps (\<lambda>r. aval expression (join_ir inputs r) = Some output)"

declare get_regs_def [code del]
code_printing constant get_regs \<rightharpoonup> (Scala) "Dirties.getRegs"

type_synonym action_info = "(cfstate \<times> registers \<times> registers \<times> inputs \<times> tids \<times> transition)"
type_synonym run_info = "action_info list"
type_synonym targeted_run_info = "(registers \<times> action_info) list"

fun everything_walk :: "output_function \<Rightarrow> nat \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> trace \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> transition_group \<Rightarrow> run_info" where
  "everything_walk _ _ _ [] _ _ _ _ = []" |
  "everything_walk f fi types ((label, inputs, outputs)#t) oPTA s regs gp  = (
    let (tid, s', ta) = fthe_elem (i_possible_steps oPTA s regs label inputs) in
     \<comment> \<open>Possible steps with a transition we need to modify\<close>
    if \<exists>(tid', _) \<in> set gp. tid = tid' then
      (s, regs, get_regs types inputs f (outputs!fi), inputs, tid, ta)#(everything_walk f fi types t oPTA s' (evaluate_updates ta inputs regs) gp)
    else
      let empty = <> in
      (s, regs, empty, inputs, tid, ta)#(everything_walk f fi types t oPTA s' (evaluate_updates ta inputs regs) gp)
  )"

definition everything_walk_log :: "output_function \<Rightarrow> nat \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> transition_group \<Rightarrow> run_info list" where
  "everything_walk_log f fi types log e gp = map (\<lambda>t. everything_walk f fi types t e 0 <> gp) log"

fun target :: "registers \<Rightarrow> run_info \<Rightarrow> targeted_run_info" where
  "target _ [] = []" |
  "target tRegs ((s, oldregs, regs, inputs, tid, ta)#t) = (
    let newTarget = if finfun_to_list regs = [] then tRegs else regs in
    (tRegs, s, oldregs, regs, inputs, tid, ta)#target newTarget t
  )"

fun target_tail :: "registers \<Rightarrow> run_info \<Rightarrow> targeted_run_info \<Rightarrow> targeted_run_info" where
  "target_tail _ [] tt = rev tt" |
  "target_tail tRegs ((s, oldregs, regs, inputs, tid, ta)#t) tt = (
    let newTarget = if finfun_to_list regs = [] then tRegs else regs in
    target_tail newTarget t ((tRegs, s, oldregs, regs, inputs, tid, ta)#tt)
  )"

lemma target_tail: "(rev bs)@(target tRegs ts) = target_tail tRegs ts bs"
proof(induct ts arbitrary: bs tRegs)
  case (Cons a ts)
  then show ?case
    apply (cases a)
    apply simp
    apply standard
    by (metis (no_types, lifting) append_eq_append_conv2 rev.simps(2) rev_append rev_swap self_append_conv2)+
qed simp

definition "target_fold tRegs ts b = fst (fold (\<lambda>(s, oldregs, regs, inputs, tid, ta) (acc, tRegs).
let newTarget = if finfun_to_list regs = [] then tRegs else regs in
    (acc@[(tRegs, s, oldregs, regs, inputs, tid, ta)], newTarget)
) ts (rev b, tRegs))"

lemma target_tail_fold: "target_tail tRegs ts b = target_fold tRegs ts b"
proof(induct ts arbitrary: tRegs b)
  case Nil
  then show ?case
    by (simp add: target_fold_def)
next
  case (Cons a ts)
  then show ?case
    apply (cases a)
    by (simp add: target_fold_def)
qed

lemma target_fold [code]: "target tRegs ts = target_fold tRegs ts []"
  by (metis append_self_conv2 rev.simps(1) target_tail_fold target_tail)

\<comment> \<open>This will be replaced by symbolic regression in the executable\<close>
definition get_update :: "label \<Rightarrow> nat \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> vname aexp option" where
  "get_update _ reg values train = (let
    possible_funs = {a. \<forall>(i, r, r') \<in> set train. aval a (join_ir i r) = r' $ reg}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs))
  )"

declare get_update_def [code del]
code_printing constant get_update \<rightharpoonup> (Scala) "Dirties.getUpdate"

definition get_updates_opt :: "label \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> (nat \<times> vname aexp option) list" where
  "get_updates_opt l values train = (let
    updated_regs = fold List.union (map (finfun_to_list \<circ> snd \<circ> snd) train) [] in
    map (\<lambda>r.
      let targetValues = remdups (map (\<lambda>(_, _, regs). regs $ r) train) in
      if  (\<forall>(_, anteriorRegs, posteriorRegs) \<in> set train. anteriorRegs $ r = posteriorRegs $ r) then
        (r, Some (V (R r)))
      else if length targetValues = 1 \<and> (\<forall>(inputs, anteriorRegs, _) \<in> set train. finfun_to_list anteriorRegs = []) then
        case hd targetValues of Some v \<Rightarrow>
        (r, Some (L v))
      else
        (r, get_update l r values train)
    ) updated_regs
  )"

definition finfun_add :: "(('a::linorder) \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_add a b = fold (\<lambda>k f. f(k $:= b $ k)) (finfun_to_list b) a"

definition group_update :: "value list \<Rightarrow> targeted_run_info \<Rightarrow> (tids \<times> (nat \<times> vname aexp) list) option" where
  "group_update values l = (
    let
      (_, (_, _, _, _, _, t)) = hd l;
      targeted = filter (\<lambda>(regs, _). finfun_to_list regs \<noteq> []) l;
      maybe_updates = get_updates_opt (Label t) values (map (\<lambda>(tRegs, s, oldRegs, regs, inputs, tid, ta). (inputs, finfun_add oldRegs regs, tRegs)) targeted)
    in
    if \<exists>(_, f_opt) \<in> set maybe_updates. f_opt = None then
      None
    else
      Some (fold List.union (map (\<lambda>(tRegs, s, oldRegs, regs, inputs, tid, ta). tid) l) [], map (\<lambda>(r, f_o). (r, the f_o)) maybe_updates)
  )"

fun groupwise_put_updates :: "transition_group list \<Rightarrow> log \<Rightarrow> value list \<Rightarrow> run_info list \<Rightarrow> (nat \<times> (vname aexp \<times> vname \<Rightarrow>f String.literal)) \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "groupwise_put_updates [] _ _ _ _  e = e" |
  "groupwise_put_updates (gp#gps) log values walked (o_inx, (op, types)) e = (
    let
      targeted = map (\<lambda>x. filter (\<lambda>(_, _, _, _, _, id, tran). (id, tran) \<in> set gp) x) (map (\<lambda>w. rev (target <> (rev w))) walked);
      group = fold List.union targeted []
    in
    case group_update values group of
      None \<Rightarrow> groupwise_put_updates gps log values walked (o_inx, (op, types)) e |
      Some u \<Rightarrow> groupwise_put_updates gps log values walked (o_inx, (op, types)) (make_distinct (add_groupwise_updates log [u] e))
  )"

definition updates_for_output :: "log \<Rightarrow> value list \<Rightarrow> transition_group \<Rightarrow> nat \<Rightarrow> vname aexp \<Rightarrow> vname \<Rightarrow>f String.literal \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
"updates_for_output log values current o_inx op types e = (
  if AExp.enumerate_regs op = {} then e
  else
    let
      walked = everything_walk_log op o_inx types log e current;
      groups = transition_groups e log
    in
    groupwise_put_updates groups log values walked (o_inx, (op, types)) e
  )"

type_synonym output_types = "(vname aexp \<times> vname \<Rightarrow>f String.literal)"

fun put_updates :: "log \<Rightarrow> value list \<Rightarrow> transition_group \<Rightarrow> nat \<Rightarrow> (nat \<times> output_types option) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "put_updates _ _ _ _ [] e = e" |
  "put_updates log values gp mreg ((_, None)#ops) e = put_updates log values gp mreg ops e" |
  "put_updates log values gp mreg ((o_inx, Some (op, types))#ops) e = (
    let
      gp' = map (\<lambda>(id, t). (id, t\<lparr>Outputs := list_update (Outputs t) o_inx op\<rparr>)) gp;
      generalised_model = fold (\<lambda>(id, t) acc. replace_transition acc id t) gp' e
    in
     if accepts_log (set log) (tm generalised_model) then
      put_updates log values gp' mreg ops generalised_model
    else
    let
      e' = updates_for_output log values gp o_inx op types generalised_model
    in
    if accepts_log (set log) (tm e') then
     put_updates log values gp' mreg ops e'
    else
     put_updates log values gp mreg ops e
  )"

fun unzip_3 :: "('a \<times> 'b \<times> 'c) list \<Rightarrow> ('a list \<times> 'b list \<times> 'c list)" where
  "unzip_3 [] = ([], [], [])" |
  "unzip_3 ((a, b, c)#l) = (
    let (as, bs, cs) = unzip_3 l in
    (a#as, b#bs, c#cs)
  )"

lemma unzip_3: "unzip_3 l = (map fst l, map (fst \<circ> snd) l, map (snd \<circ> snd) l)"
  by (induct l, auto)

fun unzip_3_tailrec_rev :: "('a \<times> 'b \<times> 'c) list \<Rightarrow> ('a list \<times> 'b list \<times> 'c list) \<Rightarrow> ('a list \<times> 'b list \<times> 'c list)" where
  "unzip_3_tailrec_rev [] (as, bs, cs) = (as, bs, cs)" |
  "unzip_3_tailrec_rev ((a, b, c)#t) (as, bs, cs) = unzip_3_tailrec_rev t (a#as, b#bs, c#cs)"

lemma unzip_3_tailrec_rev: "unzip_3_tailrec_rev l (as, bs, cs) = ((map_tailrec_rev fst l as), (map_tailrec_rev (fst \<circ> snd) l bs), (map_tailrec_rev (snd \<circ> snd) l cs))"
  by (induct l arbitrary: as bs cs, auto)

definition "unzip_3_tailrec l = (let (as, bs, cs) = unzip_3_tailrec_rev l ([],[],[]) in (rev as, rev bs, rev cs))"

lemma unzip_3_tailrec [code]: "unzip_3 l = unzip_3_tailrec l"
  apply (simp only: unzip_3_tailrec_def unzip_3_tailrec_rev)
  by (simp add: Let_def map_tailrec_rev unzip_3 map_eq_map_tailrec)

text\<open>We want to return an aexp which, when evaluated in the correct context accounts for the literal
input-output pairs within the training set. This will be replaced by symbolic regression in the
executable\<close>
definition get_output :: "label \<Rightarrow> nat \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> value) list \<Rightarrow> (vname aexp \<times> (vname \<Rightarrow>f String.literal)) option" where
  "get_output _ maxReg values train = (let
    possible_funs = {a. \<forall>(i, r, p) \<in> set train. aval a (join_ir i r) = Some p}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs), (K$ STR ''int''))
  )"
declare get_output_def [code del]
code_printing constant get_output \<rightharpoonup> (Scala) "Dirties.getOutput"

definition get_outputs :: "label \<Rightarrow> nat \<Rightarrow> value list \<Rightarrow> inputs list \<Rightarrow> registers list \<Rightarrow> value list list \<Rightarrow> (vname aexp \<times> (vname \<Rightarrow>f String.literal)) option list" where
  "get_outputs l maxReg values I r outputs = map_tailrec (\<lambda>(maxReg, ps). get_output l maxReg values (zip I (zip r ps))) (enumerate maxReg (transpose outputs))"

definition enumerate_exec_values :: "trace \<Rightarrow> value list" where
  "enumerate_exec_values vs = fold (\<lambda>(_, i, p) I. List.union (List.union i p) I) vs []"

definition enumerate_log_values :: "log \<Rightarrow> value list" where
  "enumerate_log_values l = fold (\<lambda>e I. List.union (enumerate_exec_values e) I) l []"

definition replace_transition_outputs_updates :: "iEFSM \<Rightarrow> tids \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace_transition_outputs_updates e uid new = (fimage (\<lambda>(uids, (from, to), t). if set uid \<subseteq> set uids then (uids, (from, to), t\<lparr>Outputs:=Outputs new, Updates:=Updates new\<rparr>) else (uids, (from, to), t)) e)"

definition replace_all_outputs_updates :: "iEFSM \<Rightarrow> tids list \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace_all_outputs_updates e ids new = fold (\<lambda>id acc. replace_transition_outputs_updates acc id new) ids e"

definition "search_for t gp e log= accepts_log (set log) (tm (replace_all e (map fst gp) t))"

(*This is where the types stuff originates*)
definition generalise_and_update :: "log \<Rightarrow> iEFSM \<Rightarrow> transition_group \<Rightarrow> transition_group list \<Rightarrow> iEFSM" where
  "generalise_and_update log e gp gps = (
    let
      label = Label (snd (hd gp));
      values = enumerate_log_values log;
      new_gp_ts = make_training_set e log gp;
      (I, R, P) = unzip_3 new_gp_ts;
      max_reg = max_reg_total e;
      \<comment>\<open> TODO: We want to record output funs and types as we infer them! \<close>
      outputs = get_outputs label max_reg values I R P
    in
      put_updates log values gp max_reg (enumerate 0 outputs) e
      \<comment> \<open>fold (\<lambda>gp e'. put_updates log values gp max_reg (enumerate 0 outputs) e') (gp#gps) e\<close>

  )"

text \<open>Splitting structural groups up into subgroups by previous transition can cause different
subgroups to get different updates. We ideally want structural groups to have the same output and
update functions, as structural groups are likely to be instances of the same underlying behaviour.\<close>
definition standardise_group :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group \<Rightarrow> (iEFSM \<Rightarrow> log \<Rightarrow> transition_group \<Rightarrow> transition_group) \<Rightarrow> (iEFSM \<times> tids list)" where
  "standardise_group e l gp s = (
    let
      standardised = s e l gp;
      e' = replace_transitions e standardised
    in
      if e' = e then (e, map fst standardised) else
      if accepts_log (set l) (tm e') then (e', map fst standardised) else (e, [])
)"

primrec find_outputs :: "output_function list list \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> transition_group \<Rightarrow> output_function list option" where
  "find_outputs [] _ _ _ = None" |
  "find_outputs (h#t) e l g = (
    let
      outputs = fold (\<lambda>(tids, t) acc. replace_transition acc tids (t\<lparr>Outputs := h\<rparr>)) g e
    in
      if accepts_log (set l) (tm outputs) then
        Some h
      else
        find_outputs t e l g
  )"

primrec find_updates_outputs :: "update_function list list \<Rightarrow> output_function list list \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> transition_group \<Rightarrow> (output_function list \<times> update_function list) option" where
  "find_updates_outputs [] _ _ _ _ = None" |
  "find_updates_outputs (h#t) p e l g = (
    let
      updates = fold (\<lambda>(tids, t) acc. replace_transition acc tids (t\<lparr>Updates := h\<rparr>)) g e
    in
      case find_outputs p updates l (map (\<lambda>(id, t). (id,t\<lparr>Updates := h\<rparr>))  g) of
        Some pp \<Rightarrow> Some (pp, h) |
        None \<Rightarrow> find_updates_outputs t p e l g
  )"

definition updates_for :: "update_function list \<Rightarrow> update_function list list" where
  "updates_for U = (
    let uf = fold (\<lambda>(r, u) f. f(r $:= u#(f $ r))) U (K$ []) in
    map (\<lambda>r. map (\<lambda>u. (r, u)) (uf $ r)) (finfun_to_list uf)
  )"

definition standardise_group_outputs_updates :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group \<Rightarrow> transition_group" where
  "standardise_group_outputs_updates e l g = (
    let
      update_groups = product_lists (updates_for (remdups (List.maps (Updates \<circ> snd) g)));
      update_groups_subs = fold (List.union \<circ> subseqs) update_groups [];
      output_groups = product_lists (transpose (remdups (map (Outputs \<circ> snd) g)))
    in
    case find_updates_outputs update_groups_subs output_groups e l g of
      None \<Rightarrow> g |
      Some (p, u) \<Rightarrow> map (\<lambda>(id, t). (id, t\<lparr>Outputs := p, Updates := u\<rparr>)) g
  )"

fun find_first_use_of_trace :: "nat \<Rightarrow> trace \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> tids option" where
  "find_first_use_of_trace _ [] _ _ _ = None" |
  "find_first_use_of_trace rr ((l, i, _)#es) e s r = (
    let
      (id, s', t) = fthe_elem (i_possible_steps e s r l i)
    in
      if (\<exists>p \<in> set (Outputs t). aexp_constrains p (V (R rr))) then
        Some id
      else
        find_first_use_of_trace rr es e s' (evaluate_updates t i r)
  )"

definition find_first_uses_of :: "nat \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> tids list" where
  "find_first_uses_of r l e = List.maps (\<lambda>x. case x of None \<Rightarrow> [] | Some x \<Rightarrow> [x]) (map (\<lambda>t. find_first_use_of_trace r t e 0 <>) l)"

fun find_initialisation_of_trace :: "nat \<Rightarrow> trace \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> (tids \<times> transition) option" where
  "find_initialisation_of_trace _ [] _ _ _ = None" |
  "find_initialisation_of_trace r' ((l, i, _)#es) e s r = (
    let
      (tids, s', t) = fthe_elem (i_possible_steps e s r l i)
    in
    if (\<exists>(rr, u) \<in> set (Updates t). rr = r' \<and> is_lit u) then
      Some (tids, t)
    else
      find_initialisation_of_trace r' es e s' (evaluate_updates t i r)
  )"

primrec find_initialisation_of :: "nat \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) option list" where
  "find_initialisation_of _ _ [] = []" |
  "find_initialisation_of r e (h#t) = (
    case find_initialisation_of_trace r h e 0 <> of
      None \<Rightarrow> find_initialisation_of r e t |
      Some thing \<Rightarrow> Some thing#(find_initialisation_of r e t)
  )"

definition delay_initialisation_of :: "nat \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> tids list \<Rightarrow> iEFSM" where
  "delay_initialisation_of r l e tids = fold (\<lambda>x e. case x of
      None \<Rightarrow> e |
    Some (i_tids, t) \<Rightarrow>
      let
        origins = map (\<lambda>id. origin id e) tids;
        init_val = snd (hd (filter (\<lambda>(r', _). r = r') (Updates t)));
        e' = fimage (\<lambda>(id, (origin', dest), tr).
        \<comment> \<open>Add the initialisation update to incoming transitions\<close>
        if dest \<in> set origins then
          (id, (origin', dest), tr\<lparr>Updates := List.insert (r, init_val) (Updates tr)\<rparr>)
        \<comment> \<open>Strip the initialisation update from the original initialising transition\<close>
        else if id = i_tids then
          (id, (origin', dest), tr\<lparr>Updates := filter (\<lambda>(r', _). r \<noteq> r') (Updates tr)\<rparr>)
        else
          (id, (origin', dest), tr)
      ) e
      in
      \<comment> \<open>We don't want to update a register twice so just leave it\<close>
      if accepts_log (set l) (tm e') then
        e'
      else
        e
  ) (find_initialisation_of r e l) e"

fun groupwise_generalise_and_update :: "log \<Rightarrow> iEFSM \<Rightarrow> transition_group list \<Rightarrow> tids list \<Rightarrow> (transition \<times> output_types option list) list \<Rightarrow> (iEFSM \<times> tids list \<times> (transition \<times> output_types option list) list)" where
  "groupwise_generalise_and_update _ e [] to_derestrict closed = (e, to_derestrict, closed)" |
  "groupwise_generalise_and_update log e (gp#t) to_derestrict closed = (
        let
          rep = snd (hd (gp));
          structural_groups = filter (\<lambda>gp'. same_structure rep (snd (hd (gp')))) t;
          e' = generalise_and_update log e gp structural_groups;
          structural_group = fimage (\<lambda>(i, _, t). (i, t)) (ffilter (\<lambda>(_, _, t). same_structure rep t) e');
          delayed = fold (\<lambda>r acc. delay_initialisation_of r log acc (find_first_uses_of r log acc)) (sorted_list_of_set (all_regs e')) e';
          (standardised, more_to_derestrict) = standardise_group delayed log (sorted_list_of_fset structural_group) standardise_group_outputs_updates;
          structural_group2 = fimage (\<lambda>(_, _, t). (Outputs t, Updates t)) (ffilter (\<lambda>(_, _, t).  Label rep = Label t \<and> Arity rep = Arity t \<and> length (Outputs rep) = length (Outputs t)) standardised)
        in
        \<comment> \<open>If we manage to standardise a structural group, we do not need to evolve outputs and
            updates for the other historical subgroups so can filter them out.\<close>
        if fis_singleton structural_group2 then
          groupwise_generalise_and_update log (merge_regs standardised (accepts_log (set log))) (filter (\<lambda>g. set g \<inter> fset structural_group = {}) t) (to_derestrict @ more_to_derestrict) []
        else
          groupwise_generalise_and_update log (merge_regs standardised (accepts_log (set log))) t (to_derestrict @ more_to_derestrict) []
  )"

definition drop_all_guards :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
"drop_all_guards e pta log m np = (let
      derestricted = fimage (\<lambda>(id, tf, tran). (id, tf, tran\<lparr>Guards := []\<rparr>)) e;
      nondeterministic_pairs = sorted_list_of_fset (np derestricted)
    in
    case resolve_nondeterminism {} nondeterministic_pairs pta derestricted m (accepts_log (set log)) np of
      (None, _) \<Rightarrow> pta |
      (Some resolved, _) \<Rightarrow> resolved
  )"

definition updated_regs :: "transition \<Rightarrow> nat set" where
  "updated_regs t = set (map fst (Updates t))"

definition fewer_updates :: "transition \<Rightarrow> transition fset \<Rightarrow> transition option" where
  "fewer_updates t tt = (
    let p = ffilter (\<lambda>t'. same_structure t t' \<and> Outputs t = Outputs t' \<and> updated_regs t' \<subset> updated_regs t) tt in
    if p = {||} then None else Some (snd (fMin (fimage (\<lambda>t. (length (Updates t), t)) p))))"

fun remove_spurious_updates_aux :: "iEFSM \<Rightarrow> transition_group \<Rightarrow> transition fset \<Rightarrow> log \<Rightarrow> iEFSM" where
  "remove_spurious_updates_aux e [] _ _ = e" |
  "remove_spurious_updates_aux e ((tid, t)#ts) tt l = (
    case fewer_updates t tt of
      None \<Rightarrow> remove_spurious_updates_aux e ts tt l |
      Some t' \<Rightarrow> (
        let e' = replace_transition e tid t' in
        if accepts_log (set l) (tm e') then
          remove_spurious_updates_aux e' ts tt l
        else
          remove_spurious_updates_aux e ts tt l
      )
  )"

(* This goes through and tries to remove spurious updates that get introduced during preprocessing *)
definition remove_spurious_updates :: "iEFSM \<Rightarrow> log \<Rightarrow> iEFSM" where
  "remove_spurious_updates e l = (
    let transitions = fimage (\<lambda>(tid, _, t). (tid, t)) e in
      remove_spurious_updates_aux e (sorted_list_of_fset transitions) (fimage snd transitions) l
  )"

definition drop_selected_guards :: "iEFSM \<Rightarrow> tids list \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
"drop_selected_guards e ids pta log m np = (let
      derestricted = fimage (\<lambda>(id, tf, tran). (id, tf, if id \<in> set ids then tran\<lparr>Guards := []\<rparr> else tran)) e;
      nondeterministic_pairs = sorted_list_of_fset (np derestricted)
    in
    case resolve_nondeterminism {} nondeterministic_pairs pta derestricted m (accepts_log (set log)) np of
      (None, _) \<Rightarrow> pta |
      (Some resolved, _) \<Rightarrow> resolved
  )"

fun tidy_updates :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "tidy_updates [] = []" |
  "tidy_updates ((a, b)#t) = (if a \<in> set (map fst t) then tidy_updates t else (a, b)#(tidy_updates t))"

definition derestrict :: "iEFSM \<Rightarrow> log \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "derestrict pta log m np = (
    let
      groups = historical_groups pta log;
      (normalised, to_derestrict, _) = groupwise_generalise_and_update log pta groups [] [];
      tidied = fimage (\<lambda>(id, tf, t). (id, tf, t\<lparr>Updates:= tidy_updates (Updates t)\<rparr>)) normalised
    in
      drop_selected_guards tidied to_derestrict pta log m np
  )"

definition "drop_pta_guards pta log m np = drop_all_guards pta pta log m np"

end
