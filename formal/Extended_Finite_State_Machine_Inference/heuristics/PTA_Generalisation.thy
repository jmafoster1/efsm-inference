section\<open>PTA Generalisation\<close>
text\<open>The problem with the simplistic heuristics of \cite{foster2019} is that the performance of the
Inference technique is almost entirely dependent on the quality and applicability of the heuristics
provided to it. Producing high quality heuristics often requires some inside knowledge of the system
under inference. If the user has this knowledge already, they are unlikely to require automated
inference. Ideally, we would like something more generally applicable. This theory presents a more
abstract \emph{metaheuristic} which can be implemented with genetic programming.\<close>

theory PTA_Generalisation
  imports "../Inference" Same_Register Group_By "HOL-Library.Sublist" "Extended_Finite_State_Machines.Drinks_Machine"
begin

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

definition finfun_filter :: "(('a::linorder) \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_filter F f = (
    let
      keys = filter f (finfun_to_list F)
    in
    fold (\<lambda>k acc. acc(k $:= (F $ k))) keys (K$ finfun_default F)
  )"

text\<open>For a given trace group, log, and EFSM, we want to build the training set for that group. That
is, the set of inputs, registers, and expected outputs from those transitions. To do this, we must
walk the traces in the EFSM to obtain the register values.\<close>
fun trace_group_training_set :: "transition_group \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> transition \<Rightarrow> trace \<Rightarrow> (inputs \<times> registers \<times> value list \<times> nat list) list \<Rightarrow> (inputs \<times> registers \<times> value list \<times> nat list) list" where
  "trace_group_training_set _ _ _ _ _ [] train = train" |
  "trace_group_training_set gp e s r last_tran ((l, i, p)#t) train = (
    let
      (ids, s', transition) = fthe_elem (i_possible_steps e s r l i);
      last_updated = map fst (Updates last_tran)
    in
    if \<exists>(ids', _) \<in> set gp. ids' = ids then
        trace_group_training_set gp e s' (evaluate_updates transition i r) transition t ((i, r, p, last_updated)#train)
    else
      trace_group_training_set gp e s' (evaluate_updates transition i r) transition t train
  )"

definition make_training_set :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group \<Rightarrow> (inputs \<times> registers \<times> value list \<times> nat list) list" where
  "make_training_set e l gp = fold (\<lambda>h a. trace_group_training_set gp e 0 <> \<lparr>Label=STR '''', Arity=0, Guards=[], Outputs=[], Updates=[]\<rparr> h a) l []"

lemma trace_group_training_set_empty: "trace_group_training_set [] e s r u l acc = acc"
proof(induct l arbitrary: e s r u)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by (cases a, simp)
qed

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

type_synonym funMem = "(String.literal \<Rightarrow>f (vname aexp \<times> (vname \<Rightarrow>f String.literal)) list)"

fun cartProdN :: "'a list list \<Rightarrow> 'a list list" where
"cartProdN as = foldr (\<lambda>xs as. [x # a. x <- xs , a <- as]) as [[]]"

definition correct_row :: "vname aexp \<Rightarrow> value list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> value \<Rightarrow> bool" where
  "correct_row a values i r expected = (
    let
      latent_vars = filter (\<lambda>x. r $ x = None) (sorted_list_of_set (AExp.enumerate_regs a));
      valuations = cartProdN (repeat (length latent_vars) values);
      assignments = map (zip latent_vars) valuations;
      update = fold (\<lambda>(reg, val) acc. acc(reg $:= Some val))
    in
    \<exists>assignment \<in> set assignments. aval a (join_ir i (update assignment r)) = Some expected
  )"

definition correct :: "vname aexp \<Rightarrow> output_function set \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> value \<times> nat list) list \<Rightarrow> bool" where
  "correct a bad values train = (a \<notin> bad \<and> (\<forall>(i, r, p, l) \<in> set train. correct_row a values i (fold (\<lambda>k acc. acc(k $:= None)) l r) p))"

\<comment> \<open>This will be replaced by symbolic regression in the executable\<close>
definition get_update_gp :: "label \<Rightarrow> nat \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> value \<times> nat list) list \<Rightarrow> vname aexp option" where
  "get_update_gp _ reg values train = (let
    possible_funs = {a. \<forall>(i, r, r', l) \<in> set train. aval a (join_ir i r) = Some r'}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs))
  )"

declare get_update_gp_def [code del]
code_printing constant get_update_gp \<rightharpoonup> (Scala) "Dirties.getUpdate"

definition get_update :: "funMem \<Rightarrow> label \<Rightarrow> nat \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> vname aexp option" where
  "get_update fun_mem label reg values train = (
    if (\<exists>(inputs, (aregs, pregs)) \<in> set train. pregs $ reg = None)
    then None
    else
      let ioPairs = remdups (map (\<lambda>(inputs, (aregs, pregs)). case pregs $ reg of Some v \<Rightarrow> (inputs, ((K$ None)(reg $:= aregs $ reg), v, []))) train) in
      case find (\<lambda>(a, _). correct a {} values ioPairs) (fun_mem $ label) of
        None \<Rightarrow> get_update_gp label reg values ioPairs |
        Some (u, _) \<Rightarrow> Some u
  )"

definition get_updates_opt :: "funMem \<Rightarrow> label \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> (nat \<times> vname aexp option) list" where
  "get_updates_opt fun_mem l values train = (let
    updated_regs = fold List.union (map (finfun_to_list \<circ> snd \<circ> snd) train) [] in
    map (\<lambda>r.
      let targetValues = remdups (map (\<lambda>(_, _, regs). regs $ r) train) in
      if  (\<forall>(_, anteriorRegs, posteriorRegs) \<in> set train. anteriorRegs $ r = posteriorRegs $ r) then
        (r, Some (V (R r)))
      else if length targetValues = 1 \<and> (\<forall>(inputs, anteriorRegs, _) \<in> set train. finfun_to_list anteriorRegs = []) then
        case hd targetValues of Some v \<Rightarrow> (r, Some (L v))
      else
        (r, get_update fun_mem l r values train)
    ) updated_regs
  )"

definition finfun_add :: "(('a::linorder) \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_add a b = fold (\<lambda>k f. f(k $:= b $ k)) (finfun_to_list b) a"

(*We only want to update transitions that need it*)
definition group_update :: "funMem \<Rightarrow> value list \<Rightarrow> targeted_run_info \<Rightarrow> (tids \<times> (nat \<times> vname aexp) list) option" where
  "group_update fun_mem values l = (
    let
      (_, _, _, _, _, _, t) = hd l;
      targeted = filter (\<lambda>(regs, _). finfun_to_list regs \<noteq> []) l;
      maybe_updates = get_updates_opt fun_mem (Label t) values (map (\<lambda>(tRegs, s, oldRegs, regs, inputs, tid, ta). (inputs, finfun_add oldRegs regs, tRegs)) targeted)
    in
    if \<exists>(_, f_opt) \<in> set maybe_updates. f_opt = None then
      None
    else
      let the_update_functions = map (\<lambda>(r, f_o). (r, the f_o)) maybe_updates in
      if \<forall>(r, fun) \<in> set the_update_functions. is_lit fun then
        Some (fold List.union (map (\<lambda>(tRegs, s, oldRegs, regs, inputs, tid, ta). tid) targeted) [], the_update_functions)
      else
        Some (fold List.union (map (\<lambda>(tRegs, s, oldRegs, regs, inputs, tid, ta). tid) l) [], the_update_functions)
  )"

type_synonym output_types = "(vname aexp \<times> vname \<Rightarrow>f String.literal)"

fun unzip_3 :: "('a \<times> 'b \<times> 'c) list \<Rightarrow> ('a list \<times> 'b list \<times> 'c list)" where
  "unzip_3 [] = ([], [], [])" |
  "unzip_3 ((a, b, c)#l) = (
    let (as, bs, cs) = unzip_3 l in
    (a#as, b#bs, c#cs)
  )"

fun unzip_4 :: "('a \<times> 'b \<times> 'c \<times> 'd) list \<Rightarrow> ('a list \<times> 'b list \<times> 'c list \<times> 'd list)" where
  "unzip_4 [] = ([], [], [], [])" |
  "unzip_4 ((a, b, c, d)#l) = (
    let (as, bs, cs, ds) = unzip_4 l in
    (a#as, b#bs, c#cs, d#ds)
  )"

text\<open>We want to return an aexp which, when evaluated in the correct context accounts for the literal
input-output pairs within the training set. This will be replaced by symbolic regression in the
executable\<close>
definition get_output_gp :: "label \<Rightarrow> tids \<Rightarrow> nat \<Rightarrow> value list \<Rightarrow> output_function set \<Rightarrow> (inputs \<times> registers \<times> value \<times> nat list) list \<Rightarrow> (vname aexp \<times> (vname \<Rightarrow>f String.literal)) option" where
  "get_output_gp label tids maxReg values bad train = (let
    possible_funs = {a. correct a bad values train}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs), (K$ STR ''int''))
  )"
declare get_output_gp_def [code del]
code_printing constant get_output_gp \<rightharpoonup> (Scala) "Dirties.getOutput"

definition get_output :: "label \<Rightarrow> tids \<Rightarrow> nat \<Rightarrow> value list \<Rightarrow> output_function set \<Rightarrow> (inputs \<times> registers \<times> value \<times> nat list) list \<Rightarrow> funMem \<Rightarrow> (vname aexp \<times> (vname \<Rightarrow>f String.literal)) option" where
  "get_output label tids maxReg values bad train fun_mem = (
    case find (\<lambda>(fun, _). fun \<notin> bad \<and> correct fun bad values train) (fun_mem $ label) of
      None \<Rightarrow> get_output_gp label tids maxReg values bad train |
      Some (fun, types) \<Rightarrow> Some (fun, types)
  )"

definition enumerate_exec_values :: "trace \<Rightarrow> value list" where
  "enumerate_exec_values vs = fold (\<lambda>(_, i, p) I. List.union (List.union i p) I) vs []"

definition enumerate_log_values :: "log \<Rightarrow> value list" where
  "enumerate_log_values l = fold (\<lambda>e I. List.union (enumerate_exec_values e) I) l []"

fun target_registers :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (output_function \<Rightarrow>f (vname \<Rightarrow>f String.literal)) \<Rightarrow> run_info" where
  "target_registers e s r [] types = []" |
  "target_registers e s r ((l, i, p)#es) types = (
    let
      (tids, s', t) = fthe_elem (i_possible_steps e s r l i);
      r' = evaluate_updates t i r;
      necessary_regs = fold finfun_add (map (\<lambda>(p, f). if finfun_to_list (types $ f) = [] then <> else get_regs (types $ f) i f p) (zip p (Outputs t))) <>
    in
    (s, r, necessary_regs, i, tids, t)#(target_registers e s' r' es types)
  )"

fun infer_updates :: "funMem \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> transition_group \<Rightarrow> (output_function \<Rightarrow>f (vname \<Rightarrow>f String.literal)) \<Rightarrow> iEFSM" where
  "infer_updates fun_mem e l gp types = (
    let
      values = enumerate_log_values l;
      group_ids = set (map fst gp);
      targeted = map (\<lambda>trace. rev (target <> (rev (target_registers e 0 <> trace types)))) l;
      relevant = fold List.union (map (filter (\<lambda>(t_regs, s, oldregs, necessary_regs, inputs, tids, tran). tids \<in> group_ids)) targeted ) []
    in                   
    case group_update fun_mem values relevant of
      None \<Rightarrow> e |
      Some u \<Rightarrow> (make_distinct (add_groupwise_updates l [u] e))
  )"

fun groupwise_infer_updates :: "funMem \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> transition_group list \<Rightarrow> (output_function \<Rightarrow>f (vname \<Rightarrow>f String.literal)) \<Rightarrow> iEFSM" where
  "groupwise_infer_updates fun_mem l e [] types = e" |
  "groupwise_infer_updates fun_mem l e (gp#gps) types = (
    if accepts_log (set l) (tm e) then e else groupwise_infer_updates fun_mem l (infer_updates fun_mem e l gp types) gps types
  )"

(* Waypoints *)
definition nodes :: "iEFSM \<Rightarrow> cfstate fset" where
  "nodes g = ((fimage (\<lambda>(_, (from, to), tran). from) g) |\<union>| (fimage (\<lambda>(_, (from, to), tran). to) g))"

definition "fst_not v = (\<lambda>x. v \<noteq> x) \<circ> fst"

definition out :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> cfstate fset" where
  "out g v = fimage (\<lambda>(_, (from, to), tran). to) (ffilter (\<lambda>(_, (from, to), tran). from = v) g)"

definition "transitions = fimage (\<lambda>(tids, (from, to), tran). (to, tids))"

definition outgoing_transitions :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> (cfstate \<times> tids) fset" where
  "outgoing_transitions g v = transitions (ffilter (\<lambda>(_, (from, to), tran). from = v) g)"

definition "drinks_iEFSM = fset_of_list (map (\<lambda>(x, rest). ([x], rest)) (enumerate 1 (sorted_list_of_fset drinks)))"

lemma bot_fset_eq: "x = {||} = (fset x = {})"
  by (simp add: fset_equiv)

lemma in_outgoing_transitions: "(s', tids) \<in> fset (PTA_Generalisation.outgoing_transitions g s) = (\<exists>t. (tids, (s, s'), t) |\<in>| g)"
  apply (simp add: outgoing_transitions_def transitions_def fmember_def)
  apply standard
   apply auto[1]
  by force

function allRoutes :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> tids list \<Rightarrow> tids list fset" where
  "allRoutes g v closed = (
    if v |\<notin>| (nodes g) then {||} else
    let options = ffilter (\<lambda>(s', t). t \<notin> set closed) (outgoing_transitions g v) in
    if options = {||} then {|[]|} else
    fimage (\<lambda>(s', t). [t]) options |\<union>| fUnion (fimage (\<lambda>(s', t). fimage (\<lambda>x. t#x) (allRoutes g s' (t#closed))) options)
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(g, v, closed). size (fimage fst g - fset_of_list closed)]")
   apply simp
  apply (simp)
  apply clarsimp
  apply (simp add: FSet.fmember.rep_eq fset_of_list.rep_eq)
  apply (rule Finite_Set.psubset_card_mono)
   apply simp
  apply (simp add: in_outgoing_transitions fmember_def)
  apply clarsimp
  apply (case_tac "b \<in> fst ` fset g")
   apply auto[1]
  by force

fun remove :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> iEFSM" where
  "remove g v = ffilter (\<lambda>(_, (from, to), tran). to \<noteq> v) g"

function allPaths :: "iEFSM \<Rightarrow> cfstate \<Rightarrow> cfstate list \<Rightarrow> cfstate list fset" where
  "allPaths g v closed = (
    if v \<in> set closed \<or> v |\<notin>| (nodes g) then {||} else
    if out g v = {||} then {|[v]|} else
    finsert [v] (fimage (\<lambda>x. v#x) (fUnion (fimage (\<lambda>s. allPaths g s (v#closed)) (out g v))))
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(g, v, closed). size (nodes g - fset_of_list closed)]")
   apply simp
  apply (simp del: remove.simps)
  apply clarsimp
  apply (simp add: FSet.fmember.rep_eq fset_of_list.rep_eq)
  by (metis Diff_iff card_gt_0_iff diff_Suc_less empty_iff finite_Diff finite_fset)

definition satisfies :: "cfstate list \<Rightarrow> cfstate list \<Rightarrow> bool" where
  "satisfies wps path = (
    let
      acc = \<lambda>x wp. case x of None \<Rightarrow> None | Some path' \<Rightarrow> (let new = dropWhile (\<lambda>e. wp \<noteq> e) path' in case new of [] \<Rightarrow> None | _ \<Rightarrow> Some (tl new));
      fold_result = foldl acc (Some path) wps
    in
    fold_result = Some []
  )"

(* \ Waypoints *)

type_synonym bad_funs = "tids \<Rightarrow>f output_function set"
datatype output_generalisation = Success "(iEFSM \<times> funMem \<times> output_function list \<times> bad_funs)" | Failure bad_funs

function output_and_update :: "bad_funs \<Rightarrow> output_function list \<Rightarrow> funMem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> transition_group list \<Rightarrow> transition_group \<Rightarrow>  value list \<Rightarrow> inputs list \<Rightarrow> registers list \<Rightarrow> (nat \<times> nat \<times> value list) list \<Rightarrow> nat list list \<Rightarrow> output_generalisation" where
  "output_and_update bad good fun_mem _ _ e _ _ _ _ _ _ [] _ = Success (e, fun_mem, rev good, bad)" |
  "output_and_update bad good fun_mem max_attempts attempts e log gps gp values is r ((inx, maxReg, ps)#pss) latent = (
    let (rep_id, rep) = (hd gp); label = Label rep in
    case get_output label (fst (hd gp)) maxReg values (bad $ rep_id) (zip is (zip r (zip ps latent))) fun_mem of
      None \<Rightarrow> Failure (bad(rep_id $:= (set good) \<union> (bad $ rep_id))) |
      Some (fun, types) \<Rightarrow>
        let
          e' = fimage (\<lambda>(tids, tf, t). if tids \<in> set (map fst gp) then (tids, tf, t\<lparr>Outputs:=(Outputs t)[inx := fun]\<rparr>) else (tids, tf, t)) e;
          unknown = (K$ (STR ''UNKNOWN''));
          routes = allRoutes e 0 [];
          fun_mem' = fun_mem(label $:= (fun, types)#(fun_mem $ label))
        in
        if accepts_log (set log) (tm e') then
          output_and_update bad (fun#good) fun_mem' max_attempts attempts e' log gps gp values is r pss latent
        else
          let
            group_ids = \<lambda>g. set (map fst g);
            gp_ids = (group_ids gp);
            \<comment>\<open>It only makes sense to try and infer updates for groups with ids before the group we've inferred updates for
               otherwise, the updates aren't executed before the registers are evaluated.\<close>
            possible_gps = filter (\<lambda>g. \<exists>r |\<in>| routes. \<exists>id \<in> (group_ids g). \<exists>id' \<in> (gp_ids). id \<in> set r \<and> id' \<in> set r) gps;
            e'' = groupwise_infer_updates fun_mem log e' possible_gps ((K$ unknown)(fun$:=types))
          in
          if accepts_log (set log) (tm e'') then
            output_and_update bad (fun#good) fun_mem' max_attempts attempts e'' log gps gp values is r pss latent
          else
          if attempts > 0 then
            output_and_update (bad(rep_id $:= insert fun (bad $ rep_id))) good fun_mem max_attempts (attempts - 1) e log gps gp values is r ((inx, maxReg, ps)#pss) latent
          else
            Failure (bad(rep_id $:= (set good) \<union> (bad $ rep_id)))
  )"
     apply (clarsimp, meson unzip_3.cases)
  by auto
termination
  by (relation "measures [\<lambda>(bad, good, fun_mem, max_attempts, attempts, e, log, gps, gp, values, I, r, l, latent). length l + attempts]", auto)

(*This is where the types stuff originates*)
definition generalise_and_update :: "nat \<Rightarrow> nat \<Rightarrow> bad_funs \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> transition_group \<Rightarrow> transition_group list \<Rightarrow> funMem \<Rightarrow>  output_generalisation" where
  "generalise_and_update level attempts bad log e gp gps fun_mem = (
    let
      values = enumerate_log_values log;
      new_gp_ts = make_training_set e log gp;
      (I, R, P, L) = unzip_4 new_gp_ts;
      max_reg = max_reg_total e;
      \<comment>\<open> TODO: We want to record output funs and types as we infer them! \<close>
      outputs_to_infer = enumerate 0 (enumerate max_reg (transpose P))
      in output_and_update bad [] fun_mem attempts attempts e log gps gp values I R outputs_to_infer L
  )"

datatype generalisation = Failed bad_funs | Succeeded "(iEFSM \<times> tids list \<times> funMem \<times> (transition \<times> output_types option list) list)"

fun take_maximum_updates :: "iEFSM \<Rightarrow> (tids \<times> transition) fset" where
  "take_maximum_updates ts = fold (\<lambda>(tids, _, t) acc.
    if \<exists>(_, h) |\<in>| acc. Label t = Label h \<and> Arity t = Arity h \<and> Outputs t = Outputs h \<and> set (Updates t) \<subset> set (Updates h) then
      acc
    else
      finsert (tids, t) acc) (sorted_list_of_fset ts) {||}"

definition bad_union :: "bad_funs \<Rightarrow> bad_funs \<Rightarrow> bad_funs" where
  "bad_union bad bad' = fold (\<lambda>k acc. acc(k $:= (acc $ k) \<union> (bad' $ k))) (finfun_to_list bad') bad"

definition bad_add :: "bad_funs \<Rightarrow> tids \<Rightarrow> output_function set \<Rightarrow> bad_funs" where
  "bad_add bad k v = bad(k $:= (bad $ k \<union> v))"

fun groupwise_generalise_and_update :: "bad_funs \<Rightarrow> bad_funs \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> transition_group list \<Rightarrow> transition_group list \<Rightarrow> (tids \<Rightarrow> abstract_event) \<Rightarrow> (abstract_event \<Rightarrow>f (output_function list \<times> update_function list) option) \<Rightarrow> tids list \<Rightarrow> (transition \<times> output_types option list) list \<Rightarrow> funMem \<Rightarrow> generalisation" where
  "groupwise_generalise_and_update bad maybe_bad max_attempts attempts _ e [] update_groups structure funs to_derestrict closed fun_mem = Succeeded (e, to_derestrict, fun_mem, closed)" |
  "groupwise_generalise_and_update bad maybe_bad max_attempts attempts log e (gp#t) update_groups structure funs to_derestrict closed fun_mem_old = (
        case generalise_and_update attempts max_attempts bad log e gp update_groups fun_mem_old of
        Failure bad' \<Rightarrow> Failed (bad_union bad bad') |
        Success (e', fun_mem, output_funs, bad') \<Rightarrow>
        let
          reg_bad = set (filter (\<lambda>a. AExp.enumerate_regs a \<noteq> {}) output_funs);
          (rep_id, rep) = (hd (gp));
          different = ffilter (\<lambda>(id, tf, t). t \<noteq> get_by_ids e id) e';
          funs = fold (\<lambda>(id, t) acc. acc(structure id $:= Some ((Outputs t), (Updates t)))) (sorted_list_of_fset (take_maximum_updates different)) funs;
          structural_group = fimage (\<lambda>(i, _, t). (i, t)) (ffilter (\<lambda>(i, _, _). structure i = structure rep_id) e');
          new_outputs = \<lambda>tid t. case funs $ (structure tid) of None \<Rightarrow> Outputs t | Some (outputs, updates) \<Rightarrow> outputs;
          new_updates = \<lambda>tid t. case funs $ (structure tid) of None \<Rightarrow> Updates t | Some (outputs, updates) \<Rightarrow> updates;
          pre_standardised = fimage (\<lambda>(tida, tfa, tra). (tida, tfa, tra\<lparr>Outputs := new_outputs tida tra, Updates := new_updates tida tra\<rparr>)) e';
          pre_standardised_good =  accepts_log (set log) (tm pre_standardised);
          standardised = if pre_standardised_good then pre_standardised else e';
          \<comment> \<open>This tackles transitions which have been changed\<close>
          more_to_derestrict = sorted_list_of_fset (fimage fst (ffilter (\<lambda>(id, _, tran). tran \<noteq> get_by_ids e id) standardised));
        \<comment> \<open>If we manage to standardise a structural group, we do not need to evolve outputs and
            updates for the other historical subgroups so can filter them out.\<close>
        
        result = (if pre_standardised_good then
          groupwise_generalise_and_update bad (bad_add (bad_union maybe_bad bad') (rep_id) reg_bad) max_attempts attempts log (merge_regs standardised (accepts_log (set log))) (filter (\<lambda>g. structure (fst (hd g)) \<notin> set (finfun_to_list funs)) t) update_groups structure funs (to_derestrict @ more_to_derestrict) [] fun_mem
        else
          groupwise_generalise_and_update bad (bad_add (bad_union maybe_bad bad') (rep_id) reg_bad) max_attempts attempts log (merge_regs standardised (accepts_log (set log))) t update_groups structure funs (to_derestrict @ more_to_derestrict) [] fun_mem)
        in
        case result of
          Failed bad \<Rightarrow>  (
          if attempts > 0 then
            groupwise_generalise_and_update (bad_add (bad_union maybe_bad bad) (rep_id) reg_bad) (K$ {}) max_attempts (attempts - 1) log e (gp#t) update_groups structure funs to_derestrict closed fun_mem_old
          else
            groupwise_generalise_and_update (bad_add bad rep_id reg_bad) (K$ {}) max_attempts max_attempts log e t update_groups structure funs to_derestrict closed fun_mem
        ) |
        Succeeded res \<Rightarrow> Succeeded res
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

definition get_structures :: "iEFSM \<Rightarrow> log \<Rightarrow> (tids \<Rightarrow> abstract_event)" where
  "get_structures e log = (
    let
      observed = fold (@) (map (\<lambda>t. events_transitions e 0 <> t []) log) []
    in
      fold (\<lambda>(tids, abs) acc. \<lambda>tt. if set tt \<subseteq> set tids \<or> set tids \<subseteq> set tt then abs else acc tt) observed (\<lambda>x. (STR ''UNKNOWN'', [], []))
  )"

definition this :: "generalisation \<Rightarrow> (iEFSM \<times> tids list \<times> funMem \<times> (transition \<times> output_types option list) list)" where
  "this x = (case x of Succeeded y \<Rightarrow> y)"

definition derestrict :: "iEFSM \<Rightarrow> log \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "derestrict pta log m np = (
    let
      groups = historical_groups pta log;
      output_groups = filter (\<lambda>g. (Outputs (snd (hd g))) \<noteq> []) groups;
      (normalised, to_derestrict, _, _) = this (groupwise_generalise_and_update (K${}) (K${}) 2 2 log pta output_groups groups (get_structures pta log) (K$ None) [] [] (K$ []));
      tidied = fimage (\<lambda>(id, tf, t). (id, tf, t\<lparr>Updates:= tidy_updates (Updates t)\<rparr>)) normalised
    in
      drop_selected_guards tidied to_derestrict pta log m np
  )"

definition "drop_pta_guards pta log m np = drop_all_guards pta pta log m np"

end
