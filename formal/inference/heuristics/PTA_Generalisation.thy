theory PTA_Generalisation
  imports "../Inference"
begin

hide_const I

\<comment> \<open>Cannot be converted to fold due to early termination in the "true" case of the "if"\<close>
primrec insert_into_group :: "(tids \<times> transition) list list \<Rightarrow> (tids \<times> transition) \<Rightarrow> (tids \<times> transition) list list" where
  "insert_into_group [] pair = [[pair]]" |
  "insert_into_group (h#t) pair = (
    if \<forall>(_, t) \<in> set h. same_structure (snd pair) t then
      ((List.insert pair h))#t
    else
      h#(insert_into_group t pair)
    )"

definition group_by_structure :: "iEFSM \<Rightarrow> (tids \<times> transition) list list" where
  "group_by_structure e = fold (\<lambda>(tid, _, transition) acc. insert_into_group acc (tid, transition)) (sorted_list_of_fset e) []"

fun same_structure_opt :: "transition option \<Rightarrow> transition option \<Rightarrow> bool" where
  "same_structure_opt None None = True" |
  "same_structure_opt (Some t) (Some t') = same_structure t t'" |
  "same_structure_opt _ _ = False"

type_synonym transition_group = "transition option \<times> nat \<times> ((tids \<times> transition) list)"

\<comment> \<open>Cannot be converted to fold due to early termination in the "true" case of the "if"\<close>
fun assign_group :: "transition_group list \<Rightarrow> (transition option \<Rightarrow> nat) \<Rightarrow> transition option \<Rightarrow> tids \<times> transition \<Rightarrow> transition_group list" where
  "assign_group [] count prev (tid, t) = [(prev, count prev, [(tid, t)])]" |
  "assign_group ((prev', c, gp)#t) count prev (tid, tr) = (
    if same_structure_opt prev prev' \<and> (\<forall>(_, tr') \<in> set gp. same_structure tr tr') \<and> count prev = c then
      (prev', c, List.insert (tid, tr) gp)#t
    else
      (prev', c, gp)#assign_group t count prev (tid, tr)
  )"

fun trace_group_transitions :: "(transition option \<Rightarrow> nat) \<Rightarrow> iEFSM \<Rightarrow> execution \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> transition option \<Rightarrow> transition option \<Rightarrow> transition_group list \<Rightarrow> transition_group list" where
  "trace_group_transitions _ _ [] _ _ _ _ g = g" |
  "trace_group_transitions count e ((l, i, _)#trace) s r prevGroup currentGroup g = (
    let
      (id, s', t) = fthe_elem (i_possible_steps e s r l i);
      r' = apply_updates (Updates t) (join_ir i r) r;
      newCount = (\<lambda>x. if x = Some t then Suc (count x) else count x)
    in
    if (same_structure_opt (Some t) currentGroup) then
      trace_group_transitions newCount e trace s' r' prevGroup currentGroup (assign_group g count prevGroup (id, t))
    else
      trace_group_transitions newCount e trace s' r' currentGroup (Some t) (assign_group g count currentGroup (id, t))
  )"

definition log_group_transitions :: "iEFSM \<Rightarrow> log \<Rightarrow> transition_group list" where
  "log_group_transitions e l = fold (\<lambda>t acc. trace_group_transitions (\<lambda>x. 0) e t 0 <> None None acc) l []"

definition transition_groups :: "iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list list" where
  "transition_groups e l = (
    let
      group_dict = log_group_transitions e l
    in
      map (snd \<circ> snd) group_dict
  )"

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

definition log_training_set :: "iEFSM \<Rightarrow> log \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list" where
  "log_training_set e l ts = fold (\<lambda>h a. trace_training_set e h 0 <> a) l ts"

(* This will generate the training sets in the same order that the PTA was built, i.e. traces     *)
(* that appear earlier in the logs will appear earlier in the list of training sets. This allows  *)
(* us to infer register updates according to trace precidence so  we won't get redundant updates  *)
(* on later transitions which spoil the data state                                                *)
definition make_training_set :: "iEFSM \<Rightarrow> log \<Rightarrow> (((tids \<times> transition) list) \<times> (registers \<times> value list \<times> value list) list) list" where
  "make_training_set e l = log_training_set e l (map (\<lambda>x. (x, [])) (transition_groups e l))"

\<comment> \<open>This will be replaced by symbolic regression in the executable\<close>
definition get_output :: "nat \<Rightarrow> value list \<Rightarrow> inputs list \<Rightarrow> registers list \<Rightarrow> value list \<Rightarrow> (vname aexp \<times> (vname \<Rightarrow>f String.literal)) option" where
  "get_output maxReg values I r P = (let
    possible_funs = {a. \<forall>(i, r, p) \<in> set (zip I (zip r P)). aval a (join_ir i r) = Some p}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs), (K$ STR ''int''))
  )"
declare get_output_def [code del]
code_printing constant get_output \<rightharpoonup> (Scala) "Dirties.getOutput"

definition get_outputs :: "nat \<Rightarrow> value list \<Rightarrow> inputs list \<Rightarrow> registers list \<Rightarrow> value list list \<Rightarrow> (vname aexp \<times> (vname \<Rightarrow>f String.literal)) option list" where
  "get_outputs maxReg values I r outputs = map (\<lambda>ps. get_output maxReg values I r ps) (transpose outputs)" 

fun put_outputs :: "(((vname aexp \<times> (vname \<Rightarrow>f String.literal)) option) \<times> vname aexp) list \<Rightarrow> vname aexp list" where
  "put_outputs [] = []" |
  "put_outputs ((None, p)#t) = p#(put_outputs t)" |
  "put_outputs ((Some (p, _), _)#t) = p#(put_outputs t)"

lemma put_outputs_fold [code]: "put_outputs xs = foldr (\<lambda>x acc. case x of (None, p) \<Rightarrow> p#acc | (Some (p, _), _) \<Rightarrow> p#acc) xs []"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    apply (cases a)
    apply (case_tac aa)
    by auto
qed

type_synonym output_types = "(nat \<times> (vname aexp \<times> vname \<Rightarrow>f String.literal) option) list"

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
  "replace_groups (h#t) e = replace_groups t (fold (\<lambda>(id, t) acc. replace_transition acc id t) h e)"

lemma replace_groups_fold [code]: "replace_groups xs e = fold (\<lambda>h acc'. (fold (\<lambda>(id, t) acc. replace_transition acc id t) h acc')) xs e"
  by (induct xs arbitrary: e,  auto)

definition pta_generalise_outputs :: "log \<Rightarrow> (iEFSM \<times> ((tids \<times> transition \<times> output_types) list list))" where
  "pta_generalise_outputs log = (
    let
      values = enumerate_log_values log;
      pta = make_pta log;
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

definition get_updates :: "(tids \<times> update_function list) list \<Rightarrow> tids \<Rightarrow> update_function list" where
  "get_updates u t = List.maps snd (filter (\<lambda>(tids, _). set t \<subseteq> set tids) u)"

definition get_ids :: "(tids \<times> update_function list) list \<Rightarrow> tids \<Rightarrow> tids" where
  "get_ids u t = List.maps fst (filter (\<lambda>(tids, _). set t \<subseteq> set tids) u)"

fun add_groupwise_updates_trace :: "execution  \<Rightarrow> (tids \<times> update_function list) list \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> iEFSM" where
  "add_groupwise_updates_trace [] _ e _ _ = e" |
  "add_groupwise_updates_trace ((l, i, _)#trace) funs e s r = (
    let
      (id, s', t) = fthe_elem (i_possible_steps e s r l i);
      updated = apply_updates (Updates t) (join_ir i r) r;
      newUpdates = get_updates funs id;
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

lemma fold_add_groupwise_updates [code]: "add_groupwise_updates log funs e = fold (\<lambda>trace acc. add_groupwise_updates_trace trace funs acc 0 <>) log e"
  by (induct log arbitrary: e, auto)

\<comment> \<open>This will be replaced to calls to Z3 in the executable\<close>
definition get_regs :: "(vname \<Rightarrow>f String.literal) \<Rightarrow> inputs \<Rightarrow> vname aexp \<Rightarrow> value \<Rightarrow> registers" where
  "get_regs types inputs expression output = Eps (\<lambda>r. aval expression (join_ir inputs r) = Some output)"

type_synonym event_info = "(cfstate \<times> registers \<times> registers \<times> inputs \<times> tids \<times> transition)"
type_synonym run_info = "event_info list"
type_synonym targeted_run_info = "(registers \<times> event_info) list"

fun everything_walk :: "output_function \<Rightarrow> nat \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> execution \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> tids list \<Rightarrow> run_info" where
  "everything_walk _ _ _ [] _ _ _ _ = []" |
  "everything_walk f fi types ((label, inputs, outputs)#t) oPTA s regs gp  = (
    let (tid, s', ta) = fthe_elem (i_possible_steps oPTA s regs label inputs) in
     \<comment> \<open>Possible steps with a transition we need to modify\<close>
    if tid \<in> set gp then
      (s, regs, get_regs types inputs f (outputs!fi), inputs, tid, ta)#(everything_walk f fi types t oPTA s' (apply_updates (Updates ta) (join_ir inputs regs) regs) gp)
    else
      let empty = <> in
      (s, regs, empty, inputs, tid, ta)#(everything_walk f fi types t oPTA s' (apply_updates (Updates ta) (join_ir inputs regs) regs) gp)
  )"

definition everything_walk_log :: "output_function \<Rightarrow> nat \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> tids list \<Rightarrow> run_info list" where
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
  case Nil
  then show ?case
    by simp
next
  case (Cons a ts)
  then show ?case
    apply (cases a)
    apply simp
    apply standard
    by (metis (no_types, lifting) append_eq_append_conv2 rev.simps(2) rev_append rev_swap self_append_conv2)+
qed

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
definition get_update :: "nat \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> vname aexp option" where
  "get_update reg values train = (let
    possible_funs = {a. \<forall>(i, r, r') \<in> set train. aval a (join_ir i r) = r' $ reg}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs))
  )"

definition get_updates_opt :: "value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> (nat \<times> vname aexp option) list" where
  "get_updates_opt values train = (let
    updated_regs = fold List.union (map (finfun_to_list \<circ> snd \<circ> snd) train) [] in
    map (\<lambda>r.
      let targetValues = remdups (map (\<lambda>(_, _, regs). regs $ r) train) in
      \<comment> \<open>add inputs=[] to this too but only when we've got non-numericals working\<close>
      if  (\<forall>(_, anteriorRegs, posteriorRegs) \<in> set train. anteriorRegs $ r = posteriorRegs $ r) then
        (r, Some (V (R r)))
      else if length targetValues = 1 \<and> (\<forall>(inputs, initialRegs, _) \<in> set train. finfun_to_list initialRegs = []) then
        case hd targetValues of Some v \<Rightarrow>
        (r, Some (L v))
      else
        (r, get_update r values train)
    ) updated_regs
  )"

definition finfun_add :: "(('a::linorder) \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b) \<Rightarrow> ('a \<Rightarrow>f 'b)" where
  "finfun_add a b = fold (\<lambda>k f. f(k $:= b $ k)) (finfun_to_list b) a"

definition group_update :: "value list \<Rightarrow> targeted_run_info \<Rightarrow> (tids \<times> (nat \<times> vname aexp) list) option" where
  "group_update values l = (
    let
      targeted = filter (\<lambda>(regs, _). finfun_to_list regs \<noteq> []) l;
      maybe_updates = get_updates_opt values (map (\<lambda>(tRegs, s, oldRegs, regs, inputs, tid, ta). (inputs, finfun_add oldRegs regs, tRegs)) targeted)
    in
    if \<exists>(_, f_opt) \<in> set maybe_updates. f_opt = None then
      None
    else
      Some (fold List.union (map (\<lambda>(tRegs, s, oldRegs, regs, inputs, tid, ta). tid) l) [], map (\<lambda>(r, f_o). (r, the f_o)) maybe_updates)
  )"

fun groupwise_put_updates :: "(tids \<times> transition) list list \<Rightarrow> log \<Rightarrow> value list \<Rightarrow> tids list \<Rightarrow> (nat \<times> (vname aexp \<times> vname \<Rightarrow>f String.literal)) \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "groupwise_put_updates [] _ _ _ _  e = e" |
  "groupwise_put_updates (gp#gps) log values current (o_inx, (op, types)) e = (
    let
      walked = everything_walk_log op o_inx types log e current;
      targeted = map (\<lambda>x. filter (\<lambda>(_, _, _, _, _, id, tran). (id, tran) \<in> set gp) x) (map (\<lambda>w. rev (target <> (rev w))) walked);
      group = fold List.union targeted []
    in
    case group_update values group of
      None \<Rightarrow> groupwise_put_updates gps log values current (o_inx, (op, types)) e |
      Some u \<Rightarrow> groupwise_put_updates gps log values current (o_inx, (op, types)) (make_distinct (add_groupwise_updates log [u] e))
  )"

fun put_updates :: "log \<Rightarrow> value list \<Rightarrow> tids list \<Rightarrow> output_types \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_updates _ _ _ [] e = Some e" |
  "put_updates _ _ _ ((_, None)#_) _ = None" |
  "put_updates log values current ((o_inx, Some (op, types))#ops) e = (
    if enumerate_aexp_regs op = {} then
      if satisfies (set log) (tm e) then
        Some e
      else
        None
    else
      let
        groups = transition_groups e log;
        updated = groupwise_put_updates groups log values current (o_inx, (op, types)) e
      in
        put_updates log values current ops updated
  )"

(*This is where the types stuff originates*)
definition generalise_and_update :: "log \<Rightarrow> iEFSM \<Rightarrow> (tids \<times> transition) list \<times> (registers \<times> value list \<times> value list) list \<Rightarrow> iEFSM option" where
  "generalise_and_update log e gp = (
    let
      values = enumerate_log_values log;
      I = map (\<lambda>(regs, ins, outs).ins) (snd gp);
      R = map (\<lambda>(regs, ins, outs).regs) (snd gp);
      P = map (\<lambda>(regs, ins, outs).outs) (snd gp);
      max_reg = max_reg_total e;
      outputs = get_outputs max_reg values I R P;
      changes = map (\<lambda>(id, tran). (id, tran\<lparr>Outputs := put_outputs (zip outputs (Outputs tran))\<rparr>)) (fst gp);
      generalised_model = fold (\<lambda>(id, t) acc. replace_transition acc id t) changes e
  in
  case put_updates log values (map fst (fst gp)) (enumerate 0 outputs) generalised_model of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> if satisfies (set log) (tm e') then Some e' else None
  )"

primrec groupwise_generalise_and_update :: "log \<Rightarrow> iEFSM \<Rightarrow> ((tids \<times> transition) list \<times> (registers \<times> value list \<times> value list) list) list \<Rightarrow> iEFSM" where
  "groupwise_generalise_and_update _ e [] = e" |
  "groupwise_generalise_and_update log e (gp#t) = (
    case generalise_and_update log e gp of
      None \<Rightarrow> groupwise_generalise_and_update log e t |
      Some e' \<Rightarrow> groupwise_generalise_and_update log e' t
  )"

lemma groupwise_generalise_and_update_fold [code]: 
"groupwise_generalise_and_update log e gs = fold (\<lambda>gp e.
  case generalise_and_update log e gp of
        None \<Rightarrow> e |
        Some e' \<Rightarrow> e'
  ) gs e"
  apply(induct gs arbitrary: e)
  apply simp
  by (case_tac "generalise_and_update log e a", auto)

definition standardise_outputs :: "vname aexp list \<Rightarrow> vname aexp list \<Rightarrow> vname aexp list" where
  "standardise_outputs p1 p2 = map (\<lambda>(p1, p2). max p1 p2) (zip p1 p2)"

definition standardise_group_outputs :: "(tids \<times> transition) list \<Rightarrow> (tids \<times> transition) list" where
  "standardise_group_outputs g = (
    let
      outputs = case g of 
        [] \<Rightarrow> [] |
        (h#t) \<Rightarrow> fold (\<lambda>x acc. standardise_outputs x acc) (map (Outputs \<circ> snd) t) (Outputs (snd h))
    in
      map (\<lambda>(id, t). (id, t\<lparr>Outputs := outputs\<rparr>)) g
  )"

definition standardise_group_updates :: "(tids \<times> transition) list \<Rightarrow> (tids \<times> transition) list" where
  "standardise_group_updates g = (
    let
      updates = remdups (List.maps (Updates \<circ> snd) g)
    in
      map (\<lambda>(id, t). (id, t\<lparr>Updates := updates\<rparr>)) g
  )"

(* Sometimes inserting updates without redundancy can cause certain transitions to not get a      *)
(* particular update function. This can lead to disparate groups of transitions which we want to  *)
(* standardise such that every group of transitions has the same update function                  *)
primrec standardise_groups_aux :: "iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list list \<Rightarrow> ((tids \<times> transition) list \<Rightarrow> (tids \<times> transition) list) \<Rightarrow> iEFSM" where
  "standardise_groups_aux e _ [] _ = e" |
  "standardise_groups_aux e l (h#t) s = (
    let
      standardised = s h;
      e' = replace_transitions e standardised
    in
      if satisfies (set l) (tm e') then
        standardise_groups_aux e' l t s
      else
        standardise_groups_aux e l t s
  )"

lemma standardise_groups_aux_fold [code]: "standardise_groups_aux e l xs s = fold (\<lambda>h acc. 
  let
      e' = replace_transitions acc (s h)
    in
      if satisfies (set l) (tm e') then
        e'
      else
        acc
  ) xs e"
proof(induct xs arbitrary: e s l)
case Nil
  then show ?case
    by simp
next
case (Cons a xs)
  then show ?case
    by (simp add: Let_def)
qed

definition standardise_groups :: "iEFSM \<Rightarrow> log \<Rightarrow> iEFSM" where
  "standardise_groups e l = standardise_groups_aux e l (group_by_structure e) (standardise_group_outputs \<circ> standardise_group_updates)"

definition standardise_groups_updates :: "iEFSM \<Rightarrow> log \<Rightarrow> iEFSM" where
  "standardise_groups_updates e l = standardise_groups_aux e l (group_by_structure e) (standardise_group_updates)"

(* Instead of doing all the outputs and all the updates, do it one output and update at a time    *)
(* This way if one update fails, we don't end up losing the rest by having to default back to the *)
(* original PTA if the normalised one doesn't reproduce the original behaviour                    *)
definition incremental_normalised_pta :: "log \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "incremental_normalised_pta log pta = (
    let
      values = enumerate_log_values log;
      training_set = make_training_set pta log
    in
    standardise_groups (groupwise_generalise_and_update log pta training_set) log
  )"                 

\<comment> \<open>Need to derestrict variables which occur in the updates but keep unrelated ones to avoid \<close>
\<comment> \<open>nondeterminism creeping in too early in the inference process                            \<close>
definition derestrict_transition :: "transition \<Rightarrow> transition" where
  "derestrict_transition t = (
    let relevant_vars = image V (fold (\<lambda>(r, u) acc. acc \<union> (AExp.enumerate_vars u)) (Updates t) {}) in
    t\<lparr>Guard := filter (\<lambda>g. \<forall>v \<in> relevant_vars. \<not> gexp_constrains g v) (Guard t)\<rparr>
  )"

fun find_initialisation_of_trace :: "nat \<Rightarrow> execution \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> (tids \<times> transition) option" where
  "find_initialisation_of_trace _ [] _ _ _ = None" |
  "find_initialisation_of_trace r' ((l, i, _)#es) e s r = (
    let
      (tids, s', t) = fthe_elem (i_possible_steps e s r l i)
    in
    if (\<exists>(rr, u) \<in> set (Updates t). rr = r' \<and> is_lit u) then
      Some (tids, t)
    else
      find_initialisation_of_trace r' es e s' (apply_updates (Updates t) (join_ir i r) r)
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
        \<comment> \<open>Add the initialisation update to incumbant transitions\<close>
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
      if satisfies (set l) (tm e') then
        e'
      else
        e
  ) (find_initialisation_of r e l) e"

fun find_first_use_of_trace :: "nat \<Rightarrow> execution \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> tids option" where
  "find_first_use_of_trace _ [] _ _ _ = None" |
  "find_first_use_of_trace rr ((l, i, _)#es) e s r = (
    let
      (id, s', t) = fthe_elem (i_possible_steps e s r l i)
    in
      if (\<exists>p \<in> set (Outputs t). aexp_constrains p (V (R rr))) then
        Some id
      else
        find_first_use_of_trace rr es e s' (apply_updates (Updates t) (join_ir i r) r)
  )"

definition find_first_uses_of :: "nat \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> tids list" where
  "find_first_uses_of r l e = List.maps (\<lambda>x. case x of None \<Rightarrow> [] | Some x \<Rightarrow> [x]) (map (\<lambda>t. find_first_use_of_trace r t e 0 <>) l)"

definition derestrict :: "log \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "derestrict log m np = (
    let
      pta = make_pta log;
      normalised = incremental_normalised_pta log pta;
      delayed = fold (\<lambda>r acc. delay_initialisation_of r log acc (find_first_uses_of r log acc)) (sorted_list_of_set (all_regs normalised)) normalised;
      derestricted = fimage (\<lambda>(id, tf, tran). (id, tf, tran\<lparr>Guard := []\<rparr>)) delayed;
      nondeterministic_pairs = sorted_list_of_fset (np derestricted)
    in
    case resolve_nondeterminism [] nondeterministic_pairs pta derestricted m (satisfies (set log)) np of
      None \<Rightarrow> pta |
      Some resolved \<Rightarrow> resolved
  )"

end