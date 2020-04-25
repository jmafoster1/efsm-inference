theory PTA_Generalisation
  imports "../Inference" Same_Register
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

fun group_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "group_by _ [] = []" |
  "group_by f (h#t) = (
    let groups = group_by f t in
    case groups of
      [] \<Rightarrow> [[h]] |
      (g#gs) \<Rightarrow> (
        case g of
          [] \<Rightarrow> [h]#gs |
          (x#xs) \<Rightarrow> if f h x then (h#g)#gs else [h]#g#gs
      )
  )"

lemma no_empty_groups:
"\<forall>x \<in> set (group_by f xs). x \<noteq> []"
proof(induct xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  then show ?case
    apply simp
    apply (cases "group_by f xs")
     apply simp
    by (case_tac aa, auto)
qed

definition "make_transition label inputs outputs = \<lparr>Label=label, Arity=length inputs, Guards=(make_guard inputs 0), Outputs=(make_outputs outputs), Updates=[]\<rparr>"

fun observe_all :: "iEFSM \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> (cfstate \<times> cfstate \<times> tids \<times> transition) list" where
  "observe_all _ _ _ [] = []" |
  "observe_all e s r ((l, i)#es)  =
    (case random_member (i_possible_steps e s r l i)  of
      (Some (ids, s', t)) \<Rightarrow> (((s, s', ids, t)#(observe_all e s' (apply_updates (Updates t) (join_ir i r) r) es))) |
      _ \<Rightarrow> []
    )"

definition transition_groups_exec :: "iEFSM \<Rightarrow> execution \<Rightarrow> (cfstate \<times> cfstate \<times> tids \<times> transition) list list" where
  "transition_groups_exec e t = (
    let
      walked = observe_all e 0 <> (map (\<lambda>(x, y, _). (x, y)) t)
    in
    group_by (\<lambda>(_, _, _, t1) (_, _, _, t2). same_structure t1 t2) walked
  )"

type_synonym struct = "(label \<times> arity \<times> arity)"

fun tag :: "struct option \<Rightarrow> (cfstate \<times> cfstate \<times> tids \<times> transition) list list \<Rightarrow> (struct option \<times> struct \<times> (cfstate \<times> cfstate \<times> tids \<times> transition) list) list" where
  "tag _ [] = []" |
  "tag t (g#gs) = (
    let
      (_, _, _, head) = hd g;
      struct = (Label head, Arity head, length (Outputs head))
    in
    (t, struct, g)#(tag (Some struct) gs)
  )"

definition min_s :: "(struct option \<times> struct \<times> (cfstate \<times> cfstate \<times> tids \<times> transition) list) \<Rightarrow> (struct option \<times> cfstate \<times> struct \<times> (cfstate \<times> cfstate \<times> tids \<times> transition) list)" where
  "min_s g = (
    let
      (tag, struct, group) = g;
      states = map fst group;
      min = Min (set states)
    in
    (tag, min, struct, group)
  )"

definition "strip_ss = map (\<lambda>(_, _, id, t). (id, t))"

definition transition_groups :: "iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list list" where
  "transition_groups e l = (
    let
      trace_groups = map (transition_groups_exec e) l;
      tagged = map (tag None) trace_groups;
      flat =  sort (fold (@) tagged []);
      minned = sort (map min_s flat);
      pairwise_groups = group_by (\<lambda>(t1, m1, s1, g1) (t2, m2, s2, g2). t1 = t2 \<and> s1 = s2) minned;
      group_minned = map (\<lambda>g. (fst (snd (hd g)), map (\<lambda>(t1, m1, s1, g1). (t1, s1, strip_ss g1)) g)) pairwise_groups;
      stripped = map snd (sort group_minned)
    in
    map (\<lambda>l. fold (@) (map ((\<lambda>(l1, s1, g1). g1)) l) []) stripped
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
    let (id, s', transition) = fthe_elem (ffilter (\<lambda>(_, _, t). apply_outputs (Outputs t) (join_ir inputs r) = map Some outputs) (i_possible_steps e s r label inputs)) in
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

lemma put_outputs_fold [code]:
"put_outputs xs = foldr (\<lambda>x acc. case x of (None, p) \<Rightarrow> p#acc | (Some (p, _), _) \<Rightarrow> p#acc) xs []"
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

definition replace_transition :: "iEFSM \<Rightarrow> tids \<Rightarrow> transition \<Rightarrow> iEFSM" where
  "replace_transition e uid new = (fimage (\<lambda>(uids, (from, to), t). if set uid \<subseteq> set uids then (uids, (from, to), new) else (uids, (from, to), t)) e)"

primrec replace_groups :: "(tids \<times> transition) list list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "replace_groups [] e = e" |
  "replace_groups (h#t) e = replace_groups t (fold (\<lambda>(id, t) acc. replace_transition acc id t) h e)"

lemma replace_groups_fold [code]:
"replace_groups xs e = fold (\<lambda>h acc'. (fold (\<lambda>(id, t) acc. replace_transition acc id t) h acc')) xs e"
  by (induct xs arbitrary: e,  auto)

definition insert_updates :: "transition \<Rightarrow> update_function list \<Rightarrow> transition" where
  "insert_updates t u = (
    let
      \<comment> \<open>Want to filter out null updates of the form rn := rn. It doesn't affect anything but it  \<close>
      \<comment> \<open>does make things look cleaner                                                            \<close>
      necessary_updates = filter (\<lambda>(r, u). u \<noteq> V (R r)) u
    in
    t\<lparr>Updates := (filter (\<lambda>(r, _). r \<notin> set (map fst u)) (Updates t))@necessary_updates\<rparr>
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

lemma fold_add_groupwise_updates [code]:
"add_groupwise_updates log funs e = fold (\<lambda>trace acc. add_groupwise_updates_trace trace funs acc 0 <>) log e"
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

lemma target_tail:
"(rev bs)@(target tRegs ts) = target_tail tRegs ts bs"
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

lemma target_tail_fold:
"target_tail tRegs ts b = target_fold tRegs ts b"
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

lemma target_fold [code]:
"target tRegs ts = target_fold tRegs ts []"
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
      if  (\<forall>(_, anteriorRegs, posteriorRegs) \<in> set train. anteriorRegs $ r = posteriorRegs $ r) then
        (r, Some (V (R r)))
      else if length targetValues = 1 \<and> (\<forall>(inputs, anteriorRegs, _) \<in> set train. finfun_to_list anteriorRegs = []) then
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

fun groupwise_put_updates :: "(tids \<times> transition) list list \<Rightarrow> log \<Rightarrow> value list \<Rightarrow> run_info list \<Rightarrow> (nat \<times> (vname aexp \<times> vname \<Rightarrow>f String.literal)) \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
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

fun put_updates :: "log \<Rightarrow> value list \<Rightarrow> tids list \<Rightarrow> output_types \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_updates _ _ _ [] e = Some e" |
  "put_updates _ _ _ ((_, None)#_) _ = None" |
  "put_updates log values current ((o_inx, Some (op, types))#ops) e = (
    if AExp.enumerate_regs op = {} then Some e
    else
      let
        walked = everything_walk_log op o_inx types log e current;
        groups = transition_groups e log;
        updated = groupwise_put_updates groups log values walked (o_inx, (op, types)) e
      in
        put_updates log values current ops updated
  )"

(*This is where the types stuff originates*)
definition generalise_and_update :: "log \<Rightarrow> iEFSM \<Rightarrow> (tids \<times> transition) list \<Rightarrow> (registers \<times> value list \<times> value list) list \<Rightarrow> iEFSM option" where
  "generalise_and_update log e gp tr = (
    let
      label = Label (snd (hd gp));
      values = enumerate_log_values_by_label label log;
      I = map (\<lambda>(regs, ins, outs).ins) tr;
      R = map (\<lambda>(regs, ins, outs).regs) tr;
      P = map (\<lambda>(regs, ins, outs).outs) tr;
      max_reg = max_reg_total e;
      outputs = get_outputs max_reg values I R P;
      changes = map (\<lambda>(id, tran). (id, tran\<lparr>Outputs := put_outputs (zip outputs (Outputs tran))\<rparr>)) gp;
      generalised_model = fold (\<lambda>(id, t) acc. replace_transition acc id t) changes e
  in
  case put_updates log values (map fst gp) (enumerate 0 outputs) generalised_model of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> if satisfies (set log) (tm e') then Some e' else None
  )"

primrec groupwise_generalise_and_update :: "log \<Rightarrow> iEFSM \<Rightarrow> ((tids \<times> transition) list \<times> (registers \<times> value list \<times> value list) list) list \<Rightarrow> iEFSM" where
  "groupwise_generalise_and_update _ e [] = e" |
  "groupwise_generalise_and_update log e (gp#t) = (
    case generalise_and_update log e (fst gp) (snd gp) of
      None \<Rightarrow> groupwise_generalise_and_update log e t |
      Some e' \<Rightarrow> groupwise_generalise_and_update log e' t
  )"

lemma groupwise_generalise_and_update_fold [code]:

"groupwise_generalise_and_update log e gs = fold (\<lambda>gp e.
  case generalise_and_update log e (fst gp) (snd gp) of
        None \<Rightarrow> e |
        Some e' \<Rightarrow> e'
  ) gs e"
  apply(induct gs arbitrary: e)
   apply simp
  by (case_tac a, case_tac "generalise_and_update log e aa b", auto)

definition standardise_outputs :: "(vname aexp \<Rightarrow> vname aexp \<Rightarrow> vname aexp) \<Rightarrow> vname aexp list \<Rightarrow> vname aexp list \<Rightarrow> vname aexp list" where
  "standardise_outputs f p1 p2 = map (\<lambda>(p1, p2). f p1 p2) (zip p1 p2)"

definition standardise_group_outputs :: "(vname aexp \<Rightarrow> vname aexp \<Rightarrow> vname aexp) \<Rightarrow> (tids \<times> transition) list \<Rightarrow> (tids \<times> transition) list" where
  "standardise_group_outputs f g = (
    let
      outputs = case g of 
        [] \<Rightarrow> [] |
        (h#t) \<Rightarrow> fold (\<lambda>x acc. standardise_outputs f x acc) (map (Outputs \<circ> snd) t) (Outputs (snd h))
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

definition max_min_outputs :: "iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list \<Rightarrow> (tids \<times> transition) list" where
"max_min_outputs e l ts = (
    let
      outputs_max = standardise_group_outputs max ts;
      outputs_min = standardise_group_outputs min ts;
      e_max = fold (\<lambda>(tids, t) acc. replace_transition acc tids t) outputs_max e;
      e_min = fold (\<lambda>(tids, t) acc. replace_transition acc tids t) outputs_min e
    in
      if satisfies (set l) (tm e_max) then outputs_max else
      if satisfies (set l) (tm e_min) then outputs_min else
      ts
)"

definition "updates_same u1 u2 = (fst u1 = fst u2)"

definition cartProdN :: "'a list list \<Rightarrow> 'a list list" where
  "cartProdN l = foldr (\<lambda>xs as. [ x # a. x \<leftarrow> xs , a \<leftarrow> as ]) l [[]]"

primrec find_outputs :: "output_function list list \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list \<Rightarrow> output_function list option" where
  "find_outputs [] _ _ _ = None" |
  "find_outputs (h#t) e l g = (
    let
      outputs = fold (\<lambda>(tids, t) acc. replace_transition acc tids (t\<lparr>Outputs := h\<rparr>)) g e
    in
      if satisfies (set l) (tm outputs) then
        Some h
      else
        find_outputs t e l g
  )"

definition "this x = (case x of Some y \<Rightarrow> y)"

definition replace_updates :: "transition \<Rightarrow> update_function list \<Rightarrow> transition" where
  "replace_updates t u = (
    let
      oldUpdates = map_of (Updates t);
      newUpdates = (\<lambda>r. case (map_of u) r of Some a \<Rightarrow> Some a | None \<Rightarrow> oldUpdates r)
    in
    t\<lparr>Updates := map (\<lambda>(r, _). (r, this (newUpdates r))) (Updates t)\<rparr>
  )"

primrec find_updates_outputs :: "update_function list list \<Rightarrow> output_function list list \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list \<Rightarrow> (output_function list \<times> update_function list) option" where
  "find_updates_outputs [] _ _ _ _ = None" |
  "find_updates_outputs (h#t) p e l g = (
    let
      updates = fold (\<lambda>(tids, t) acc. replace_transition acc tids (replace_updates t h)) g e
    in
      case find_outputs p updates l g of
        Some pp \<Rightarrow> Some (pp, h) |
        None \<Rightarrow> find_updates_outputs t p e l g
  )"

definition power_list :: "('a::linorder) list \<Rightarrow> 'a list list" where
  "power_list l = sorted_list_of_set (image sorted_list_of_set (Pow (set l)))"

definition power_lists :: "'a::linorder list list \<Rightarrow> 'a list list" where
  "power_lists l = fold List.union (map power_list l) []"

(* Try max and min output function with satisfies *)
definition standardise_group_outputs_updates :: "iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list \<Rightarrow> (tids \<times> transition) list" where
  "standardise_group_outputs_updates e l g = (
    let
      update_groups = cartProdN (group_by updates_same (sort (remdups (List.maps (Updates \<circ> snd) g))));
      update_groups_subs = power_lists update_groups;
      output_groups = cartProdN (transpose (remdups (map (Outputs \<circ> snd) g)))
    in
    case find_updates_outputs update_groups_subs output_groups e l g of
      None \<Rightarrow> g |
      Some (p, u) \<Rightarrow> map (\<lambda>(id, t). (id, t\<lparr>Outputs := p, Updates := u\<rparr>)) g
  )"

(* Sometimes inserting updates without redundancy can cause certain transitions to not get a      *)
(* particular update function. This can lead to disparate groups of transitions which we want to  *)
(* standardise such that every group of transitions has the same update function                  *)
primrec standardise_groups_aux :: "iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list list \<Rightarrow> (iEFSM \<Rightarrow> log \<Rightarrow> (tids \<times> transition) list \<Rightarrow> (tids \<times> transition) list) \<Rightarrow> iEFSM" where
  "standardise_groups_aux e _ [] _ = e" |
  "standardise_groups_aux e l (h#t) s = (
    let
      standardised = s e l h;
      e' = replace_transitions e standardised
    in
      if satisfies (set l) (tm e') then
        standardise_groups_aux e' l t s
      else
        standardise_groups_aux e l t s
  )"

lemma standardise_groups_aux_fold [code]:
"standardise_groups_aux e l xs s = fold (\<lambda>h acc. 
  let
      e' = replace_transitions acc (s acc l h)
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
  "standardise_groups e l = standardise_groups_aux e l (group_by_structure e) standardise_group_outputs_updates"

definition standardise_groups_updates :: "iEFSM \<Rightarrow> log \<Rightarrow> iEFSM" where
  "standardise_groups_updates e l = standardise_groups_aux e l (group_by_structure e) (\<lambda>_ _. standardise_group_updates)"

\<comment> \<open>Need to derestrict variables which occur in the updates but keep unrelated ones to avoid \<close>
\<comment> \<open>nondeterminism creeping in too early in the inference process                            \<close>
definition derestrict_transition :: "transition \<Rightarrow> transition" where
  "derestrict_transition t = (
    let relevant_vars = image V (fold (\<lambda>(r, u) acc. acc \<union> (AExp.enumerate_vars u)) (Updates t) {}) in
    t\<lparr>Guards := filter (\<lambda>g. \<forall>v \<in> relevant_vars. \<not> gexp_constrains g v) (Guards t)\<rparr>
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

definition drop_all_guards :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> log \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
"drop_all_guards e pta log m np = (let
      derestricted = fimage (\<lambda>(id, tf, tran). (id, tf, tran\<lparr>Guards := []\<rparr>)) e;
      nondeterministic_pairs = sorted_list_of_fset (np derestricted)
    in
    case resolve_nondeterminism {} nondeterministic_pairs pta derestricted m (satisfies (set log)) np of
      (None, _) \<Rightarrow> pta |
      (Some resolved, _) \<Rightarrow> resolved
  )"

fun merge_if_same :: "iEFSM \<Rightarrow> log \<Rightarrow> (nat \<times> nat) list \<Rightarrow> iEFSM" where
  "merge_if_same e _ [] = e" |
  "merge_if_same e l ((r1, r2)#rs) = (
    let transitions = fimage (snd \<circ> snd) e in
    if \<exists>(t1, t2) |\<in>| ffilter (\<lambda>(t1, t2). t1 < t2) (transitions |\<times>| transitions).
      same_structure t1 t2 \<and> r1 \<in> enumerate_regs t1 \<and> r2 \<in> enumerate_regs t2
    then
      let newE = replace_with e r1 r2 in
      if satisfies (set l) (tm newE) then
        merge_if_same newE l rs
      else
        merge_if_same e l rs
    else
      merge_if_same e l rs
  )"

definition merge_regs :: "iEFSM \<Rightarrow> log \<Rightarrow> iEFSM" where
  "merge_regs e l = (
    let
      regs = all_regs e;
      reg_pairs = sorted_list_of_set (Set.filter (\<lambda>(r1, r2). r1 < r2) (regs \<times> regs))
    in
    merge_if_same e l reg_pairs
  )"

definition updated_regs :: "transition \<Rightarrow> nat set" where
  "updated_regs t = set (map fst (Updates t))"

definition fewer_updates :: "transition \<Rightarrow> transition fset \<Rightarrow> transition option" where
  "fewer_updates t T = (
    let p = ffilter (\<lambda>t'. same_structure t t' \<and> Outputs t = Outputs t' \<and> updated_regs t' \<subset> updated_regs t) T in
    if p = {||} then None else Some (snd (fMin (fimage (\<lambda>t. (length (Updates t), t)) p))))"

fun remove_spurious_updates_aux :: "iEFSM \<Rightarrow> (tids \<times> transition) list \<Rightarrow> transition fset \<Rightarrow> log \<Rightarrow> iEFSM" where
  "remove_spurious_updates_aux e [] _ _ = e" |
  "remove_spurious_updates_aux e ((tid, t)#ts) T l = (
    case fewer_updates t T of
      None \<Rightarrow> remove_spurious_updates_aux e ts T l |
      Some t' \<Rightarrow> (
        let e' = replace_transition e tid t' in
        if satisfies (set l) (tm e') then
          remove_spurious_updates_aux e' ts T l
        else
          remove_spurious_updates_aux e ts T l
      )
  )"

(* This goes through and tries to remove spurious updates that get introduced during preprocessing *)
definition remove_spurious_updates :: "iEFSM \<Rightarrow> log \<Rightarrow> iEFSM" where
  "remove_spurious_updates e l = (
    let transitions = fimage (\<lambda>(tid, _, t). (tid, t)) e in
      remove_spurious_updates_aux e (sorted_list_of_fset transitions) (fimage snd transitions) l
  )"

definition derestrict :: "iEFSM \<Rightarrow> log \<Rightarrow> update_modifier \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "derestrict pta log m np = (
    let
      training_set = make_training_set pta log;
      normalised = groupwise_generalise_and_update log pta training_set;
      standardised = standardise_groups normalised log;
      delayed = fold (\<lambda>r acc. delay_initialisation_of r log acc (find_first_uses_of r log acc)) (sorted_list_of_set (all_regs standardised)) standardised;
      merged = remove_spurious_updates (merge_regs delayed log) log
    in
      drop_all_guards merged pta log m np
  )"

definition "drop_pta_guards pta log m np = drop_all_guards pta pta log m np"

end