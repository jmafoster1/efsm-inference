theory Symbolic_Regression
imports "../Inference" "Distinguishing_Guards"
begin

hide_const I

type_synonym indexed_execution = "(nat \<times> label \<times> inputs \<times> value list) list"
type_synonym indexed_log = "(nat \<times> indexed_execution) list"
type_synonym flat_log = "(nat \<times> nat \<times> label \<times> inputs \<times> value list) list"

fun flatten :: "indexed_log \<Rightarrow> flat_log \<Rightarrow> flat_log" where
  "flatten [] l = l" |
  "flatten ((k, e)#t) l = flatten t (l@(map (\<lambda>v. (k, v)) e))"

\<comment> \<open>This will be replaced by symbolic regression in the executable\<close>
definition get_function :: "nat \<Rightarrow> value list \<Rightarrow> inputs list \<Rightarrow> value list \<Rightarrow> (aexp \<times> (vname \<Rightarrow>f String.literal)) option" where
  "get_function maxReg values I P = (let
    possible_funs = {a. \<forall>(i, p) \<in> set (zip I P). \<exists>r. aval a (join_ir i r) = Some p}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs), (K$ STR ''int''))
  )"
declare get_function_def [code del]
code_printing constant get_function \<rightharpoonup> (Scala) "Dirties.getFunction"

definition get_inputs :: "flat_log \<Rightarrow> inputs list" where
  "get_inputs l = map (\<lambda>(_, _, _, i, _). i) l"

definition get_outputs :: "flat_log \<Rightarrow> nat \<Rightarrow> value list" where
  "get_outputs l n = map (\<lambda>(_, _, _, _, p). p ! n) l"

definition get_functions :: "nat \<Rightarrow> value list \<Rightarrow> nat \<Rightarrow> flat_log \<Rightarrow> (aexp \<times> (vname \<Rightarrow>f String.literal)) option list" where
  "get_functions maxReg values n l = map (\<lambda>p. get_function maxReg values (get_inputs l) (get_outputs l p)) [0..<n]"

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
    \<lparr>Label = Label t, Arity = Arity t, Guard = filter (\<lambda>g. \<forall>v \<in> relevant_vars. \<not> gexp_constrains g v) (Guard t), Outputs = Outputs t, Updates = (filter (\<lambda>(r, _). r \<notin> set (map fst u)) (Updates t))@necessary_updates\<rparr>
  )"

definition drop_guard :: "transition \<Rightarrow> transition" where
  "drop_guard t = \<lparr>Label = Label t, Arity = Arity t, Guard = [], Outputs = Outputs t, Updates = Updates t\<rparr>"

definition insert_outputs :: "transition \<Rightarrow> aexp option \<Rightarrow> nat \<Rightarrow> transition" where
  "insert_outputs t op ox = (case op of None \<Rightarrow> t | Some a \<Rightarrow> \<lparr>Label = Label t, Arity = Arity t, Guard = Guard t, Outputs = list_update (Outputs t) ox a, Updates = (Updates t)\<rparr>)"

fun put_update_function_aux :: "aexp option \<Rightarrow> nat \<Rightarrow> update_function list \<Rightarrow> indexed_execution \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> iEFSM option" where
  "put_update_function_aux _ _ _ [] _ _ _ e _ _ = Some e" |
  "put_update_function_aux op ox us ((_, l, i, p)#t) label i_arity pta target s r = (
    let
      poss_steps = ffilter (\<lambda>(_, _, t). apply_outputs (Outputs t) (join_ir i r) = map Some p) (i_possible_steps pta s r l i);
      (tid, s', ta) =  fthe_elem poss_steps;
      ta = get_by_id target (hd tid)
    in
     \<comment> \<open>Possible steps with a transition we need to modify\<close>
    if l = label \<and> length i = i_arity then let
      newT = drop_guard (insert_outputs (insert_updates ta us) op ox);
      newE = make_distinct (replace_transitions target [(tid, newT)])
      in
      put_update_function_aux op ox us t label i_arity pta newE s' (apply_updates (Updates ta) (join_ir i r) r)
     \<comment> \<open>Possible steps but not interesting - just take a transition and move on\<close>
    else
      put_update_function_aux op ox us t label i_arity pta target s' (apply_updates (Updates ta) (join_ir i r) r)
  )"

primrec put_update_functions :: "aexp option \<Rightarrow> nat \<Rightarrow> update_function list \<Rightarrow> indexed_log \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_update_functions _ _  _ [] _ _ pta target = Some target" |
  "put_update_functions op ox us (h#t) label arity pta target = (
    case put_update_function_aux op ox us (snd h) label arity pta target 0 <> of
      None \<Rightarrow> None |       
      Some e' \<Rightarrow> put_update_functions op ox us t label arity pta (make_distinct e')
  )"

\<comment> \<open>This will be replaced to calls to Z3 in the executable\<close>
definition get_regs :: "(vname \<Rightarrow>f String.literal) \<Rightarrow> inputs \<Rightarrow> aexp \<Rightarrow> value \<Rightarrow> registers" where
  "get_regs types inputs expression output = Eps (\<lambda>r. aval expression (join_ir inputs r) = Some output)"

fun put_output_function_2_aux :: "nat \<Rightarrow> aexp \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> indexed_execution \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> arity \<Rightarrow> tids option \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> iEFSM option" where
  "put_output_function_2_aux _ _ _ [] _ _ _ _ e _ _ = Some e" |
  "put_output_function_2_aux fi f types ((_, l, i, p)#t) label i_arity o_arity prevtid e s r = (
    let
      poss_steps = ffilter (\<lambda>(_, _, t). apply_outputs (Outputs t) (join_ir i r) = map Some p) (i_possible_steps e s r l i);
      (tid, s', ta) = fthe_elem poss_steps
    in
     \<comment> \<open>Possible steps with a transition we need to modify\<close>
    if l = label \<and> length i = i_arity \<and> length p = o_arity then
      case prevtid of None \<Rightarrow> None | Some prevtid \<Rightarrow> let
      satisfyingRegs = get_regs types i f (p!fi);
      necessaryRegs = finfun_to_list satisfyingRegs in
      if length necessaryRegs \<noteq> 1 then None else let
      newT = \<lparr>Label = Label ta, Arity = Arity ta, Guard = [], Outputs = list_update (Outputs ta) fi f, Updates = remdups ((hd necessaryRegs, f)#(Updates ta))\<rparr>;
      updates = map (\<lambda>r. case (satisfyingRegs $ r) of Some v' \<Rightarrow> (r, L v')) (necessaryRegs);
      prevT = get_by_ids e prevtid;
      newPrevT = (if Label prevT = Label ta then
        \<lparr>Label = Label prevT, Arity = Arity prevT, Guard = [], Outputs = Outputs prevT, Updates = remdups ((hd necessaryRegs, f)#(Updates prevT))\<rparr>
        else
        \<lparr>Label = Label prevT, Arity = Arity prevT, Guard = Guard prevT, Outputs = Outputs prevT, Updates = remdups (updates@(Updates prevT))\<rparr>);
      newE = replace_transitions e [(tid, newT), (prevtid, newPrevT)]
      in
      put_output_function_2_aux fi f types t label i_arity o_arity (Some tid) newE s' (apply_updates (Updates ta) (join_ir i r) r)
     \<comment> \<open>Possible steps but not interesting - just take a transition and move on\<close>
    else
      put_output_function_2_aux fi f types t label i_arity o_arity (Some tid) e s' (apply_updates (Updates ta) (join_ir i r) r)
  )"

primrec put_output_function_2 :: "nat \<Rightarrow> aexp \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> indexed_log \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_output_function_2 _ _ _ [] _ e = Some e" |
  "put_output_function_2 fi f types (h#t) t1 e = (case put_output_function_2_aux fi f types (snd h) (Label t1) (Arity t1) (length (Outputs t1)) None e 0 <> of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> put_output_function_2 fi f types t t1 e'
  )"

fun put_output_functions_2 :: "(nat \<times> (aexp \<times> (vname \<Rightarrow>f String.literal)) option) list \<Rightarrow> indexed_log \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_output_functions_2 [] _ _ e = Some e" |
  "put_output_functions_2 ((_, None)#_) _ _ _ = None" |
  "put_output_functions_2 ((fi, Some (f, types))#rest) log t e = (case put_output_function_2 fi f types log t e of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> put_output_functions_2 rest log t e'
  )"

primrec overwrites_update :: "update_function list \<Rightarrow> nat set \<Rightarrow> bool" where
  "overwrites_update [] _ = False" |
  "overwrites_update (h#t) s = (if fst h \<in> s then True else overwrites_update t (insert (fst h) s))"

fun put_output_function_aux :: "nat \<Rightarrow> aexp \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> indexed_execution \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> arity \<Rightarrow> tids option \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> iEFSM option" where
  "put_output_function_aux _ _ _ [] _ _ _ _ e _ _ = (
    if \<exists>(_, _, t) |\<in>| e. overwrites_update (Updates t) {} then
      None
    else
      Some e
  )" |
  "put_output_function_aux fi f types ((_, l, i, p)#t) label i_arity o_arity prevtid e s r = (
    let
    poss_steps = ffilter (\<lambda>(_, _, t). apply_outputs (Outputs t) (join_ir i r) = map Some p) (i_possible_steps e s r l i) in
    \<comment> \<open>No possible steps with matching output means something bad has happenned\<close>
    case random_member poss_steps of
      None \<Rightarrow> None |
      Some (tid, s', ta) \<Rightarrow>
       \<comment> \<open>Possible steps with a transition we need to modify\<close>
      if l = label \<and> length i = i_arity \<and> length p = o_arity then let
        newT = \<lparr>Label = Label ta, Arity = Arity ta, Guard = Guard ta, Outputs = list_update (Outputs ta) fi f, Updates = Updates ta\<rparr>;
        necessaryRegs = get_regs types i f (p!fi);
        updates = map (\<lambda>r. case (necessaryRegs $ r) of Some v' \<Rightarrow> (r, L v')) (finfun_to_list necessaryRegs) in
        case prevtid of None \<Rightarrow> None | Some prevtid \<Rightarrow> let
        prevT = get_by_ids e prevtid;
        newPrevT = \<lparr>Label = Label prevT, Arity = Arity prevT, Guard = Guard prevT, Outputs = Outputs prevT, Updates = remdups ((Updates prevT)@updates)\<rparr>;
        newE = replace_transitions e [(tid, newT), (prevtid, newPrevT)]
        in
        if \<exists>(_, _, t) |\<in>| newE. overwrites_update (Updates t) {} then
          None
        else
          put_output_function_aux fi f types t label i_arity o_arity (Some tid) newE s' (apply_updates (Updates ta) (join_ir i r) r)
       \<comment> \<open>Possible steps but not interesting - just take a transition and move on\<close>
      else
        put_output_function_aux fi f types t label i_arity o_arity (Some tid) e s' (apply_updates (Updates ta) (join_ir i r) r)
  )"

primrec put_output_function :: "nat \<Rightarrow> aexp \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> indexed_log \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_output_function _ _ _ [] _ e = Some e" |
  "put_output_function fi f types (h#t) t1 e = (case put_output_function_aux fi f types (snd h) (Label t1) (Arity t1) (length (Outputs t1)) None e 0 <> of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> put_output_function fi f types t t1 e'
  )"

fun put_output_functions :: "(nat \<times> (aexp \<times> (vname \<Rightarrow>f String.literal)) option) list \<Rightarrow> indexed_log \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_output_functions [] _ _ e = Some e" |
  "put_output_functions ((_, None)#_) _ _ _ = None" |
  "put_output_functions ((fi, Some (f, types))#rest) log t e = (case put_output_function fi f types log t e of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> put_output_functions rest log t e'
  )"

definition infer_output_functions :: "log \<Rightarrow> update_modifier" where
  "infer_output_functions log t1ID t2ID s new _ old _ = (let
     t1 = get_by_ids new t1ID;
     i_log = enumerate 0 (map (enumerate 0) log);
     num_outs = length (Outputs t1);
     relevant_events = flatten (map (\<lambda>(i, ex). (i, filter (\<lambda>(_, l, ip, op). l = Label t1 \<and> length ip = Arity t1 \<and> length op = num_outs) ex)) i_log) [];
     values = enumerate_log_values log;
     max_reg = max_reg_total new;
     output_functions = get_functions max_reg values (length (Outputs t1)) relevant_events
     in put_output_functions (enumerate 0 output_functions) i_log t1 new
   )"

definition infer_output_functions_2 :: "log \<Rightarrow> update_modifier" where
  "infer_output_functions_2 log t1ID t2ID s new _ old _ = (let
     t1 = get_by_ids new t1ID;
     i_log = enumerate 0 (map (enumerate 0) log);
     num_outs = length (Outputs t1);
     relevant_events = flatten (map (\<lambda>(i, ex). (i, filter (\<lambda>(_, l, ip, op). l = Label t1 \<and> length ip = Arity t1 \<and> length op = num_outs) ex)) i_log) [];
     values = enumerate_log_values log;
     max_reg = max_reg_total new;
     output_functions = get_functions max_reg values (length (Outputs t1)) relevant_events
     in put_output_functions_2 (enumerate 0 output_functions) i_log t1 new
   )"

definition "is_updated r t = (length (filter (\<lambda>(r', _). r' = r) (Updates t)) \<ge> 1)"

fun get_exec_reg_values :: "aexp \<Rightarrow> indexed_execution \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> (inputs \<times> registers \<times> registers) list" where
  "get_exec_reg_values _ [] _ _ _ _ _ = []" |
  "get_exec_reg_values f ((_, l, i, p)#t) label i_arity e s r = (
    let
    poss_steps = ffilter (\<lambda>(_, _, t). apply_outputs (Outputs t) (join_ir i r) = map Some p) (i_possible_steps e s r l i);
    (tid, s', ta) = fthe_elem poss_steps;
    updated = (apply_updates (Updates ta) (join_ir i r) r)
    in
       \<comment> \<open>Possible steps with a transition we're interested in\<close>
      if l = label \<and> length i = i_arity then 
        if \<forall>r \<in> enumerate_aexp_regs f. is_updated r ta then
          List.insert (i, r, updated) (get_exec_reg_values f t label i_arity e s' updated)
        else get_exec_reg_values f t label i_arity e s' updated
       \<comment> \<open>Possible steps but not interesting - just take a transition and move on\<close>
      else
        get_exec_reg_values f t label i_arity e s' updated
  )"

fun get_log_reg_values :: "aexp \<Rightarrow> indexed_log \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> iEFSM \<Rightarrow> (inputs \<times> registers \<times> registers) list" where
  "get_log_reg_values _ [] _ _ _ = []" |
  "get_log_reg_values a (h#t) l ia pta = List.union (get_exec_reg_values a (snd h) l ia pta 0 <>) (get_log_reg_values a t l ia pta)"

\<comment> \<open>This will be replaced by symbolic regression in the executable\<close>
definition get_update :: "nat \<Rightarrow> value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> aexp option" where
  "get_update reg values train = (let
    possible_funs = {a. \<forall>(i, r, r') \<in> set train. aval a (join_ir i r) = r' $ reg}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs))
  )"

definition get_updates :: "value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> (nat \<times> aexp) list" where
  "get_updates values train = (let
    updated_regs = fold List.union (map (finfun_to_list \<circ> snd \<circ> snd) train) [];
    maybe_updates = map (\<lambda>r. (r, get_update r values train)) updated_regs;
    updates = filter (\<lambda>(r, u). u \<noteq> None) maybe_updates
    in map (\<lambda>(r, u). case u of Some u' \<Rightarrow> (r, u')) updates
  )"

fun outputwise_updates :: "value list \<Rightarrow> nat \<Rightarrow> (aexp \<times> (vname \<Rightarrow>f String.literal)) option list \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> indexed_log \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> iEFSM option" where
  "outputwise_updates _ _ [] pta e _ _ _ = Some e" |
  "outputwise_updates values ox (None#t) pta e log label arity = outputwise_updates values (ox + 1) t pta e log label arity" |
  "outputwise_updates values ox ((Some (a, types))#t) pta e log label arity = (
    let
      train = get_log_reg_values a log label arity pta;
      update_functions = get_updates values train
    in
    case put_update_functions (Some a) ox update_functions log label arity pta e of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> outputwise_updates values (ox + 1) t pta e' log label arity
  )"

fun transfer_updates :: "(tids \<times> (cfstate \<times> cfstate) \<times> transition) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "transfer_updates [] target = target" |
  "transfer_updates ((uid, (from, to), t)#ts) target = (let
    correspondingTransition = get_by_id target (hd uid);
    updatedT = insert_updates correspondingTransition (Updates t)
    in
    transfer_updates ts (replace_transition target uid updatedT)
  )"

definition infer_output_update_functions :: "log \<Rightarrow> update_modifier" where
  "infer_output_update_functions log t1ID t2ID s new _ old _ = (let
     t1 = get_by_ids new t1ID;
     i_log = enumerate 0 (map (enumerate 0) log);
     num_outs = length (Outputs t1);
     relevant_events = flatten (map (\<lambda>(i, ex). (i, filter (\<lambda>(_, l, ip, op). l = Label t1 \<and> length ip = Arity t1 \<and> length op = num_outs) ex)) i_log) [];
     values = enumerate_log_values log;
     max_reg = max_reg_total new;
     output_functions = get_functions max_reg values (length (Outputs t1)) relevant_events;
     pta = make_pta log;
     lit_updates = put_output_functions (enumerate 0 output_functions) i_log t1 pta in
     case lit_updates of
      None \<Rightarrow> None |
      Some e' \<Rightarrow> (
          outputwise_updates values 0 output_functions e' (transfer_updates (sorted_list_of_fset e') new) i_log (Label t1) (Arity t1)
      )
   )"

type_synonym event_info = "(cfstate \<times> registers \<times> inputs \<times> tids \<times> transition)"
type_synonym run_info = "event_info list"
type_synonym targeted_run_info = "(registers \<times> event_info) list"

fun everything_walk :: "output_function \<Rightarrow> nat \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> execution \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> arity \<Rightarrow> run_info" where
  "everything_walk _ _ _ [] _ _ _ _ _ _ = []" |
  "everything_walk f fi types ((label, inputs, outputs)#t) oPTA s regs ll i_arity o_arity  = (
    let (tid, s', ta) = fthe_elem (i_possible_steps oPTA s regs label inputs) in
     \<comment> \<open>Possible steps with a transition we need to modify\<close>
    if ll = label \<and> length inputs = i_arity \<and> length (Outputs ta) = o_arity then
      (s, get_regs types inputs f (outputs!fi), inputs, tid, ta)#(everything_walk f fi types t oPTA s' (apply_updates (Updates ta) (join_ir inputs regs) regs) ll i_arity o_arity)
    else
      let empty = <> in
      (s, empty, inputs, tid, ta)#(everything_walk f fi types t oPTA s' (apply_updates (Updates ta) (join_ir inputs regs) regs) ll i_arity o_arity)
  )"

definition everything_walk_log :: "output_function \<Rightarrow> nat \<Rightarrow> (vname \<Rightarrow>f String.literal) \<Rightarrow> log \<Rightarrow> iEFSM \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> arity \<Rightarrow> run_info list" where
  "everything_walk_log f fi types log e l ia oa = map (\<lambda>t. everything_walk f fi types t e 0 <> l ia oa) log"

fun target :: "registers \<Rightarrow> run_info \<Rightarrow> targeted_run_info" where
  "target _ [] = []" |
  "target tRegs ((s, regs, inputs, tid, ta)#t) = (
    let newTarget = if finfun_to_list regs = [] then tRegs else regs in
    (tRegs, s, regs, inputs, tid, ta)#target newTarget t
  )"

fun structural_insert :: "(registers \<times> event_info) \<Rightarrow> (registers \<times> event_info) list list \<Rightarrow> (registers \<times> event_info) list list" where
  "structural_insert x [] = [[x]]" |
  "structural_insert x (h#t) = (
    case x of (_, _, _, _, _, ta) \<Rightarrow>
    if \<exists>(_, _, _, _, _, tb) \<in> set h. same_structure ta tb then
      (List.insert x h)#t
    else
      h#structural_insert x t
  )"

definition group_by_structure :: "targeted_run_info \<Rightarrow> targeted_run_info list \<Rightarrow> targeted_run_info list" where
  "group_by_structure info groups = fold (\<lambda>event acc. structural_insert event acc) info []"

definition get_updates_opt :: "value list \<Rightarrow> (inputs \<times> registers \<times> registers) list \<Rightarrow> (nat \<times> aexp option) list" where
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

fun group_update :: "value list \<Rightarrow> targeted_run_info \<Rightarrow> (tids \<times> (nat \<times> aexp) list) option" where
  "group_update values l = (
    let
      targeted = filter (\<lambda>(regs, _). finfun_to_list regs \<noteq> []) l;
      maybe_updates = get_updates_opt values (map (\<lambda>(tRegs, s, regs, inputs, tid, ta). (inputs, regs, tRegs)) targeted)
    in
    if \<exists>(_, f_opt) \<in> set maybe_updates. f_opt = None then
      None
    else
      Some (fold List.union (map (\<lambda>(tRegs, s, regs, inputs, tid, ta). tid) l) [], map (\<lambda>(r, f_o). (r, the f_o)) maybe_updates)
  )"

fun groupwise_updates :: "value list \<Rightarrow> targeted_run_info list \<Rightarrow> (tids \<times> update_function list) option list" where
  "groupwise_updates values [] = []" |
  "groupwise_updates values (g#gs) = (
    if \<forall>(regs, _) \<in> set g. finfun_to_list regs = [] then
      groupwise_updates values gs
    else
      (group_update values g) # groupwise_updates values gs 
  )"



end