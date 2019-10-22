theory Symbolic_Regression
imports "../Inference"
begin

hide_const I

type_synonym indexed_execution = "(nat \<times> label \<times> inputs \<times> value list) list"
type_synonym indexed_log = "(nat \<times> indexed_execution) list"
type_synonym flat_log = "(nat \<times> nat \<times> label \<times> inputs \<times> value list) list"

fun flatten :: "indexed_log \<Rightarrow> flat_log \<Rightarrow> flat_log" where
  "flatten [] l = l" |
  "flatten ((k, e)#t) l = flatten t (l@(map (\<lambda>v. (k, v)) e))"

\<comment> \<open>This will be replaced by symbolic regression in the executable\<close>
definition get_function :: "nat \<Rightarrow> int list \<Rightarrow> inputs list \<Rightarrow> value list \<Rightarrow> aexp option" where
  "get_function maxReg values I P = (let
    possible_funs = {a. \<forall>(i, p) \<in> set (zip I P). \<exists>r. aval a (join_ir i r) = Some p}
    in
    if possible_funs = {} then None else Some (Eps (\<lambda>x. x \<in> possible_funs))
  )"

definition get_inputs :: "flat_log \<Rightarrow> inputs list" where
  "get_inputs l = map (\<lambda>(_, _, _, i, _). i) l"

definition get_outputs :: "flat_log \<Rightarrow> nat \<Rightarrow> value list" where
  "get_outputs l n = map (\<lambda>(_, _, _, _, p). p ! n) l"

definition get_functions :: "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> flat_log \<Rightarrow> aexp option list" where
  "get_functions maxReg values n l = map (\<lambda>p. get_function maxReg values (get_inputs l) (get_outputs l p)) [0..<n]"

\<comment> \<open>This will be replaced to calls to Z3 in the executable\<close>
definition get_regs :: "inputs \<Rightarrow> aexp \<Rightarrow> value \<Rightarrow> registers" where
  "get_regs i a v = Eps (\<lambda>r. aval a (join_ir i r) = Some v)"

definition finfun2pairs :: "('a::linorder \<Rightarrow>f 'b) \<Rightarrow> ('a \<times> 'b) list" where
  "finfun2pairs f = (let
    keys = finfun_to_list f;
    values = map (\<lambda>k. f $ k) keys
    in zip keys values
   )"

fun replace_transitions :: "(tid \<times> transition) list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "replace_transitions [] e = e" |
  "replace_transitions ((ti, t)#rest) e = replace_transitions rest (fimage (\<lambda>(id', od, t'). if id' = ti then (id', od, t) else (id', od, t')) e)"

fun put_output_function_aux :: "nat \<Rightarrow> aexp \<Rightarrow> indexed_execution \<Rightarrow> label \<Rightarrow> arity \<Rightarrow> arity \<Rightarrow> tid option \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> iEFSM option" where
  "put_output_function_aux _ _ [] _ _ _ _ e _ _ = Some e" |
  "put_output_function_aux fi f ((_, l, i, p)#t) label i_arity o_arity prevtid e s r = (
    let
    poss_steps = ffilter (\<lambda>(_, _, t). apply_outputs (Outputs t) (join_ir i r) = map Some p) (i_possible_steps e s r l i) in
    \<comment> \<open>No possible steps with matching output means something bad has happenned\<close>
    case random_member poss_steps of
      None \<Rightarrow> None |
      Some (tid, s', ta) \<Rightarrow>
       \<comment> \<open>Possible steps with a transition we need to modify\<close>
      if l = label \<and> length i \<noteq> i_arity \<and> length p \<noteq> o_arity then let
        newT = \<lparr>Label = Label ta, Arity = Arity ta, Guard = Guard ta, Outputs = list_update (Outputs ta) fi f, Updates = Updates ta\<rparr>;
        necessaryRegs = get_regs i f (p!fi);
        updates = map (\<lambda>r. case (necessaryRegs $ r) of Some v' \<Rightarrow> (r, L v')) (finfun_to_list necessaryRegs) in
        case prevtid of None \<Rightarrow> None | Some prevtid \<Rightarrow> let
        prevT = get_by_id e prevtid;
        newPrevT = \<lparr>Label = Label prevT, Arity = Arity prevT, Guard = Guard prevT, Outputs = Outputs prevT, Updates = (Updates prevT)@updates\<rparr>;
        newE = replace_transitions [(tid, newT), (prevtid, newPrevT)] e
        in
        put_output_function_aux fi f t label i_arity o_arity (Some tid) newE s' (apply_updates (Updates ta) (join_ir i r) r)
       \<comment> \<open>Possible steps but not interesting - just take a transition and move on\<close>
      else
        put_output_function_aux fi f t label i_arity o_arity (Some tid) e s' (apply_updates (Updates ta) (join_ir i r) r)
  )"

primrec put_output_function :: "nat \<Rightarrow> aexp \<Rightarrow> indexed_log \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_output_function _ _ [] _ e = Some e" |
  "put_output_function fi f (h#t) t1 e = (case put_output_function_aux fi f (snd h) (Label t1) (Arity t1) (length (Outputs t1)) None e 0 <> of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> put_output_function fi f t t1 e')"

fun put_output_functions :: "(nat \<times> aexp option) list \<Rightarrow> indexed_log \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM option" where
  "put_output_functions [] _ _ e = Some e" |
  "put_output_functions ((_, None)#_) _ _ _ = None" |
  "put_output_functions ((fi, Some f)#rest) log t e = (case put_output_function fi f log t e of
    None \<Rightarrow> None |
    Some e' \<Rightarrow> put_output_functions rest log t e'
   )"

definition enumerate_value_ints :: "value list \<Rightarrow> int list" where
  "enumerate_value_ints vs = map (\<lambda>v. case v of Num n \<Rightarrow> n) (filter (\<lambda>v. case v of Num _ \<Rightarrow> True | value.Str _ \<Rightarrow> False) vs)"

definition enumerate_exec_ints :: "execution \<Rightarrow> int list" where
  "enumerate_exec_ints vs = fold (\<lambda>(_, i, p) I. (enumerate_value_ints i) @ (enumerate_value_ints p) @ I) vs []"

definition enumerate_log_ints :: "log \<Rightarrow> int list" where
  "enumerate_log_ints l = fold (\<lambda>e I. enumerate_exec_ints e @ I) l []"

definition infer_output_functions :: "log \<Rightarrow> update_modifier" where
  "infer_output_functions log t1ID t2ID s new old _ = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID);
     i_log = enumerate 0 (map (enumerate 0) log);
     num_outs = length (Outputs t1);
     relevant_events = flatten (map (\<lambda>(i, ex). (i, filter (\<lambda>(_, l, ip, op). l = Label t1 \<and> length ip = Arity t1 \<and> length op = num_outs) ex)) i_log) [];
     values = enumerate_log_ints log;
     max_reg = max_reg_total new;
     output_functions = get_functions max_reg values (length (Outputs t1)) relevant_events
     in put_output_functions (enumerate 0 output_functions) i_log t1 new
   )"

end