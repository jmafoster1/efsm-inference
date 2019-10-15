theory Symbolic_Regression
imports "../Inference"
begin

hide_const I

datatype numOrStr = N | S

fun typeChecks :: "numOrStr list \<Rightarrow> value list \<Rightarrow> bool" where
  "typeChecks [] [] = True" |
  "typeChecks (N#tt) ((Num _)#tv) = typeChecks tt tv" |
  "typeChecks (S#tt) ((value.Str _)#tv) = typeChecks tt tv" |
  "typeChecks _ _ = False"

definition gather_events :: "log \<Rightarrow> label \<Rightarrow> numOrStr list \<Rightarrow> numOrStr list \<Rightarrow> (label \<times> value list \<times> value list) list" where
  "gather_events ls label inputTypes outputTypes = fold List.union (
     map
      (\<lambda>trace. filter (\<lambda>(label', inputs, outputs). label' = label \<and> typeChecks inputTypes inputs \<and> typeChecks outputTypes outputs)
     trace)
   ls) []"

definition is_fun :: "inputs list \<Rightarrow> inputs \<Rightarrow> nat \<Rightarrow> value list \<Rightarrow> bool" where
  "is_fun Inputs Regs numExtraRegs Output = (\<exists>f (R :: value list list). length R = length Inputs \<and> (\<forall>r \<in> set R. length r = numExtraRegs) \<and> (\<forall>(i, r, p) \<in> set (zip Inputs (zip R Output)). f i (Regs@r) = p))"

lemma "is_fun [[Num 50], [Num 100]] [] 0 [Num 50, Num 100]"
  apply (simp add: is_fun_def)
  apply (rule_tac x="\<lambda>i r. hd i" in exI)
  apply (rule_tac x="[[], []]" in exI)
  by simp

lemma "\<not>is_fun [[Num 50], [Num 50]] [] 0 [Num 50, Num 100]"
  apply (simp add: is_fun_def)
  apply clarify
  apply (case_tac R)
   apply simp
  apply (case_tac list)
  by auto

lemma "is_fun [[Num 50], [Num 50]] [] 1 [Num 50, Num 100]"
  apply (simp add: is_fun_def)
  apply (rule_tac x="\<lambda>i r. case (hd i, hd r) of (Num n, Num n') \<Rightarrow> Num (n+n')" in exI)
  apply (rule_tac x="[[Num 0], [Num 50]]" in exI)
  by simp

(*
  This gives us a minimal register assignment such that there is a deterministic function which
  produces the correct outputs given the inputs. This will be a series of calls to Z3 in the
  executable implementation.
*)
definition get_assignments :: "inputs list \<Rightarrow> inputs \<Rightarrow> value list list \<Rightarrow> inputs" where
  "get_assignments i r P = Eps (\<lambda>R. \<forall>p \<in> set P.
     \<comment> \<open>A function which takes these inputs and register values this many extra registers and
         produces the correct outputs.\<close>
    is_fun i r (length R) p \<and>
     \<comment> \<open>Make sure it's the fewest possible additional registers\<close>
    (\<nexists> r'. r' < length R \<and> is_fun i r r' p)
  )"

(*
  This gives us an aexp which, when evaluated with the inputs and registers, produces the correct
  outputs. If no such aexp exists, it returns None.
*)
definition get_aexp :: "inputs list \<Rightarrow> inputs \<Rightarrow> value list \<Rightarrow> aexp option" where
  "get_aexp i r p = (let
    aexp_pred = (\<lambda>a. \<forall>(i, p) \<in> set (zip i p). aval a (join_ir i (input2state r)) = Some p) in
    if \<exists>a. aexp_pred a then Some (Eps aexp_pred) else None
  )"

fun type_of :: "value \<Rightarrow> numOrStr" where
  "type_of (Num _) = N" |
  "type_of (value.Str _) = S"

definition exits :: "transition_matrix \<Rightarrow> transition \<Rightarrow> cfstate \<Rightarrow> bool" where
  "exits e t s = (ffilter (\<lambda>((origin, _), t'). origin = s \<and> t' = t) e \<noteq> {||})"

fun walk_up_to_choice :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> (numOrStr list \<times> numOrStr list \<times> value list) option" where
  "walk_up_to_choice _ _ _ [] _ _ _ = None" |
  "walk_up_to_choice e s r ((l, i, p)#t) s' t1 t2 = (
    let possSteps = possible_steps e s r l i in
    if s = s' \<and> l = (Label t1) \<and> exits e t1 s \<and> exits e t2 s \<and> possSteps \<noteq> {||} then
      Some (map type_of i, map type_of p, map (\<lambda>reg. case r $ reg of Some v \<Rightarrow> v) (finfun_to_list r))
    else
      let
      possibleTypes = ffilter (\<lambda>x. x \<noteq> None) (fimage (\<lambda>(dest, tr). walk_up_to_choice e dest (apply_updates (Updates tr) (join_ir i r) r) t s' t1 t2) possSteps);
      types = fimage (\<lambda>r. case r of Some (x, y, z) \<Rightarrow> (x, y)) possibleTypes;
      regs =  fimage (\<lambda>r. case r of Some (x, y, z) \<Rightarrow> z) possibleTypes
      in
      if fis_singleton types \<and> fis_singleton regs then Some (fst (fthe_elem types), snd (fthe_elem types), fthe_elem regs) else None
  )"

(*
  This gives us an aexp from a log and two transitions for a particular output
*)
definition symbolic_regression :: "log \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> cfstate \<Rightarrow> iEFSM \<Rightarrow> (aexp list \<times> value list) option" where
  "symbolic_regression log t1 t2 s new = (let
     maybe_io_types = set (map (\<lambda>p. case p of Some x \<Rightarrow> x) (filter (\<lambda>x. x \<noteq> None) (map (\<lambda>ex. walk_up_to_choice (tm new) 0 <> ex s t1 t2) log)))
     in
     if is_singleton maybe_io_types then let
        (i_types, o_types, regValues) = the_elem maybe_io_types;
        events = gather_events log (Label t1) i_types o_types;
        inputs = map (\<lambda>(label, inputs, outputs). inputs) events;
        (Outputs:: value list list) = map (\<lambda>(label, inputs, outputs). outputs) events;
        registers = get_assignments inputs regValues Outputs;
        funs = map (\<lambda>outputs. get_aexp inputs registers outputs) Outputs
       in
       if \<exists>p \<in> set funs. p = None then Some (map (\<lambda>p. case p of Some a \<Rightarrow> a) funs, registers) else None
     else
        None
   )"

(*
  This will be replaced by a call to Neil's thing to get us register update functions
*)
definition call_Neils_thing :: "iEFSM \<Rightarrow> iEFSM" where
  "call_Neils_thing i = i"

fun infer_output_functions :: "log \<Rightarrow> update_modifier" where
  "infer_output_functions log t1ID t2ID s new old _ = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID);
     orig = origin t1ID new;
     dest1 = dest t1ID new;
     dest2 = dest t2ID new;
     maxReg = total_max_reg new in
     case symbolic_regression log t1 t2 s new of
      None \<Rightarrow> None |
      Some (op, regs) \<Rightarrow>
        let newT = \<lparr>Label = Label t1, Arity = Arity t1, Guard = map (\<lambda>(r, v). Eq (V (R r)) (L v)) (enumerate maxReg regs) , Outputs = op, Updates = Updates t1\<rparr> in 
        Some ((drop_transitions new {|t1ID, t2ID|}) |\<union>| {|(t1ID, (orig, dest1), newT), (t2ID, (orig, dest2), newT)|})
   )"

end