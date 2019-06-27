theory Ignore_Inputs
imports "../Inference"
begin

definition enumerate_outputs :: "iEFSM \<Rightarrow> label \<Rightarrow> arity \<Rightarrow>  aexp list fset" where
  "enumerate_outputs e l a = (fimage (\<lambda>(_, _, t). Outputs t) (ffilter (\<lambda>(_, _, t). Label t = l \<and> Arity t = a) e))"

definition drop_inputs :: "update_modifier" where
  "drop_inputs t1ID t2ID s new old = (let
     t1 = (get_by_id new t1ID);
     t2 = (get_by_id new t2ID) in
     if fis_singleton (enumerate_outputs new (Label t1) (Arity t1)) then
     Some (fimage 
      (\<lambda>(id, route, t). 
       if id = t1ID then
         (id, route, \<lparr>Label = Label t, Arity = Arity t, Guard = [], Outputs = Outputs t, Updates = Updates t\<rparr>)
       else (id, route, t)) (ffilter (\<lambda>(id, _). id \<noteq> t2ID) new))
     else None
   )"

end