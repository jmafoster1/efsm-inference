theory IO
  imports Types
begin

abbreviation noouts :: "outputs" where
"noouts  \<equiv> \<lambda>(ip,dt) . \<lambda>ot . None"

definition blankouts :: "outvalues" where
"blankouts \<equiv> \<lambda>x . None"
declare blankouts_def [simp]

definition blankdata :: "data" where
"blankdata \<equiv> \<lambda>x . None"
declare blankdata_def [simp]

definition noupdates :: "updates" where
"noupdates  \<equiv> \<lambda>(ip,dt) . dt"
declare noupdates_def [simp]

abbreviation trueguard :: "guard" where
"trueguard \<equiv> \<lambda>x. True"

definition blankips :: "inputs" where
"blankips \<equiv> \<lambda>x . None"
declare blankips_def [simp]

definition set_reg :: "dataname \<Rightarrow> valuetype option \<Rightarrow> data" where
"set_reg n v \<equiv> (\<lambda>k . if k = n then v else None)"

(* Stuff for making traces from simpler to type stuff... *)
definition overwrite :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option)" (infix "\<oplus>" 50) where
"overwrite \<equiv> \<lambda>f . \<lambda>g . \<lambda>kk . 
  case g(kk) of
    None \<Rightarrow> f(kk)
    | Some v \<Rightarrow> Some v"
declare overwrite_def[simp]

definition make_update :: "dataname => exp => updates" ("r _/ := _/" 50) where
"(r n := e) \<equiv> \<lambda>(dt,ip) . dt \<oplus> (set_reg n (eval (dt,ip) e))"

fun make_updates :: "updates list \<Rightarrow> updates" ("u _" 50) where
"u [] = noupdates"
| "u (a#as) = (\<lambda>(dt,ip) . ((u as)(dt,ip)) \<oplus> (a(dt,ip)))"

value "((u [r 1 := (Lit (In 1)), r 2 := (Lit (In 4))])(blankdata,blankips))(1)"

lemma overwriting:
  fixes n
  shows "u [r n := v, r n := vv] \<equiv> r n := vv"
  apply (simp only: make_updates.simps)

lemma noupdates_left_id : "u [noupdates, x] \<equiv> u [x]"
  

primrec make_trace_step :: "inputs \<Rightarrow> valuetype list => int \<Rightarrow> inputs" where
"make_trace_step ips [] _ = ips"
|"make_trace_step ips (i#is) n = make_trace_step (ips \<oplus> (n,Some i)) is (n+1)"

(* Make a trace (i.e. a list of input partial functions) from a list of literals *)
primrec make_trace :: "(label \<times> valuetype list) list \<Rightarrow> trace" where
"make_trace [] = []"
|"make_trace (t#ts) = (fst t, (make_trace_step blankips (snd t) 1))#(make_trace ts)"

(* Make an observation (i.e. a list of output partial functions) from a list of literals *)
primrec make_obs :: "valuetype list list \<Rightarrow> observation" where
"make_obs [] = []"
|"make_obs (t#ts) = (make_trace_step blankouts t 1)#(make_obs ts)"

end
