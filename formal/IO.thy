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

(* Stuff for making traces from simpler to type stuff... *)
definition overwrite :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a * 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" (infix "\<oplus>" 50) where
"overwrite \<equiv> \<lambda>f . \<lambda>(k,v) . \<lambda>kk . if kk = k then v else f(kk)"
declare overwrite_def[simp]

primrec make_trace_step :: "inputs \<Rightarrow> valuetype list => int \<Rightarrow> inputs" where
"make_trace_step ips [] _ = ips"
|"make_trace_step ips (i#is) n = make_trace_step (ips \<oplus> (n,Some i)) is (n+1)"

(* Make a trace (i.e. a list of input partial functions) from a list of literals *)
primrec make_trace :: "valuetype list list \<Rightarrow> trace" where
"make_trace [] = []"
|"make_trace (t#ts) = (make_trace_step blankips t 0)#(make_trace ts)"

(* Make an observation (i.e. a list of output partial functions) from a list of literals *)
primrec make_obs :: "valuetype list list \<Rightarrow> observation" where
"make_obs [] = []"
|"make_obs (t#ts) = (make_trace_step blankouts t 1)#(make_obs ts)"

end
