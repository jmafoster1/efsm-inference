theory Traces
  imports EFSM
begin

type_synonym trace = "inputs list"
type_synonym observation = "outputs list"

primrec observe :: "transition_matrix \<Rightarrow> state \<Rightarrow> data \<Rightarrow> trace \<Rightarrow> observation" where
"observe _ _ _ [] = []"
| "observe M s d (i # is) = 
  (case apply_inputs M s d i of
    Stop \<Rightarrow> []
    | NonDet \<Rightarrow> []
    | Do (s',d',o') \<Rightarrow> o' # (observe M s' d' is)
  )"

(* Or definition of individual point determinism should mean that an EFSM is observably deterministic *)
lemma observable_determinism :
  fixes M
  assumes "\<forall>s . \<forall>d . \<forall>i . deterministic M s d i"
  shows "trace1 = trace2 \<longrightarrow> observe M s d trace1 = observe M s d trace2"
proof -
  show ?thesis
    by simp (*... this should not be this simple!... It ought to rely on the determinism...*)
qed

definition observably_equivilent :: "EFSM \<Rightarrow> EFSM \<Rightarrow> bool" where
"observably_equivilent E1 E2 \<equiv> 
  let (M1,s1,d1) = E1 in 
  let (M2,s2,d2) = E2 in 
  \<forall>trace . (observe M1 s1 d1 trace) = (observe M2 s2 d2 trace)"

end