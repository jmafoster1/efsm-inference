theory Different_Times
imports "../Inference"
begin

declare One_nat_def [simp del]
declare gval.simps [simp]
declare ValueEq_def [simp]

definition "nats2aexpregs n = image (\<lambda>r. (V (R r))) n"

definition weakly_directly_subsumes :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "weakly_directly_subsumes e1 e2 s s' t1 t2 \<equiv> (\<forall>p. accepts_trace (tm e1) p \<and> gets_us_to s (tm e1) 0 <>  p \<longrightarrow>
                                                accepts_trace (tm e2) p \<and> gets_us_to s' (tm e2) 0 <>  p \<longrightarrow>
                                                weakly_subsumes t1 (anterior_context (tm e2) p) t2 (nats2aexpregs (all_regs e2 - all_regs e1))) \<and>
                                                (\<exists>c. subsumes t1 c t2)"

definition ignore_new_register :: update_modifier where
  "ignore_new_register u\<^sub>1 u\<^sub>2 s destMerge oldEFSM = (let
     t\<^sub>1 = get_by_id destMerge u\<^sub>1;
     t\<^sub>2 = get_by_id destMerge u\<^sub>2 in
     if weakly_directly_subsumes oldEFSM destMerge (origin u\<^sub>1 oldEFSM) (origin u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1 then
       Some (replace_transition destMerge u\<^sub>1 (origin u\<^sub>1 destMerge) (dest u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2)
     else if weakly_directly_subsumes oldEFSM destMerge (origin u\<^sub>2 oldEFSM) (origin u\<^sub>2 destMerge) t\<^sub>1 t\<^sub>2 then
       Some (replace_transition destMerge u\<^sub>1 (origin u\<^sub>1 destMerge) (dest u\<^sub>1 destMerge) t\<^sub>2 t\<^sub>1)
     else None
  )"

lemma consistent_replace_true: "consistent c \<Longrightarrow> consistent (\<lambda>ra. if ra = a then {|cexp.Bc True|} else c ra)"
  apply (simp add: consistent_def)
  apply clarify
  apply (rule_tac x=s in exI)
  by (simp add: cval_true)

lemma "t2 = \<lparr>Label = Label t1, Arity = Arity t1, Guard = [], Outputs = [Plus (V (R r)) (V (I 1))], Updates=(((R r), Plus (V (R r)) (V (I 1)))#Updates t1)\<rparr> \<Longrightarrow>
       Guard t1 = [gexp.Eq (V (I 1)) (L (Num m))] \<Longrightarrow>
       Outputs t1 = [L (Num n)] \<Longrightarrow>
       Updates t1 =[] \<Longrightarrow>       
       c (V (R r)) = {|Eq (Num (n - m))|} \<Longrightarrow>
       \<forall>i. c (V (I i)) = {|Bc True|} \<Longrightarrow>
       r \<in> s \<Longrightarrow>
       weakly_subsumes t2 c t1 (nats2aexpregs s)"
proof-
  assume t2_def: "t2 = \<lparr>Label = Label t1, Arity = Arity t1, Guard = [], Outputs = [Plus (V (R r)) (V (I 1))], Updates=(((R r), Plus (V (R r)) (V (I 1)))#Updates t1)\<rparr>"
  assume guards_t1: "Guard t1 = [gexp.Eq (V (I 1)) (L (Num m))]"
  assume outputs_t1: "Outputs t1 = [L (Num n)]"
  assume updates_t1: "Updates t1 =[]"
  assume context_r: "c (V (R r)) = {|Eq (Num (n - m))|}"
  assume context_all_i: "\<forall>i. c (V (I i)) = {|Bc True|}"
  assume r_in_s: "r \<in> s"
  have enumerate_t_regs_t1: "enumerate_t_regs t1 = {}"
    by (simp add: enumerate_t_regs_def guards_t1 outputs_t1 updates_t1)
  have enumerate_t_regs_t2: "enumerate_t_regs t2 = {r}"
    by (simp add: enumerate_t_regs_def t2_def guards_t1 outputs_t1 updates_t1)
  have consistent_medial_t1: "consistent (medial c (Guard t1)) \<Longrightarrow> consistent (medial c (Guard t2))"
    apply (simp add: medial_def guards_t1 outputs_t1 updates_t1 t2_def List.maps_def pairs2context_def consistent_def)
    by auto
  show ?thesis
    apply (simp add: enumerate_t_regs_t2 enumerate_t_regs_t1 nats2aexpregs_def)
    apply (rule weak_subsumption)
         apply (simp add: t2_def guards_t1 outputs_t1 updates_t1)
        apply (simp add: t2_def medial_empty)
    using anterior_subset_medial apply blast
       apply (simp add: t2_def guards_t1 outputs_t1 updates_t1)
    using context_r
       apply clarify
    using satisfactory_registers [of c r "Num (n - m)"]
       apply fastforce
      apply (rule_tac x="[Num m]" in exI)
      apply (rule_tac x="<R r := Num (n-m)>" in exI)
      apply (simp add: guards_t1 outputs_t1 updates_t1 t2_def)
     apply (simp add: posterior_def guards_t1 outputs_t1 updates_t1 t2_def)
     apply (simp add: posterior_separate_def Let_def remove_obsolete_constraints_def r_in_s)
    apply (simp add: posterior_def posterior_separate_def Let_def consistent_medial_t1 inconsistent_false)
    apply clarify
    apply (simp add: guards_t1 outputs_t1 updates_t1 t2_def medial_empty context_r context_all_i fprod_singletons)
    using consistent_medial_gives_consistent_anterior [of c "[gexp.Eq (V (I 1)) (L (Num m))]"]
    apply (simp add: consistent_c_consistent_remove_obsolete_constraints)
    using consistent_replace_true [of c "V (R r)"]
          consistent_c_consistent_remove_obsolete_constraints [of "(\<lambda>ra. if ra = V (R r) then {|cexp.Bc True|} else c ra)"]
    by simp
qed

declare One_nat_def [simp]
declare gval.simps [simp del]
declare ValueEq_def [simp del]
end