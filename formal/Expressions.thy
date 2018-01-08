theory Expressions
imports Main "~~/src/HOL/Analysis/Finite_Cartesian_Product"
begin

(* We don't know or care how many inputs or outputs there are but there must 
  be at least one of each, otherwise it doesn't make sense to talk about observability.
  There also has to be at least one data register 
  ... otherwise the data vector stuff implodes...*)
axiomatization inputsize :: "nat" where at_least_one_input: "inputsize > 0"
axiomatization outputsize :: "nat" where at_least_one_output: "outputsize > 0"
axiomatization datasize :: "nat" where at_least_one_register: "datasize > 0"

typedef inputindex = "{x::nat . x < inputsize}"
  apply simp
  apply (rule_tac x="0" in exI)
  apply (rule at_least_one_input)
  done
instance inputindex :: finite
  proof
    show "finite (UNIV :: inputindex set)"
      unfolding type_definition.univ[OF type_definition_inputindex]
      by auto
  qed

typedef outputindex = "{x::nat . x < outputsize}"
  apply simp
  apply (rule_tac x="0" in exI)
  apply (rule at_least_one_output)
  done
instance outputindex :: finite
  proof
    show "finite (UNIV :: outputindex set)"
      unfolding type_definition.univ[OF type_definition_outputindex]
      by auto
  qed

typedef dataindex = "{x::nat . x < datasize}"
  apply simp
  apply (rule_tac x="0" in exI)
  apply (rule at_least_one_register)
  done
instance dataindex :: finite
  proof
    show "finite (UNIV :: dataindex set)"
      unfolding type_definition.univ[OF type_definition_dataindex]
      by auto
  qed

datatype nil_or_int = Nil | I int

type_synonym inputs = "(nil_or_int ^ inputindex)"
type_synonym outputs = "(nil_or_int ^ outputindex)"
type_synonym data = "(nil_or_int ^ dataindex)"

(* General Expressions produce Ints for now *)
datatype Exp = 
  Lit int | Reg dataindex | Input inputindex
  | Plus Exp Exp | Minus Exp Exp 
  | Multiply Exp Exp | Divide Exp Exp
(* Boolean expressions produce bool evaluations *)
datatype BExp = 
  T | F 
  | Conj BExp BExp | Disj BExp BExp 
  | Not BExp
(* 'Value' expressions produce a vector. 
  They can include multiple, concurrent assignments *)
datatype 'n VExp =
  Assign 'n Exp
  | Concur "'n VExp" "'n VExp"

fun perhaps_apply :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> nil_or_int \<Rightarrow> nil_or_int \<Rightarrow> nil_or_int" where
"perhaps_apply _ Nil _ = Nil"
|"perhaps_apply _ _ Nil = Nil"
|"perhaps_apply f (I l) (I r) = I (f l r)"

primrec eval :: "data \<Rightarrow> inputs \<Rightarrow> Exp \<Rightarrow> nil_or_int" where
"eval _ _ (Lit n) = I n"
| "eval d _ (Reg n) = d$n"
| "eval _ i (Input n) = i$n"
| "eval d i (Plus l r) = perhaps_apply (\<lambda> x. \<lambda> y . x + y) (eval d i l) (eval d i r)"
| "eval d i (Minus l r) = perhaps_apply (\<lambda> x. \<lambda> y . x - y) (eval d i l) (eval d i r)"
| "eval d i (Multiply l r) = perhaps_apply (\<lambda> x. \<lambda> y . x * y) (eval d i l) (eval d i r)"
(* We have to stick to integers, so floor any remainders *)
| "eval d i (Divide l r) = perhaps_apply (\<lambda> x. \<lambda> y . floor(x / y)) (eval d i l) (eval d i r)" 

primrec beval :: "data \<Rightarrow> inputs \<Rightarrow> BExp \<Rightarrow> bool" where
"beval _ _ T = True"
|"beval _ _ F = False"
|"beval d i (Not l) = (\<not>(beval d i l))"
|"beval d i (Conj l r) = ((beval d i l) \<and> (beval d i r))"
|"beval d i (Disj l r) = ((beval d i l) \<or> (beval d i r))"

primrec veval :: "data \<Rightarrow> inputs \<Rightarrow> (nil_or_int,'n::finite) vec \<Rightarrow> 'n VExp \<Rightarrow> (nil_or_int,'n) vec" where
"veval d i v (Assign n e) = (\<chi> m . if m = n then (eval d i e) else v$m)"
(* This is doing sequential composition. The safe_concur rule is required for 
  non-overwiting, but note that they always use the anterior data state for evaluation. *)
|"veval d i v (Concur l r) = veval d i (veval d i v l) r"

(*
value "veveal 
        (\<chi> m . if m = (1::dataindex) then I 12 else Nil)
        (\<chi> m . if m = 0 then I 1 else if m = 1 then I 1 else Nil)
        (\<chi> m . Nil)
        (Assign 0 (Add (Reg 1) (Input 1)))"
*)

primrec altered_indicies :: "'n VExp \<Rightarrow> 'n list" where
"altered_indicies (Assign n _) = [n]"
|"altered_indicies (Concur l r) = (altered_indicies l) @ (altered_indicies r)"

definition safe_concur :: "'n VExp \<Rightarrow> bool" where
"safe_concur ve \<equiv> distinct (altered_indicies ve)"

end
