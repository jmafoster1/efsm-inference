theory Expressions
imports Types
begin

(* General Expressions produce Ints for now *)
datatype Exp = 
  Lit int | Reg nat | Input nat
  | Plus Exp Exp | Minus Exp Exp 
  | Multiply Exp Exp | Divide Exp Exp
(* Boolean expressions produce bool evaluations *)
datatype BExp = 
  T | F | Not BExp | Eq Exp Exp
  | Conj BExp BExp | Disj BExp BExp 
  | Lt Exp Exp | Gt Exp Exp
  | Le Exp Exp | Ge Exp Exp

(* 'Value' expressions produce a vector. 
  They can include multiple, concurrent assignments *)
datatype VExp =
  Assign nat Exp
  | Concur "VExp" "VExp"

fun perhaps_apply :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> nil_or_int \<Rightarrow> nil_or_int \<Rightarrow> nil_or_int" where
"perhaps_apply _ Nil _ = Nil"
|"perhaps_apply _ _ Nil = Nil"
|"perhaps_apply f (I l) (I r) = I (f l r)"

primrec eval :: "data \<Rightarrow> inputs \<Rightarrow> Exp \<Rightarrow> nil_or_int" where
"eval _ _ (Lit n) = I n"
| "eval d _ (Reg n) = d(n)"
| "eval _ i (Input n) = i(n)"
| "eval d i (Plus l r) = perhaps_apply (\<lambda> x. \<lambda> y . x + y) (eval d i l) (eval d i r)"
| "eval d i (Minus l r) = perhaps_apply (\<lambda> x. \<lambda> y . x - y) (eval d i l) (eval d i r)"
| "eval d i (Multiply l r) = perhaps_apply (\<lambda> x. \<lambda> y . x * y) (eval d i l) (eval d i r)"
(* We have to stick to integers, so floor any remainders *)
| "eval d i (Divide l r) = perhaps_apply (\<lambda> x. \<lambda> y . floor(x / y)) (eval d i l) (eval d i r)" 

fun perhaps_true :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> nil_or_int \<Rightarrow> nil_or_int \<Rightarrow> bool" where
"perhaps_true _ Nil _ = False"
|"perhaps_true _ _ Nil = False"
|"perhaps_true f (I l) (I r) = f l r"

primrec beval :: "data \<Rightarrow> inputs \<Rightarrow> BExp \<Rightarrow> bool" where
"beval _ _ T = True"
|"beval _ _ F = False"
|"beval d i (Not l) = (\<not>(beval d i l))"
|"beval d i (Conj l r) = ((beval d i l) \<and> (beval d i r))"
|"beval d i (Disj l r) = ((beval d i l) \<or> (beval d i r))"
|"beval d i (Lt l r) = perhaps_true (\<lambda> x . \<lambda> y . x < y) (eval d i l) (eval d i r)"
|"beval d i (Le l r) = perhaps_true (\<lambda> x . \<lambda> y . x \<le> y) (eval d i l) (eval d i r)"
|"beval d i (Gt l r) = perhaps_true (\<lambda> x . \<lambda> y . x > y) (eval d i l) (eval d i r)"
|"beval d i (Ge l r) = perhaps_true (\<lambda> x . \<lambda> y . x \<ge> y) (eval d i l) (eval d i r)"
|"beval d i (Eq l r) = perhaps_true (\<lambda> x . \<lambda> y . x = y) (eval d i l) (eval d i r)"

definition satisfiable :: "BExp \<Rightarrow> bool" where
"satisfiable x \<equiv> \<exists> R . \<exists> I . beval R I x"

primrec veval :: "data \<Rightarrow> inputs \<Rightarrow> (nat \<Rightarrow> nil_or_int) \<Rightarrow> VExp \<Rightarrow> (nat \<Rightarrow> nil_or_int)" where
"veval d i v (Assign n e) = (v \<circ> (n,(eval d i e)))"
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

primrec altered_indicies :: "VExp \<Rightarrow> nat list" where
"altered_indicies (Assign n _) = [n]"
|"altered_indicies (Concur l r) = (altered_indicies l) @ (altered_indicies r)"

definition safe_concur :: "VExp \<Rightarrow> bool" where
"safe_concur ve \<equiv> distinct (altered_indicies ve)"

end
