theory LinkedIn
imports "../EFSM" EFSM_LTL
begin
  datatype statename = outside | loggedIn | viewDetailed | pdfDetailed | viewSummary | pdfSummary

lemma UNIV_statename: "UNIV = {outside, loggedIn, viewDetailed, pdfDetailed, viewSummary, pdfSummary}"
  using statename.exhaust by auto

instance statename :: finite
  by standard (simp add: UNIV_statename)

definition login :: "transition" where
"login \<equiv> \<lparr>
        Label = ''login'',
        Arity = 1,
        Guard = [Eq (V (I 1)) (L (Str ''free''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition viewFriend :: "transition" where
"viewFriend \<equiv> \<lparr>
        Label = ''view'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''friendID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''HM8p''))],
        Outputs = [L (Str ''friendID''), L (Str ''name''), L (Str ''HM8p'')],
        Updates = []
      \<rparr>"

definition viewOther :: "transition" where
"viewOther \<equiv> \<lparr>
        Label = ''view'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [L (Str ''otherID''), L (Str ''name''), L (Str ''4Zof'')],
        Updates = []
      \<rparr>"

definition viewOtherOON :: "transition" where
"viewOtherOON \<equiv> \<lparr>
        Label = ''view'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')), Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''otherID''), L (Str ''OUT_OF_NETWORK''), L (Str ''MNn5'')],
        Updates = []
      \<rparr>"

definition viewOtherFuzz :: "transition" where
"viewOtherFuzz \<equiv> \<lparr>
        Label = ''view'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''otherID''), L (Str ''name''), L (Str ''MNn5'')],
        Updates = []
      \<rparr>"

definition pdfFriend :: "transition" where
"pdfFriend \<equiv> \<lparr>
        Label = ''pdf'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''friendID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''HM8p''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition pdfOther :: "transition" where
"pdfOther \<equiv> \<lparr>
        Label = ''pdf'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition pdfOtherOON :: "transition" where
"pdfOtherOON \<equiv> \<lparr>
        Label = ''pdf'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')), Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition linkedIn :: "statename efsm" where
"linkedIn \<equiv> \<lparr>
          s0 = outside,
          T = \<lambda> (a,b) .
              if (a,b) = (outside,loggedIn) then {login}    (* If we want to go from state 1 to state 2 then select will do that *)
              else if (a,b) = (loggedIn,viewDetailed) then {viewFriend, viewOther} (* If we want to go from state 2 to state 3 then vend will do that *)
              else if (a,b) = (loggedIn,viewSummary) then {viewOtherOON, viewOtherFuzz} (* If we want to go from state 2 to state 3 then vend will do that *)
              else if (a,b) = (viewSummary, pdfSummary) then {pdfOtherOON} (* If we want to go from state 2 to state 3 then vend will do that *)
              else if (a,b) = (viewSummary, pdfDetailed) then {pdfOther} (* If we want to go from state 2 to state 3 then vend will do that *)
              else if (a,b) = (viewDetailed, pdfDetailed) then {pdfFriend, pdfOther} (* If we want to go from state 2 to state 3 then vend will do that *)
              else {} (* There are no other transitions *)
         \<rparr>"

(*neverDetailed: THEOREM linkedIn |- G(
(label=login AND ip_1_login_1=String_free) => X(G(
(label=pdf AND ip_1_view_3=String_otherID) => X(op_1_pdf_1 /= String_detailedPDF)
)
);*)

(*record 'statename state =
  statename :: "'statename option"
  datastate :: datastate
  event :: event
  "output" :: outputs*)

definition login_free :: "statename property" where
  "login_free s \<equiv> (event (shd s) = (''login'',  [Str ''free'']))"

definition pdf_other :: "statename property" where
  "pdf_other s \<equiv> (let (label, inputs) = event (shd s) in label=''pdf'' \<and> hd inputs = Str ''otherID'')"

definition notDetailedPDF :: "statename property" where
  "notDetailedPDF s \<equiv> (hd (output (shd s)) \<noteq> Str ''detailedPDF'')"

(*      G(login_free      =>  X(   G(    pdf_other  =>  X(notDetailedPDF))))*)
lemma "(alw login_free impl   (nxt (alw (pdf_other impl (nxt notDetailedPDF))))) (watch linkedIn i)"
  apply (simp only: notDetailedPDF_def pdf_other_def login_free_def)
  sorry


end