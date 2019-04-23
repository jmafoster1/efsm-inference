theory LinkedInLTL
imports EFSM_LTL

begin
abbreviation "outside \<equiv> (0::nat)"
abbreviation "loggedIn \<equiv> (1::nat)"
abbreviation "viewDetailed \<equiv> (2::nat)"
abbreviation "viewSummary \<equiv> (3::nat)"
abbreviation "pdfDetailed \<equiv> (4::nat)"
abbreviation "pdfSummary \<equiv> (5::nat)"

definition login :: transition where
"login \<equiv> \<lparr>
        Label = (STR ''login''),
        Arity = 1,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''free''))],
        Outputs = [],
        Updates = []
      \<rparr>"

definition viewFriend :: "transition" where
"viewFriend \<equiv> \<lparr>
        Label = (STR ''view''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''friendID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''HM8p''))],
        Outputs = [L (Str ''friendID''), L (Str ''name''), L (Str ''HM8p'')],
        Updates = []
      \<rparr>"

definition viewOther :: "transition" where
"viewOther \<equiv> \<lparr>
        Label = (STR ''view''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [L (Str ''otherID''), L (Str ''name''), L (Str ''4Zof'')],
        Updates = []
      \<rparr>"

definition viewOtherOON :: "transition" where
"viewOtherOON \<equiv> \<lparr>
        Label = (STR ''view''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')), gexp.Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''otherID''), L (Str ''OUT_OF_NETWORK''), L (Str ''MNn5'')],
        Updates = []
      \<rparr>"

definition viewOtherFuzz :: "transition" where
"viewOtherFuzz \<equiv> \<lparr>
        Label = (STR ''view''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''otherID''), L (Str ''name''), L (Str ''MNn5'')],
        Updates = []
      \<rparr>"

definition pdfFriend :: "transition" where
"pdfFriend \<equiv> \<lparr>
        Label = (STR ''pdf''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''friendID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''HM8p''))],
        Outputs = [L (Str ''detailedPDF'')],
        Updates = []
      \<rparr>"

definition pdfOther :: "transition" where
"pdfOther \<equiv> \<lparr>
        Label = (STR ''pdf''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''name'')), gexp.Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [L (Str ''detailedPDF'')],
        Updates = []
      \<rparr>"

definition pdfOtherOON :: "transition" where
"pdfOtherOON \<equiv> \<lparr>
        Label = (STR ''pdf''),
        Arity = 3,
        Guard = [gexp.Eq (V (I 1)) (L (Str ''otherID'')), gexp.Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')), gexp.Eq (V (I 3)) (L (Str ''MNn5''))],
        Outputs = [L (Str ''summaryPDF'')],
        Updates = []
      \<rparr>"

definition linkedIn :: transition_matrix where
"linkedIn \<equiv> {|
              ((outside,loggedIn), login),
              ((loggedIn,viewDetailed), viewFriend),
              ((loggedIn,viewDetailed), viewOther),
              ((loggedIn,viewSummary), viewOtherOON),
              ((loggedIn,viewSummary), viewOtherFuzz),
              ((viewSummary, pdfSummary), pdfOtherOON),
              ((viewSummary, pdfDetailed), pdfOther),
              ((viewDetailed, pdfDetailed), pdfFriend),
              ((viewDetailed, pdfDetailed), pdfOther)
         |}"

(*neverDetailed: THEOREM linkedIn |- G(
(label=login AND ip_1_login_1=String_free) => X(G(
(label=pdf AND ip_1_view_3=String_otherID) => X(op_1_pdf_1 /= String_detailedPDF)
)
);*)

lemma neverDetailed: 
    "(alw ((LabelEq ''login'' aand
     checkInx ip 1 ValueEq (Some (Str ''free''))) impl (nxt (alw ((LabelEq ''pdf'' aand
     checkInx ip 1 ValueEq (Some (Str ''otherID''))) impl (nxt (not (checkInx op 1 ValueEq (Some (Str ''pdfDetailed''))))))))))
     (watch linkedIn i)"
  oops

lemma labelNotAlwaysLogin: "not (alw (LabelEq ''login'')) (watch linkedIn i)"
  oops

lemma testStateEqSome: "((StateEq (Some 0)) until (StateEq (Some 1))) (watch linkedIn i)"
  oops

lemma testStateEqNone: "(ev (StateEq None)) (watch linkedIn i)"
  oops

lemma testInputEq: "((((StateEq (Some 0)) aand (LabelEq ''login'')) aand (InputEq [Str ''free''])) impl (nxt (StateEq (Some 1)))) (watch linkedIn i)" 
  oops

lemma testOutputEq: "(alw (StateEq (Some 3) aand InputEq [Str ''otherID'', Str ''OUT_OF_NETWORK'', Str ''MNn5'']) impl OutputEq [Some (Str ''summaryPDF'')]) (watch linkedIn i)"
  oops

end