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
        Outputs = [L (Str ''detailedPDF'')],
        Updates = []
      \<rparr>"

definition pdfOther :: "transition" where
"pdfOther \<equiv> \<lparr>
        Label = ''pdf'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''name'')), Eq (V (I 3)) (L (Str ''4Zof''))],
        Outputs = [L (Str ''detailedPDF'')],
        Updates = []
      \<rparr>"

definition pdfOtherOON :: "transition" where
"pdfOtherOON \<equiv> \<lparr>
        Label = ''pdf'',
        Arity = 3,
        Guard = [Eq (V (I 1)) (L (Str ''otherID'')), Eq (V (I 2)) (L (Str ''OUT_OF_NETWORK'')), Eq (V (I 3)) (L (Str ''MNn5''))],
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

definition login_free :: "property" where
  "login_free s \<equiv> (event (shd s) = (''login'',  [Str ''free'']))"

definition pdf_other :: "property" where
  "pdf_other s \<equiv> (let (label, inputs) = event (shd s) in label=''pdf'' \<and> hd inputs = Str ''otherID'')"

definition notDetailedPDF :: "property" where
  "notDetailedPDF s \<equiv> (hd (output (shd s)) \<noteq> Some (Str ''detailedPDF''))"

(*      G(login_free      =>  X(   G(    pdf_other  =>  X(notDetailedPDF))))*)
lemma neverDetailed: "(alw (LabelEq ''login'' aand InputEq 1 (Str ''free'') ) impl (nxt (alw ((LabelEq ''pdf'' aand InputEq 1 (Str ''otherID'')) impl (nxt (not (OutputEq 1 (Some (Str ''pdfDetailed''))))))))) 
     (watch linkedIn i)"
  oops

end