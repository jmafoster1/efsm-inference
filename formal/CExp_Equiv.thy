theory CExp_Equiv
imports GExp  CExp
begin

fun cexp2gexp :: "aexp \<Rightarrow> cexp \<Rightarrow>  gexp" where
  "cexp2gexp _ (Bc b) = gexp.Bc b" |
  "cexp2gexp a Undef = Null a" |
  "cexp2gexp a (Lt v) = gexp.Gt (L v) a" |
  "cexp2gexp a (Gt v) = gexp.Gt a (L v)" |
  "cexp2gexp a (Eq v) = gexp.Eq a (L v)" |
  "cexp2gexp a (Not v) = gNot (cexp2gexp a v)" |
  "cexp2gexp a (And v va) = gAnd (cexp2gexp a v) (cexp2gexp a va)"

definition cexp_equiv :: "cexp \<Rightarrow> cexp \<Rightarrow> bool" where
  "cexp_equiv c c' \<equiv> (\<forall>r. gexp_equiv (cexp2gexp r c) (cexp2gexp r c'))"

definition valid :: "cexp \<Rightarrow> bool" where (* Is cexp "c" satisfied under all "i" values? *)
  "valid c \<equiv> (\<forall>s r. gval (cexp2gexp r c) s = Some True)"

definition satisfiable :: "cexp \<Rightarrow> bool" where (* Is there some value of "i" which satisfies "c"? *)
  "satisfiable c \<equiv> (\<exists>s r. gval (cexp2gexp r c) s = Some True)"

lemma cexp_equiv_reflexive: "cexp_equiv x x"
  by (simp add: cexp_equiv_def gexp_equiv_reflexive)

lemma vexp_equiv_valid_aux_1: "\<And>r s. (\<forall>i. cval v i = Some True) \<longrightarrow> (\<forall>r s. gval (cexp2gexp r v) s = Some True) \<Longrightarrow>
           (\<forall>i. cval va i = Some True) \<longrightarrow> (\<forall>r s. gval (cexp2gexp r va) s = Some True) \<Longrightarrow>
           \<forall>i. (case cval v i of None \<Rightarrow> None | Some a \<Rightarrow> case cval va i of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<and> b)) = Some True \<Longrightarrow>
           gval (cexp2gexp r v) s = None \<Longrightarrow> False"
proof -
fix r :: aexp and s :: "vname \<Rightarrow> value option"
assume a1: "(\<forall>i. cval v i = Some True) \<longrightarrow> (\<forall>r s. gval (cexp2gexp r v) s = Some True)"
  assume a2: "\<forall>i. (case cval v i of None \<Rightarrow> None | Some a \<Rightarrow> case cval va i of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<and> b)) = Some True"
  assume a3: "gval (cexp2gexp r v) s = None"
  obtain zz :: "value option" where
    f4: "cval v zz \<noteq> Some True \<or> (\<forall>a f. gval (cexp2gexp a v) f = Some True)"
    using a1 by blast
  have "\<not> Option.is_none (case cval v zz of None \<Rightarrow> None | Some b \<Rightarrow> case cval va zz of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<and> ba))"
    using a2 by simp
  then have f5: "cval v zz = None \<and> \<not> Option.is_none (None::bool option) \<or> cval v zz = Some (the (cval v zz)) \<and> \<not> Option.is_none (case cval va zz of None \<Rightarrow> None | Some b \<Rightarrow> Some (the (cval v zz) \<and> b))"
    by (simp add: option.split_sel_asm)
  have f6: "\<forall>z f za. if za = None then (case za of None \<Rightarrow> z::bool option | Some (x::bool) \<Rightarrow> f x) = z else (case za of None \<Rightarrow> z | Some x \<Rightarrow> f x) = f (the za)"
    by force
  then have f7: "(case cval va zz of None \<Rightarrow> None | Some b \<Rightarrow> Some (the (cval v zz) \<and> b)) \<noteq> None \<longrightarrow> (case cval va zz of None \<Rightarrow> None | Some b \<Rightarrow> Some (the (cval v zz) \<and> b)) = Some (the (cval v zz) \<and> the (cval va zz))"
    by meson
  have "(case cval va zz of None \<Rightarrow> None | Some b \<Rightarrow> Some (the (cval v zz) \<and> b)) \<noteq> None \<longrightarrow> (case cval va zz of None \<Rightarrow> None | Some b \<Rightarrow> Some (the (cval v zz) \<and> b)) = Some (the (cval v zz) \<and> the (cval va zz))"
    using f6 by meson
  then have "(case cval va zz of None \<Rightarrow> None | Some b \<Rightarrow> Some (the (cval v zz) \<and> b)) \<noteq> None \<and> \<not> the (cval v zz) \<and> cval v zz = Some (the (cval v zz)) \<longrightarrow> ((case cval v zz of None \<Rightarrow> None | Some b \<Rightarrow> case cval va zz of None \<Rightarrow> None | Some ba \<Rightarrow> Some (b \<and> ba)) = (case cval va zz of None \<Rightarrow> None | Some b \<Rightarrow> Some (the (cval v zz) \<and> b))) = (Some True = cval v zz)"
    using a2 by auto
  then have "(case cval va zz of None \<Rightarrow> None | Some b \<Rightarrow> Some (the (cval v zz) \<and> b)) = None \<or> the (cval v zz) \<or> cval v zz \<noteq> Some (the (cval v zz)) \<or> cval v zz = Some True"
    apply simp
    apply (case_tac "cval va zz")
     apply simp
    apply simp
    apply (case_tac "cval v zz")
    by simp+
  then show False
    using f5 f4 a3 a2 by auto
qed

lemma gNegate: "gexp_equiv (gNot g) (gexp.Bc True) = gexp_equiv g (gexp.Bc False)"
proof
  show "gexp_equiv (gNot g) (gexp.Bc True) \<Longrightarrow> gexp_equiv g (gexp.Bc False)"
  proof(induct g)
    case (Bc x)
    then show ?case
      by (simp add: gexp_equiv_def)
  next
    case (Eq x1a x2)
    then show ?case
      by (simp add: gexp_equiv_def)
  next
    have test: "\<And>x1a x2 s. maybe_not
              (case MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s) of None \<Rightarrow> None
               | Some a \<Rightarrow> case MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s) of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) =
             Some True \<Longrightarrow>
         MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s) = Some False"
  apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval x1a s) (aval x2 s)")
  by auto
    case (Gt x1a x2)
    then show ?case
      apply (simp add: gexp_equiv_def)
      apply clarify
      using test
      by simp
  next
    have test: "\<And>g1 s g2. maybe_not
              (case maybe_not (case gval g1 s of None \<Rightarrow> None | Some a \<Rightarrow> case gval g2 s of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) of
               None \<Rightarrow> None
               | Some a \<Rightarrow>
                   case maybe_not (case gval g1 s of None \<Rightarrow> None | Some a \<Rightarrow> case gval g2 s of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) of
                   None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) =
             Some True \<Longrightarrow>
         maybe_not (case gval g1 s of None \<Rightarrow> None | Some a \<Rightarrow> case gval g2 s of None \<Rightarrow> None | Some b \<Rightarrow> Some (a \<or> b)) = Some False"
  apply (case_tac "gval g1 s")
   apply simp+
  apply (case_tac "gval g2 s")
  by auto
    case (Nor g1 g2)
    then show ?case
      apply (simp add: gexp_equiv_def)
      apply clarify
      using test
      by simp
  next
    case (Null x)
    then show ?case
      by (simp add: gexp_equiv_def)
  qed
  show "gexp_equiv g (gexp.Bc False) \<Longrightarrow> gexp_equiv (gNot g) (gexp.Bc True)"
    by (simp add: gexp_equiv_def)
qed

lemma cexp_equiv_valid: "valid c \<longrightarrow> cexp_equiv c (Bc True)"
  by (simp add: valid_def cexp_equiv_def gexp_equiv_def)

lemma cexp_equiv_redundant_and: "cexp_equiv (and c (and c c')) (and c c')"
  apply (simp add: cexp_equiv_def gexp_equiv_def)
  apply clarify
proof(induct c rule: cexp2gexp.induct)
  case (1 uu b)
  then show ?case
    apply (cases b)
     apply simp
    apply (case_tac c')
          apply simp
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (2 a)
  then show ?case
    apply (cases c')
          apply simp
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (3 a v)
  then show ?case
    apply (cases c')
          apply simp
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval r s)")
           apply simp+
         apply (case_tac x2)
          apply simp+
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval r s)")
          apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval r s)")
         apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval r s)")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval r s)")
       apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval r s)")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some v) (aval r s)")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (4 a v)
  then show ?case
    apply (cases c')
          apply simp+
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some v)")
           apply simp+
         apply (case_tac x2)
          apply simp+
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some v)")
          apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some v)")
         apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some v)")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some v)")
       apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some v)")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
    apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some v)")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (5 a v)
  then show ?case
    apply (cases c')
          apply simp
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
case (6 a v)
  then show ?case
    apply (cases c')
          apply simp+
          apply (case_tac "gval (cexp2gexp r v) s")
           apply simp+
         apply (case_tac x2)
          apply simp+
         apply (case_tac "gval (cexp2gexp r v) s")
          apply simp+
        apply (case_tac "gval (cexp2gexp r v) s")
         apply simp+
       apply (case_tac "gval (cexp2gexp r v) s")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
      apply (case_tac "gval (cexp2gexp r v) s")
       apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp r v) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r v) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
case (7 a v va)
  then show ?case
    apply simp
    apply (cases c')
          apply simp
          apply (case_tac "gval (cexp2gexp r v) s")
           apply simp+
          apply (case_tac "gval (cexp2gexp r va) s")
           apply simp+
          apply auto[1]
         apply (case_tac x2)
          apply simp+
         apply (case_tac "gval (cexp2gexp r v) s")
          apply simp+
         apply (case_tac "gval (cexp2gexp r va) s")
          apply simp+
        apply (case_tac "gval (cexp2gexp r v) s")
         apply simp+
        apply (case_tac "gval (cexp2gexp r va) s")
         apply simp+
        apply auto[1]
       apply simp
       apply (case_tac "gval (cexp2gexp r v) s")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
        apply (case_tac "gval (cexp2gexp r va) s")
         apply simp+
       apply (case_tac "gval (cexp2gexp r va) s")
        apply simp+
       apply auto[1]
      apply simp
      apply (case_tac "gval (cexp2gexp r v) s")
       apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
       apply (case_tac "gval (cexp2gexp r va) s")
        apply simp+
      apply (case_tac "gval (cexp2gexp r va) s")
       apply simp+
      apply auto[1]
     apply simp
     apply (case_tac "gval (cexp2gexp r v) s")
    apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
      apply (case_tac "gval (cexp2gexp r va) s")
       apply simp+
     apply (case_tac "gval (cexp2gexp r va) s")
      apply simp+
     apply auto[1]
    apply simp
    apply (case_tac "gval (cexp2gexp r v) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp r va) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp r va) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r va) s")
     apply simp+
    by auto
qed

lemma and_symmetric: "cexp_equiv (and x y) (and y x)"
proof(induct x)
  case Undef
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def)
    apply clarify
    apply (case_tac y)
          apply simp
         apply (case_tac x2)
          apply simp+
        apply auto[1]
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
       apply auto[1]
      apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
     apply auto[1]
    apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (Bc x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def)
    apply (case_tac x)
     apply simp
    apply clarify
    apply (case_tac y)
          apply simp+
         apply (metis (full_types) and.simps(1) and.simps(3))
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (Eq x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def)
    apply clarify
    apply (case_tac y)
          apply auto[1]
         apply (case_tac x2)
          apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
       apply auto[1]
      apply simp
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
     apply auto[1]
    apply simp
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (Lt x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def)
    apply clarify
    apply (cases y)
          apply simp+
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval r s)")
           apply simp+
          apply auto[1]
         apply simp
         apply (case_tac x2)
          apply simp+
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval r s)")
          apply simp+
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval r s)")
         apply simp+
        apply auto[1]
       apply simp
         apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval r s)")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
         apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
       apply auto[1]
      apply simp
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval r s)")
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval r s)")
      apply simp+
      apply (case_tac "gval (cexp2gexp r x6) s")
       apply simp+
      apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
     apply auto[1]
    apply simp
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x) (aval r s)")
     apply simp+
     apply (case_tac "gval (cexp2gexp r x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x72) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (Gt x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def)
    apply clarify
    apply (cases y)
          apply simp
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x)")
           apply simp+
          apply auto[1]
         apply (case_tac x2)
          apply simp
         apply simp+
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x)")
          apply simp+
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x)")
         apply simp+
        apply auto[1]
       apply simp
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x)")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
         apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
       apply auto[1]
      apply simp
          apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x)")
       apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x)")
      apply simp+
      apply (case_tac "gval (cexp2gexp r x6) s")
       apply simp+
      apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
     apply auto[1]
    apply simp
     apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x)")
     apply simp+
     apply (case_tac "gval (cexp2gexp r x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x72) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (Not x)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def)
    apply clarify
    apply (cases y)
          apply simp
          apply (case_tac "gval (cexp2gexp r x) s")
           apply simp+
          apply auto[1]
         apply (case_tac x2)
          apply simp+
          apply (case_tac "gval (cexp2gexp r x) s")
          apply simp+
          apply (case_tac "gval (cexp2gexp r x) s")
         apply simp+
        apply auto[1]
       apply simp
          apply (case_tac "gval (cexp2gexp r x) s")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
         apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
       apply auto[1]
      apply simp
 apply (case_tac "gval (cexp2gexp r x) s")
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
        apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
 apply (case_tac "gval (cexp2gexp r x) s")
      apply simp+
      apply (case_tac "gval (cexp2gexp r x6) s")
       apply simp+
      apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
     apply auto[1]
    apply simp
 apply (case_tac "gval (cexp2gexp r x) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp r x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x72) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
next
  case (And x1 x2)
  then show ?case
    apply (simp add: cexp_equiv_def gexp_equiv_def)
    apply clarify
    apply (cases y)
          apply simp
          apply (case_tac "gval (cexp2gexp r x1) s")
           apply simp+
          apply (case_tac "gval (cexp2gexp r x2) s")
           apply simp+
          apply auto[1]
         apply (case_tac x2a)
          apply simp+
         apply (case_tac "gval (cexp2gexp r x1) s")
          apply simp+
         apply (case_tac "gval (cexp2gexp r x2) s")
          apply simp+
        apply (case_tac "gval (cexp2gexp r x1) s")
         apply simp+
         apply (case_tac "gval (cexp2gexp r x2) s")
         apply simp+
        apply auto[1]
       apply simp
       apply (case_tac "gval (cexp2gexp r x1) s")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
         apply simp+
       apply (case_tac "gval (cexp2gexp r x2) s")
        apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
         apply simp+
        apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (Some x4) (aval r s)")
        apply simp+
       apply auto[1]
      apply simp
      apply (case_tac "gval (cexp2gexp r x1) s")
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
        apply simp+
      apply (case_tac "gval (cexp2gexp r x2) s")
       apply simp+
       apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
        apply simp+
      apply (case_tac "MaybeBoolInt (\<lambda>x y. y < x) (aval r s) (Some x5)")
       apply simp+
      apply auto[1]
     apply simp
     apply (case_tac "gval (cexp2gexp r x1) s")
      apply simp+
      apply (case_tac "gval (cexp2gexp r x6) s")
       apply simp+
     apply (case_tac "gval (cexp2gexp r x2) s")
      apply simp+
      apply (case_tac "gval (cexp2gexp r x6) s")
       apply simp+
     apply (case_tac "gval (cexp2gexp r x6) s")
      apply simp+
     apply auto[1]
    apply simp
    apply (case_tac "gval (cexp2gexp r x1) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp r x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x72) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r x2) s")
     apply simp+
     apply (case_tac "gval (cexp2gexp r x71) s")
      apply simp+
     apply (case_tac "gval (cexp2gexp r x72) s")
      apply simp+
    apply (case_tac "gval (cexp2gexp r x71) s")
     apply simp+
    apply (case_tac "gval (cexp2gexp r x72) s")
    by auto
qed

lemma cexp_equiv_symmetric: "cexp_equiv x y \<Longrightarrow> cexp_equiv y x"
  by (simp add: cexp_equiv_def gexp_equiv_def)

lemma cexp_equiv_transitive: "cexp_equiv x y \<Longrightarrow> cexp_equiv y z \<Longrightarrow> cexp_equiv x z"
  by (simp add: cexp_equiv_def gexp_equiv_def)

end
