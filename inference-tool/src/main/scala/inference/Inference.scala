object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
  implicit def
    `Transition.equal_transition_ext`[A : equal, B : equal]:
      equal[Transition.transition_ext[A, B]]
    = new equal[Transition.transition_ext[A, B]] {
    val `HOL.equal` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition.equal_transition_exta[A, B](a, b)
  }
  implicit def
    `PTA_Generalisation.equal_value_type`: equal[PTA_Generalisation.value_type]
    = new equal[PTA_Generalisation.value_type] {
    val `HOL.equal` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.equal_value_typea(a, b)
  }
  implicit def
    `Inference.equal_score_ext`[A : equal]: equal[Inference.score_ext[A]] = new
    equal[Inference.score_ext[A]] {
    val `HOL.equal` = (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.equal_score_exta[A](a, b)
  }
  implicit def `Store_Reuse.equal_ioTag`: equal[Store_Reuse.ioTag] = new
    equal[Store_Reuse.ioTag] {
    val `HOL.equal` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.equal_ioTaga(a, b)
  }
  implicit def `Product_Type.equal_unit`: equal[Unit] = new equal[Unit] {
    val `HOL.equal` = (a: Unit, b: Unit) => Product_Type.equal_unita(a, b)
  }
  implicit def `Product_Type.equal_prod`[A : equal, B : equal]: equal[(A, B)] =
    new equal[(A, B)] {
    val `HOL.equal` = (a: (A, B), b: (A, B)) =>
      Product_Type.equal_proda[A, B](a, b)
  }
  implicit def `String.equal_literal`: equal[String] = new equal[String] {
    val `HOL.equal` = (a: String, b: String) => a == b
  }
  implicit def `Optiona.equal_option`[A : equal]: equal[Option[A]] = new
    equal[Option[A]] {
    val `HOL.equal` = (a: Option[A], b: Option[A]) =>
      Optiona.equal_optiona[A](a, b)
  }
  implicit def `Value.equal_value`: equal[Value.value] = new equal[Value.value]
    {
    val `HOL.equal` = (a: Value.value, b: Value.value) =>
      Value.equal_valuea(a, b)
  }
  implicit def `VName.equal_vname`: equal[VName.vname] = new equal[VName.vname]
    {
    val `HOL.equal` = (a: VName.vname, b: VName.vname) =>
      VName.equal_vnamea(a, b)
  }
  implicit def `Lista.equal_list`[A : equal]: equal[List[A]] = new
    equal[List[A]] {
    val `HOL.equal` = (a: List[A], b: List[A]) => Lista.equal_lista[A](a, b)
  }
  implicit def `GExp.equal_gexp`[A : equal, B : equal]: equal[GExp.gexp[A, B]] =
    new equal[GExp.gexp[A, B]] {
    val `HOL.equal` = (a: GExp.gexp[A, B], b: GExp.gexp[A, B]) =>
      GExp.equal_gexpa[A, B](a, b)
  }
  implicit def `FSet.equal_fset`[A : equal]: equal[FSet.fset[A]] = new
    equal[FSet.fset[A]] {
    val `HOL.equal` = (a: FSet.fset[A], b: FSet.fset[A]) =>
      FSet.equal_fseta[A](a, b)
  }
  implicit def `AExp.equal_aexp`[A : equal, B : equal]: equal[AExp.aexp[A, B]] =
    new equal[AExp.aexp[A, B]] {
    val `HOL.equal` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp.equal_aexpa[A, B](a, b)
  }
  implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
    val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Fun {

def id[A]: A => A = ((x: A) => x)

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

def fun_upd[A : HOL.equal, B](f: A => B, a: A, b: B): A => B =
  ((x: A) => (if (HOL.eq[A](x, a)) b else f(x)))

} /* object Fun */

object Orderings {

trait ord[A] {
  val `Orderings.less_eq`: (A, A) => Boolean
  val `Orderings.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Orderings.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)
object ord {
  implicit def
    `Transition_Lexorder.ord_transition_ext`[A : HOL.equal : linorder,
      B : HOL.equal : linorder]:
      ord[Transition.transition_ext[A, B]]
    = new ord[Transition.transition_ext[A, B]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition_Lexorder.less_eq_transition_ext[A, B](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition_Lexorder.less_transition_ext[A, B](a, b)
  }
  implicit def
    `PTA_Generalisation.ord_value_type`: ord[PTA_Generalisation.value_type] =
    new ord[PTA_Generalisation.value_type] {
    val `Orderings.less_eq` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.less_eq_value_type(a, b)
    val `Orderings.less` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.less_value_type(a, b)
  }
  implicit def
    `Inference.ord_score_ext`[A : HOL.equal : linorder]:
      ord[Inference.score_ext[A]]
    = new ord[Inference.score_ext[A]] {
    val `Orderings.less_eq` =
      (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.less_eq_score_ext[A](a, b)
    val `Orderings.less` =
      (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.less_score_ext[A](a, b)
  }
  implicit def `Code_Numeral.ord_integer`: ord[BigInt] = new ord[BigInt] {
    val `Orderings.less_eq` = (a: BigInt, b: BigInt) => a <= b
    val `Orderings.less` = (a: BigInt, b: BigInt) => a < b
  }
  implicit def `Store_Reuse.ord_ioTag`: ord[Store_Reuse.ioTag] = new
    ord[Store_Reuse.ioTag] {
    val `Orderings.less_eq` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.less_eq_ioTag(a, b)
    val `Orderings.less` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.less_ioTag(a, b)
  }
  implicit def `Product_Type.ord_unit`: ord[Unit] = new ord[Unit] {
    val `Orderings.less_eq` = (a: Unit, b: Unit) =>
      Product_Type.less_eq_unit(a, b)
    val `Orderings.less` = (a: Unit, b: Unit) => Product_Type.less_unit(a, b)
  }
  implicit def `Product_Lexorder.ord_prod`[A : ord, B : ord]: ord[(A, B)] = new
    ord[(A, B)] {
    val `Orderings.less_eq` = (a: (A, B), b: (A, B)) =>
      Product_Lexorder.less_eq_prod[A, B](a, b)
    val `Orderings.less` = (a: (A, B), b: (A, B)) =>
      Product_Lexorder.less_prod[A, B](a, b)
  }
  implicit def `String.ord_literal`: ord[String] = new ord[String] {
    val `Orderings.less_eq` = (a: String, b: String) => a <= b
    val `Orderings.less` = (a: String, b: String) => a < b
  }
  implicit def `Option_ord.ord_option`[A : preorder]: ord[Option[A]] = new
    ord[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_option[A](a, b)
  }
  implicit def `Value_Lexorder.ord_value`: ord[Value.value] = new
    ord[Value.value] {
    val `Orderings.less_eq` = (a: Value.value, b: Value.value) =>
      Value_Lexorder.less_eq_value(a, b)
    val `Orderings.less` = (a: Value.value, b: Value.value) =>
      Value_Lexorder.less_value(a, b)
  }
  implicit def `VName.ord_vname`: ord[VName.vname] = new ord[VName.vname] {
    val `Orderings.less_eq` = (a: VName.vname, b: VName.vname) =>
      VName.less_eq_vname(a, b)
    val `Orderings.less` = (a: VName.vname, b: VName.vname) =>
      VName.less_vname(a, b)
  }
  implicit def `List_Lexorder.ord_list`[A : HOL.equal : order]: ord[List[A]] =
    new ord[List[A]] {
    val `Orderings.less_eq` = (a: List[A], b: List[A]) =>
      List_Lexorder.less_eq_list[A](a, b)
    val `Orderings.less` = (a: List[A], b: List[A]) =>
      List_Lexorder.less_list[A](a, b)
  }
  implicit def
    `GExp_Lexorder.ord_gexp`[A : HOL.equal : linorder,
                              B : HOL.equal : linorder]:
      ord[GExp.gexp[A, B]]
    = new ord[GExp.gexp[A, B]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A, B], b: GExp.gexp[A, B]) =>
      GExp_Lexorder.less_eq_gexp[A, B](a, b)
    val `Orderings.less` = (a: GExp.gexp[A, B], b: GExp.gexp[A, B]) =>
      GExp_Lexorder.less_gexp[A, B](a, b)
  }
  implicit def
    `AExp_Lexorder.ord_aexp`[A : HOL.equal : linorder,
                              B : HOL.equal : linorder]:
      ord[AExp.aexp[A, B]]
    = new ord[AExp.aexp[A, B]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp_Lexorder.less_eq_aexp[A, B](a, b)
    val `Orderings.less` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp_Lexorder.less_aexp[A, B](a, b)
  }
  implicit def `Nat.ord_nat`: ord[Nat.nat] = new ord[Nat.nat] {
    val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) => Nat.less_eq_nat(a, b)
    val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
  }
  implicit def `Int.ord_int`: ord[Int.int] = new ord[Int.int] {
    val `Orderings.less_eq` = (a: Int.int, b: Int.int) => Int.less_eq_int(a, b)
    val `Orderings.less` = (a: Int.int, b: Int.int) => Int.less_int(a, b)
  }
}

trait preorder[A] extends ord[A] {
}
object preorder {
  implicit def
    `Transition_Lexorder.preorder_transition_ext`[A : HOL.equal : linorder,
           B : HOL.equal : linorder]:
      preorder[Transition.transition_ext[A, B]]
    = new preorder[Transition.transition_ext[A, B]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition_Lexorder.less_eq_transition_ext[A, B](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition_Lexorder.less_transition_ext[A, B](a, b)
  }
  implicit def
    `PTA_Generalisation.preorder_value_type`:
      preorder[PTA_Generalisation.value_type]
    = new preorder[PTA_Generalisation.value_type] {
    val `Orderings.less_eq` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.less_eq_value_type(a, b)
    val `Orderings.less` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.less_value_type(a, b)
  }
  implicit def
    `Inference.preorder_score_ext`[A : HOL.equal : linorder]:
      preorder[Inference.score_ext[A]]
    = new preorder[Inference.score_ext[A]] {
    val `Orderings.less_eq` =
      (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.less_eq_score_ext[A](a, b)
    val `Orderings.less` =
      (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.less_score_ext[A](a, b)
  }
  implicit def `Store_Reuse.preorder_ioTag`: preorder[Store_Reuse.ioTag] = new
    preorder[Store_Reuse.ioTag] {
    val `Orderings.less_eq` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.less_eq_ioTag(a, b)
    val `Orderings.less` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.less_ioTag(a, b)
  }
  implicit def `Product_Type.preorder_unit`: preorder[Unit] = new preorder[Unit]
    {
    val `Orderings.less_eq` = (a: Unit, b: Unit) =>
      Product_Type.less_eq_unit(a, b)
    val `Orderings.less` = (a: Unit, b: Unit) => Product_Type.less_unit(a, b)
  }
  implicit def
    `Product_Lexorder.preorder_prod`[A : preorder, B : preorder]:
      preorder[(A, B)]
    = new preorder[(A, B)] {
    val `Orderings.less_eq` = (a: (A, B), b: (A, B)) =>
      Product_Lexorder.less_eq_prod[A, B](a, b)
    val `Orderings.less` = (a: (A, B), b: (A, B)) =>
      Product_Lexorder.less_prod[A, B](a, b)
  }
  implicit def `String.preorder_literal`: preorder[String] = new
    preorder[String] {
    val `Orderings.less_eq` = (a: String, b: String) => a <= b
    val `Orderings.less` = (a: String, b: String) => a < b
  }
  implicit def `Option_ord.preorder_option`[A : preorder]: preorder[Option[A]] =
    new preorder[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_option[A](a, b)
  }
  implicit def `Value_Lexorder.preorder_value`: preorder[Value.value] = new
    preorder[Value.value] {
    val `Orderings.less_eq` = (a: Value.value, b: Value.value) =>
      Value_Lexorder.less_eq_value(a, b)
    val `Orderings.less` = (a: Value.value, b: Value.value) =>
      Value_Lexorder.less_value(a, b)
  }
  implicit def `VName.preorder_vname`: preorder[VName.vname] = new
    preorder[VName.vname] {
    val `Orderings.less_eq` = (a: VName.vname, b: VName.vname) =>
      VName.less_eq_vname(a, b)
    val `Orderings.less` = (a: VName.vname, b: VName.vname) =>
      VName.less_vname(a, b)
  }
  implicit def
    `List_Lexorder.preorder_list`[A : HOL.equal : order]: preorder[List[A]] =
    new preorder[List[A]] {
    val `Orderings.less_eq` = (a: List[A], b: List[A]) =>
      List_Lexorder.less_eq_list[A](a, b)
    val `Orderings.less` = (a: List[A], b: List[A]) =>
      List_Lexorder.less_list[A](a, b)
  }
  implicit def
    `GExp_Lexorder.preorder_gexp`[A : HOL.equal : linorder,
                                   B : HOL.equal : linorder]:
      preorder[GExp.gexp[A, B]]
    = new preorder[GExp.gexp[A, B]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A, B], b: GExp.gexp[A, B]) =>
      GExp_Lexorder.less_eq_gexp[A, B](a, b)
    val `Orderings.less` = (a: GExp.gexp[A, B], b: GExp.gexp[A, B]) =>
      GExp_Lexorder.less_gexp[A, B](a, b)
  }
  implicit def
    `AExp_Lexorder.preorder_aexp`[A : HOL.equal : linorder,
                                   B : HOL.equal : linorder]:
      preorder[AExp.aexp[A, B]]
    = new preorder[AExp.aexp[A, B]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp_Lexorder.less_eq_aexp[A, B](a, b)
    val `Orderings.less` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp_Lexorder.less_aexp[A, B](a, b)
  }
  implicit def `Nat.preorder_nat`: preorder[Nat.nat] = new preorder[Nat.nat] {
    val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) => Nat.less_eq_nat(a, b)
    val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
  }
  implicit def `Int.preorder_int`: preorder[Int.int] = new preorder[Int.int] {
    val `Orderings.less_eq` = (a: Int.int, b: Int.int) => Int.less_eq_int(a, b)
    val `Orderings.less` = (a: Int.int, b: Int.int) => Int.less_int(a, b)
  }
}

trait order[A] extends preorder[A] {
}
object order {
  implicit def
    `Transition_Lexorder.order_transition_ext`[A : HOL.equal : linorder,
        B : HOL.equal : linorder]:
      order[Transition.transition_ext[A, B]]
    = new order[Transition.transition_ext[A, B]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition_Lexorder.less_eq_transition_ext[A, B](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition_Lexorder.less_transition_ext[A, B](a, b)
  }
  implicit def
    `PTA_Generalisation.order_value_type`: order[PTA_Generalisation.value_type]
    = new order[PTA_Generalisation.value_type] {
    val `Orderings.less_eq` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.less_eq_value_type(a, b)
    val `Orderings.less` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.less_value_type(a, b)
  }
  implicit def
    `Inference.order_score_ext`[A : HOL.equal : linorder]:
      order[Inference.score_ext[A]]
    = new order[Inference.score_ext[A]] {
    val `Orderings.less_eq` =
      (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.less_eq_score_ext[A](a, b)
    val `Orderings.less` =
      (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.less_score_ext[A](a, b)
  }
  implicit def `Store_Reuse.order_ioTag`: order[Store_Reuse.ioTag] = new
    order[Store_Reuse.ioTag] {
    val `Orderings.less_eq` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.less_eq_ioTag(a, b)
    val `Orderings.less` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.less_ioTag(a, b)
  }
  implicit def `Product_Type.order_unit`: order[Unit] = new order[Unit] {
    val `Orderings.less_eq` = (a: Unit, b: Unit) =>
      Product_Type.less_eq_unit(a, b)
    val `Orderings.less` = (a: Unit, b: Unit) => Product_Type.less_unit(a, b)
  }
  implicit def
    `Product_Lexorder.order_prod`[A : order, B : order]: order[(A, B)] = new
    order[(A, B)] {
    val `Orderings.less_eq` = (a: (A, B), b: (A, B)) =>
      Product_Lexorder.less_eq_prod[A, B](a, b)
    val `Orderings.less` = (a: (A, B), b: (A, B)) =>
      Product_Lexorder.less_prod[A, B](a, b)
  }
  implicit def `String.order_literal`: order[String] = new order[String] {
    val `Orderings.less_eq` = (a: String, b: String) => a <= b
    val `Orderings.less` = (a: String, b: String) => a < b
  }
  implicit def `Option_ord.order_option`[A : order]: order[Option[A]] = new
    order[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_option[A](a, b)
  }
  implicit def `Value_Lexorder.order_value`: order[Value.value] = new
    order[Value.value] {
    val `Orderings.less_eq` = (a: Value.value, b: Value.value) =>
      Value_Lexorder.less_eq_value(a, b)
    val `Orderings.less` = (a: Value.value, b: Value.value) =>
      Value_Lexorder.less_value(a, b)
  }
  implicit def `VName.order_vname`: order[VName.vname] = new order[VName.vname]
    {
    val `Orderings.less_eq` = (a: VName.vname, b: VName.vname) =>
      VName.less_eq_vname(a, b)
    val `Orderings.less` = (a: VName.vname, b: VName.vname) =>
      VName.less_vname(a, b)
  }
  implicit def `List_Lexorder.order_list`[A : HOL.equal : order]: order[List[A]]
    = new order[List[A]] {
    val `Orderings.less_eq` = (a: List[A], b: List[A]) =>
      List_Lexorder.less_eq_list[A](a, b)
    val `Orderings.less` = (a: List[A], b: List[A]) =>
      List_Lexorder.less_list[A](a, b)
  }
  implicit def
    `GExp_Lexorder.order_gexp`[A : HOL.equal : linorder,
                                B : HOL.equal : linorder]:
      order[GExp.gexp[A, B]]
    = new order[GExp.gexp[A, B]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A, B], b: GExp.gexp[A, B]) =>
      GExp_Lexorder.less_eq_gexp[A, B](a, b)
    val `Orderings.less` = (a: GExp.gexp[A, B], b: GExp.gexp[A, B]) =>
      GExp_Lexorder.less_gexp[A, B](a, b)
  }
  implicit def
    `AExp_Lexorder.order_aexp`[A : HOL.equal : linorder,
                                B : HOL.equal : linorder]:
      order[AExp.aexp[A, B]]
    = new order[AExp.aexp[A, B]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp_Lexorder.less_eq_aexp[A, B](a, b)
    val `Orderings.less` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp_Lexorder.less_aexp[A, B](a, b)
  }
  implicit def `Nat.order_nat`: order[Nat.nat] = new order[Nat.nat] {
    val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) => Nat.less_eq_nat(a, b)
    val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
  }
  implicit def `Int.order_int`: order[Int.int] = new order[Int.int] {
    val `Orderings.less_eq` = (a: Int.int, b: Int.int) => Int.less_eq_int(a, b)
    val `Orderings.less` = (a: Int.int, b: Int.int) => Int.less_int(a, b)
  }
}

trait linorder[A] extends order[A] {
}
object linorder {
  implicit def
    `Transition_Lexorder.linorder_transition_ext`[A : HOL.equal : linorder,
           B : HOL.equal : linorder]:
      linorder[Transition.transition_ext[A, B]]
    = new linorder[Transition.transition_ext[A, B]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition_Lexorder.less_eq_transition_ext[A, B](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A, B], b: Transition.transition_ext[A, B])
      => Transition_Lexorder.less_transition_ext[A, B](a, b)
  }
  implicit def
    `PTA_Generalisation.linorder_value_type`:
      linorder[PTA_Generalisation.value_type]
    = new linorder[PTA_Generalisation.value_type] {
    val `Orderings.less_eq` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.less_eq_value_type(a, b)
    val `Orderings.less` =
      (a: PTA_Generalisation.value_type, b: PTA_Generalisation.value_type) =>
      PTA_Generalisation.less_value_type(a, b)
  }
  implicit def
    `Inference.linorder_score_ext`[A : HOL.equal : linorder]:
      linorder[Inference.score_ext[A]]
    = new linorder[Inference.score_ext[A]] {
    val `Orderings.less_eq` =
      (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.less_eq_score_ext[A](a, b)
    val `Orderings.less` =
      (a: Inference.score_ext[A], b: Inference.score_ext[A]) =>
      Inference.less_score_ext[A](a, b)
  }
  implicit def `Store_Reuse.linorder_ioTag`: linorder[Store_Reuse.ioTag] = new
    linorder[Store_Reuse.ioTag] {
    val `Orderings.less_eq` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.less_eq_ioTag(a, b)
    val `Orderings.less` = (a: Store_Reuse.ioTag, b: Store_Reuse.ioTag) =>
      Store_Reuse.less_ioTag(a, b)
  }
  implicit def `Product_Type.linorder_unit`: linorder[Unit] = new linorder[Unit]
    {
    val `Orderings.less_eq` = (a: Unit, b: Unit) =>
      Product_Type.less_eq_unit(a, b)
    val `Orderings.less` = (a: Unit, b: Unit) => Product_Type.less_unit(a, b)
  }
  implicit def
    `Product_Lexorder.linorder_prod`[A : linorder, B : linorder]:
      linorder[(A, B)]
    = new linorder[(A, B)] {
    val `Orderings.less_eq` = (a: (A, B), b: (A, B)) =>
      Product_Lexorder.less_eq_prod[A, B](a, b)
    val `Orderings.less` = (a: (A, B), b: (A, B)) =>
      Product_Lexorder.less_prod[A, B](a, b)
  }
  implicit def `String.linorder_literal`: linorder[String] = new
    linorder[String] {
    val `Orderings.less_eq` = (a: String, b: String) => a <= b
    val `Orderings.less` = (a: String, b: String) => a < b
  }
  implicit def `Option_ord.linorder_option`[A : linorder]: linorder[Option[A]] =
    new linorder[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_option[A](a, b)
  }
  implicit def `Value_Lexorder.linorder_value`: linorder[Value.value] = new
    linorder[Value.value] {
    val `Orderings.less_eq` = (a: Value.value, b: Value.value) =>
      Value_Lexorder.less_eq_value(a, b)
    val `Orderings.less` = (a: Value.value, b: Value.value) =>
      Value_Lexorder.less_value(a, b)
  }
  implicit def `VName.linorder_vname`: linorder[VName.vname] = new
    linorder[VName.vname] {
    val `Orderings.less_eq` = (a: VName.vname, b: VName.vname) =>
      VName.less_eq_vname(a, b)
    val `Orderings.less` = (a: VName.vname, b: VName.vname) =>
      VName.less_vname(a, b)
  }
  implicit def
    `List_Lexorder.linorder_list`[A : HOL.equal : linorder]: linorder[List[A]] =
    new linorder[List[A]] {
    val `Orderings.less_eq` = (a: List[A], b: List[A]) =>
      List_Lexorder.less_eq_list[A](a, b)
    val `Orderings.less` = (a: List[A], b: List[A]) =>
      List_Lexorder.less_list[A](a, b)
  }
  implicit def
    `AExp_Lexorder.linorder_aexp`[A : HOL.equal : linorder,
                                   B : HOL.equal : linorder]:
      linorder[AExp.aexp[A, B]]
    = new linorder[AExp.aexp[A, B]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp_Lexorder.less_eq_aexp[A, B](a, b)
    val `Orderings.less` = (a: AExp.aexp[A, B], b: AExp.aexp[A, B]) =>
      AExp_Lexorder.less_aexp[A, B](a, b)
  }
  implicit def `Nat.linorder_nat`: linorder[Nat.nat] = new linorder[Nat.nat] {
    val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) => Nat.less_eq_nat(a, b)
    val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
  }
  implicit def `Int.linorder_int`: linorder[Int.int] = new linorder[Int.int] {
    val `Orderings.less_eq` = (a: Int.int, b: Int.int) => Int.less_eq_int(a, b)
    val `Orderings.less` = (a: Int.int, b: Int.int) => Int.less_int(a, b)
  }
}

trait bot[A] {
  val `Orderings.bot`: A
}
def bot[A](implicit A: bot[A]): A = A.`Orderings.bot`
object bot {
  implicit def `Option_ord.bot_option`[A : order]: bot[Option[A]] = new
    bot[Option[A]] {
    val `Orderings.bot` = Option_ord.bot_optiona[A]
  }
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def min[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) a else b)

def less_bool(x0: Boolean, b: Boolean): Boolean = (x0, b) match {
  case (true, b) => false
  case (false, b) => b
}

} /* object Orderings */

object Groups {

trait plus[A] {
  val `Groups.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Groups.plus`(a, b)
object plus {
  implicit def `Nat.plus_nat`: plus[Nat.nat] = new plus[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add {
  implicit def `Nat.semigroup_add_nat`: semigroup_add[Nat.nat] = new
    semigroup_add[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait zero[A] {
  val `Groups.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`Groups.zero`
object zero {
  implicit def `Nat.zero_nat`: zero[Nat.nat] = new zero[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add {
  implicit def `Nat.monoid_add_nat`: monoid_add[Nat.nat] = new
    monoid_add[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}
object ab_semigroup_add {
  implicit def `Nat.ab_semigroup_add_nat`: ab_semigroup_add[Nat.nat] = new
    ab_semigroup_add[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}
object comm_monoid_add {
  implicit def `Nat.comm_monoid_add_nat`: comm_monoid_add[Nat.nat] = new
    comm_monoid_add[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

} /* object Groups */

object Nat {

abstract sealed class nat
final case class Nata(a: BigInt) extends nat

def equal_nata(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) == Code_Numeral.integer_of_nat(n)

def plus_nata(m: nat, n: nat): nat =
  Nata(Code_Numeral.integer_of_nat(m) + Code_Numeral.integer_of_nat(n))

def zero_nata: nat = Nata(BigInt(0))

def less_eq_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) <= Code_Numeral.integer_of_nat(n)

def less_nat(m: nat, n: nat): Boolean =
  Code_Numeral.integer_of_nat(m) < Code_Numeral.integer_of_nat(n)

def Suc(n: nat): nat = plus_nata(n, Nat.Nata((1)))

def minus_nat(m: nat, n: nat): nat =
  Nata(Orderings.max[BigInt](BigInt(0),
                              Code_Numeral.integer_of_nat(m) -
                                Code_Numeral.integer_of_nat(n)))

} /* object Nat */

object Code_Numeral {

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

def nat_of_integer(k: BigInt): Nat.nat =
  Nat.Nata(Orderings.max[BigInt](BigInt(0), k))

def integer_of_int(x0: Int.int): BigInt = x0 match {
  case Int.int_of_integer(k) => k
}

} /* object Code_Numeral */

object Int {

abstract sealed class int
final case class int_of_integer(a: BigInt) extends int

def less_eq_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) <= Code_Numeral.integer_of_int(l)

def less_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) < Code_Numeral.integer_of_int(l)

def zero_int: int = int_of_integer(BigInt(0))

def equal_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

} /* object Int */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

} /* object Num */

object Code_Target_List {

def upt_tailrec(i: Nat.nat, j: Nat.nat, l: List[Nat.nat]): List[Nat.nat] =
  (if (Nat.equal_nata(j, Nat.zero_nata)) l
    else (if (Nat.less_eq_nat(i, Nat.minus_nat(j, Nat.Nata((1)))))
           upt_tailrec(i, Nat.minus_nat(j, Nat.Nata((1))),
                        List(Nat.minus_nat(j, Nat.Nata((1)))) ++ l)
           else l))

} /* object Code_Target_List */

object Lista {

def list_all[A](f: A => Boolean, l: List[A]): Boolean = l.par.forall(f)

def equal_lista[A : HOL.equal](xs: List[A], ys: List[A]): Boolean =
  (Nat.equal_nata(Nat.Nata(xs.par.length),
                   Nat.Nata(ys.par.length))) && (list_all[(A,
                    A)](((a: (A, A)) => {
  val (aa, b): (A, A) = a;
  HOL.eq[A](aa, b)
}),
                         xs.par.zip(ys).toList))

def upt(i: Nat.nat, j: Nat.nat): List[Nat.nat] =
  Code_Target_List.upt_tailrec(i, j, Nil)

def drop[A](n: Nat.nat, x1: List[A]): List[A] = (n, x1) match {
  case (n, Nil) => Nil
  case (n, x :: xs) =>
    (if (Nat.equal_nata(n, Nat.zero_nata)) x :: xs
      else drop[A](Nat.minus_nat(n, Nat.Nata((1))), xs))
}

def fold[A, B](f: A => B => B, xs: List[A], s: B): B =
  Dirties.foldl[B, A](((x: B) => (sa: A) => (f(sa))(x)), s, xs)

def maps[A, B](f: A => List[B], l: List[A]): List[B] = l.par.flatMap(f).toList

def foldr[A, B](f: A => B => B, xs: List[A], a: B): B =
  Dirties.foldl[B, A](((x: B) => (y: A) => (f(y))(x)), a, xs.par.reverse.toList)

def insert[A](x: A, xs: List[A]): List[A] =
  (if (xs.contains(x)) xs else x :: xs)

def union[A]: (List[A]) => (List[A]) => List[A] =
  ((a: List[A]) => (b: List[A]) =>
    fold[A, List[A]](((aa: A) => (ba: List[A]) => insert[A](aa, ba)), a, b))

def filter[A](l: A => Boolean, f: List[A]): List[A] = f.par.filter(l).toList

def list_ex[A](f: A => Boolean, l: List[A]): Boolean = l.par.exists(f)

def map[A, B](f: A => B, l: List[A]): List[B] = l.par.map(f).toList

def product[A, B](xs: List[A], ys: List[B]): List[(A, B)] =
  maps[A, (A, B)](((x: A) => map[B, (A, B)](((a: B) => (x, a)), ys)), xs)

def subseqs[A](x0: List[A]): List[List[A]] = x0 match {
  case Nil => List(Nil)
  case x :: xs => {
                    val xss: List[List[A]] = subseqs[A](xs);
                    map[List[A], List[A]](((a: List[A]) => x :: a), xss) ++ xss
                  }
}

def enumerate[A](n: Nat.nat, xs: List[A]): List[(Nat.nat, A)] =
  (upt(n, Nat.plus_nata(n, Nat.Nata(xs.par.length)))).par.zip(xs).toList

def takeWhile[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: takeWhile[A](p, xs) else Nil)
}

def transpose[A](x0: List[List[A]]): List[List[A]] = x0 match {
  case Nil => Nil
  case Nil :: xss => transpose[A](xss)
  case (x :: xs) :: xss =>
    (x :: maps[List[A],
                A](((a: List[A]) => (a match {
                                       case Nil => Nil
                                       case h :: _ => List(h)
                                     })),
                    xss)) ::
      transpose[A](xs :: maps[List[A],
                               List[A]](((a: List[A]) =>
  (a match {
     case Nil => Nil
     case _ :: t => List(t)
   })),
 xss))
}

def list_update[A](x0: List[A], i: Nat.nat, y: A): List[A] = (x0, i, y) match {
  case (Nil, i, y) => Nil
  case (x :: xs, i, y) =>
    (if (Nat.equal_nata(i, Nat.zero_nata)) y :: xs
      else x :: list_update[A](xs, Nat.minus_nat(i, Nat.Nata((1))), y))
}

def map_tailrec_rev[A, B](f: A => B, x1: List[A], bs: List[B]): List[B] =
  (f, x1, bs) match {
  case (f, Nil, bs) => bs
  case (f, a :: as, bs) => map_tailrec_rev[A, B](f, as, f(a) :: bs)
}

def map_tailrec[A, B](f: A => B, as: List[A]): List[B] =
  (map_tailrec_rev[A, B](f, as, Nil)).par.reverse.toList

def product_lists[A](x0: List[List[A]]): List[List[A]] = x0 match {
  case Nil => List(Nil)
  case xs :: xss =>
    maps[A, List[A]](((x: A) =>
                       map[List[A],
                            List[A]](((a: List[A]) => x :: a),
                                      product_lists[A](xss))),
                      xs)
}

def insort_key[A, B : Orderings.linorder](f: A => B, x: A, xa2: List[A]):
      List[A]
  =
  (f, x, xa2) match {
  case (f, x, Nil) => List(x)
  case (f, x, y :: ys) =>
    (if (Orderings.less_eq[B](f(x), f(y))) x :: y :: ys
      else y :: insort_key[A, B](f, x, ys))
}

def sort_key[A, B : Orderings.linorder](f: A => B, xs: List[A]): List[A] =
  foldr[A, List[A]](((a: A) => (b: List[A]) => insort_key[A, B](f, a, b)), xs,
                     Nil)

def sorted_list_of_set[A : Orderings.linorder](x0: Set.set[A]): List[A] = x0
  match {
  case Set.seta(l) => (l.par.distinct.toList).sortWith((Orderings.less))
}

} /* object Lista */

object Product_Type {

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => (HOL.eq[A](x1, y1)) && (HOL.eq[B](x2, y2))
}

def equal_unita(u: Unit, v: Unit): Boolean = true

def less_eq_unit(uu: Unit, uv: Unit): Boolean = true

def less_unit(uu: Unit, uv: Unit): Boolean = false

def product[A, B](x0: Set.set[A], x1: Set.set[B]): Set.set[(A, B)] = (x0, x1)
  match {
  case (Set.seta(xs), Set.seta(ys)) =>
    Set.seta[(A, B)](Lista.maps[A, (A, B)](((x: A) =>
     Lista.map[B, (A, B)](((a: B) => (x, a)), ys)),
    xs))
}

} /* object Product_Type */

object Set {

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]

def Ball[A](x0: set[A], p: A => Boolean): Boolean = (x0, p) match {
  case (seta(xs), p) => Lista.list_all[A](p, xs)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](Lista.map[A, B](f, xs))
}

def filter[A](p: A => Boolean, x1: set[A]): set[A] = (p, x1) match {
  case (p, seta(xs)) => seta[A](Lista.filter[A](p, xs))
}

def insert[A](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, seta(s)) => (if (s.contains(x)) seta[A](s) else seta[A](x :: s))
}

def member[A](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, seta(xs)) => xs.contains(x)
}

def is_empty[A](x0: set[A]): Boolean = x0 match {
  case seta(xs) => xs.isEmpty
}

def bot_set[A]: set[A] = seta[A](Nil)

def inf_set[A](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, seta(xs)) =>
    seta[A](Lista.filter[A](((x: A) => member[A](x, a)), xs))
}

def sup_set[A](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (seta(x), seta(y)) => seta[A](x ++ y)
  case (seta(xs), a) =>
    Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => insert[A](aa, b)), xs, a)
}

def less_eq_set[A](a: set[A], b: set[A]): Boolean =
  Ball[A](a, ((x: A) => member[A](x, b)))

def equal_set[A : HOL.equal](a: set[A], b: set[A]): Boolean =
  (less_eq_set[A](a, b)) && (less_eq_set[A](b, a))

} /* object Set */

object Optiona {

def equal_optiona[A : HOL.equal](x0: Option[A], x1: Option[A]): Boolean =
  (x0, x1) match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => HOL.eq[A](x2, y2)
  case (None, None) => true
}

def is_none[A](x0: Option[A]): Boolean = x0 match {
  case Some(x) => false
  case None => true
}

def the[A](x0: Option[A]): A = x0 match {
  case Some(x2) => x2
}

} /* object Optiona */

object Trilean {

abstract sealed class trilean
final case class truea() extends trilean
final case class falsea() extends trilean
final case class invalid() extends trilean

def maybe_not(x0: trilean): trilean = x0 match {
  case truea() => falsea()
  case falsea() => truea()
  case invalid() => invalid()
}

def plus_trilean(x0: trilean, uu: trilean): trilean = (x0, uu) match {
  case (invalid(), uu) => invalid()
  case (truea(), invalid()) => invalid()
  case (falsea(), invalid()) => invalid()
  case (truea(), truea()) => truea()
  case (truea(), falsea()) => truea()
  case (falsea(), truea()) => truea()
  case (falsea(), falsea()) => falsea()
}

def equal_trilean(x0: trilean, x1: trilean): Boolean = (x0, x1) match {
  case (falsea(), invalid()) => false
  case (invalid(), falsea()) => false
  case (truea(), invalid()) => false
  case (invalid(), truea()) => false
  case (truea(), falsea()) => false
  case (falsea(), truea()) => false
  case (invalid(), invalid()) => true
  case (falsea(), falsea()) => true
  case (truea(), truea()) => true
}

} /* object Trilean */

object Value {

abstract sealed class value
final case class Numa(a: Int.int) extends value
final case class Str(a: String) extends value

def equal_valuea(x0: value, x1: value): Boolean = (x0, x1) match {
  case (Numa(x1), Str(x2)) => false
  case (Str(x2), Numa(x1)) => false
  case (Str(x2), Str(y2)) => x2 == y2
  case (Numa(x1), Numa(y1)) => Int.equal_int(x1, y1)
}

trait aexp_value[A] {
  val `Value.plus`: (Option[A], Option[A]) => Option[A]
  val `Value.minus`: (Option[A], Option[A]) => Option[A]
  val `Value.times`: (Option[A], Option[A]) => Option[A]
  val `Value.gt`: (Option[A], Option[A]) => Trilean.trilean
  val `Value.is_num`: A => Boolean
  val `Value.get_num`: A => Int.int
}
def plus[A](a: Option[A], b: Option[A])(implicit A: aexp_value[A]): Option[A] =
  A.`Value.plus`(a, b)
def minus[A](a: Option[A], b: Option[A])(implicit A: aexp_value[A]): Option[A] =
  A.`Value.minus`(a, b)
def times[A](a: Option[A], b: Option[A])(implicit A: aexp_value[A]): Option[A] =
  A.`Value.times`(a, b)
def gt[A](a: Option[A], b: Option[A])(implicit A: aexp_value[A]):
      Trilean.trilean
  = A.`Value.gt`(a, b)
def is_num[A](a: A)(implicit A: aexp_value[A]): Boolean = A.`Value.is_num`(a)
def get_num[A](a: A)(implicit A: aexp_value[A]): Int.int = A.`Value.get_num`(a)
object aexp_value {
}

def value_eq[A : HOL.equal : aexp_value](a: Option[A], b: Option[A]):
      Trilean.trilean
  =
  (if (Optiona.equal_optiona[A](a, b)) Trilean.truea() else Trilean.falsea())

} /* object Value */

object VName {

abstract sealed class vname
final case class I(a: Nat.nat) extends vname
final case class R(a: Nat.nat) extends vname

def equal_vnamea(x0: vname, x1: vname): Boolean = (x0, x1) match {
  case (I(x1), R(x2)) => false
  case (R(x2), I(x1)) => false
  case (R(x2), R(y2)) => Nat.equal_nata(x2, y2)
  case (I(x1), I(y1)) => Nat.equal_nata(x1, y1)
}

def less_vname(x0: vname, x1: vname): Boolean = (x0, x1) match {
  case (I(n1), R(n2)) => true
  case (R(n1), I(n2)) => false
  case (I(n1), I(n2)) => Nat.less_nat(n1, n2)
  case (R(n1), R(n2)) => Nat.less_nat(n1, n2)
}

def less_eq_vname(v1: vname, v2: vname): Boolean =
  (less_vname(v1, v2)) || (equal_vnamea(v1, v2))

} /* object VName */

object AExp {

abstract sealed class aexp[A, B]
final case class L[B, A](a: B) extends aexp[A, B]
final case class V[A, B](a: A) extends aexp[A, B]
final case class Plus[A, B](a: aexp[A, B], b: aexp[A, B]) extends aexp[A, B]
final case class Minus[A, B](a: aexp[A, B], b: aexp[A, B]) extends aexp[A, B]
final case class Times[A, B](a: aexp[A, B], b: aexp[A, B]) extends aexp[A, B]

def equal_aexpa[A : HOL.equal, B : HOL.equal](x0: aexp[A, B], x1: aexp[A, B]):
      Boolean
  =
  (x0, x1) match {
  case (Minus(x41, x42), Times(x51, x52)) => false
  case (Times(x51, x52), Minus(x41, x42)) => false
  case (Plus(x31, x32), Times(x51, x52)) => false
  case (Times(x51, x52), Plus(x31, x32)) => false
  case (Plus(x31, x32), Minus(x41, x42)) => false
  case (Minus(x41, x42), Plus(x31, x32)) => false
  case (V(x2), Times(x51, x52)) => false
  case (Times(x51, x52), V(x2)) => false
  case (V(x2), Minus(x41, x42)) => false
  case (Minus(x41, x42), V(x2)) => false
  case (V(x2), Plus(x31, x32)) => false
  case (Plus(x31, x32), V(x2)) => false
  case (L(x1), Times(x51, x52)) => false
  case (Times(x51, x52), L(x1)) => false
  case (L(x1), Minus(x41, x42)) => false
  case (Minus(x41, x42), L(x1)) => false
  case (L(x1), Plus(x31, x32)) => false
  case (Plus(x31, x32), L(x1)) => false
  case (L(x1), V(x2)) => false
  case (V(x2), L(x1)) => false
  case (Times(x51, x52), Times(y51, y52)) =>
    (equal_aexpa[A, B](x51, y51)) && (equal_aexpa[A, B](x52, y52))
  case (Minus(x41, x42), Minus(y41, y42)) =>
    (equal_aexpa[A, B](x41, y41)) && (equal_aexpa[A, B](x42, y42))
  case (Plus(x31, x32), Plus(y31, y32)) =>
    (equal_aexpa[A, B](x31, y31)) && (equal_aexpa[A, B](x32, y32))
  case (V(x2), V(y2)) => HOL.eq[A](x2, y2)
  case (L(x1), L(y1)) => HOL.eq[B](x1, y1)
}

def aval[A, B : Value.aexp_value](x0: aexp[A, B], s: A => Option[B]): Option[B]
  =
  (x0, s) match {
  case (L(x), s) => Some[B](x)
  case (V(x), s) => s(x)
  case (Plus(a_1, a_2), s) =>
    Value.plus[B](aval[A, B](a_1, s), aval[A, B](a_2, s))
  case (Minus(a_1, a_2), s) =>
    Value.minus[B](aval[A, B](a_1, s), aval[A, B](a_2, s))
  case (Times(a_1, a_2), s) =>
    Value.times[B](aval[A, B](a_1, s), aval[A, B](a_2, s))
}

def is_lit[A, B](x0: aexp[A, B]): Boolean = x0 match {
  case L(uu) => true
  case V(v) => false
  case Plus(v, va) => false
  case Minus(v, va) => false
  case Times(v, va) => false
}

def input2state[A : HOL.equal](n: List[A]): Map[Nat.nat, Option[A]] =
  Lista.fold[(Nat.nat, A),
              Map[Nat.nat, Option[A]]](((a: (Nat.nat, A)) =>
 {
   val (k, v): (Nat.nat, A) = a;
   ((f: Map[Nat.nat, Option[A]]) => f + (k -> (Some[A](v))))
 }),
Lista.enumerate[A](Nat.zero_nata, n),
scala.collection.immutable.Map().withDefaultValue(None))

def join_ir[A : HOL.equal](i: List[A], r: Map[Nat.nat, Option[A]]):
      VName.vname => Option[A]
  =
  ((a: VName.vname) => (a match {
                          case VName.I(aa) => (input2state[A](i))(aa)
                          case VName.R(aa) => r(aa)
                        }))

def null_state[A, B : Orderings.bot]: Map[A, B] =
  scala.collection.immutable.Map().withDefaultValue(Orderings.bot[B])

def rename_regs[A](uu: Nat.nat => Nat.nat, x1: aexp[VName.vname, A]):
      aexp[VName.vname, A]
  =
  (uu, x1) match {
  case (uu, L(l)) => L[A, VName.vname](l)
  case (f, V(VName.R(r))) => V[VName.vname, A](VName.R(f(r)))
  case (uv, V(VName.I(va))) => V[VName.vname, A](VName.I(va))
  case (f, Plus(a, b)) =>
    Plus[VName.vname, A](rename_regs[A](f, a), rename_regs[A](f, b))
  case (f, Minus(a, b)) =>
    Minus[VName.vname, A](rename_regs[A](f, a), rename_regs[A](f, b))
  case (f, Times(a, b)) =>
    Times[VName.vname, A](rename_regs[A](f, a), rename_regs[A](f, b))
}

def enumerate_regs[A](x0: aexp[VName.vname, A]): Set.set[Nat.nat] = x0 match {
  case L(uu) => Set.bot_set[Nat.nat]
  case V(VName.R(n)) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case V(VName.I(uv)) => Set.bot_set[Nat.nat]
  case Plus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_regs[A](v), enumerate_regs[A](va))
  case Minus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_regs[A](v), enumerate_regs[A](va))
  case Times(v, va) =>
    Set.sup_set[Nat.nat](enumerate_regs[A](v), enumerate_regs[A](va))
}

def enumerate_aexp_inputs[A](x0: aexp[VName.vname, A]): Set.set[Nat.nat] = x0
  match {
  case L(uu) => Set.bot_set[Nat.nat]
  case V(VName.I(n)) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case V(VName.R(n)) => Set.bot_set[Nat.nat]
  case Plus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs[A](v),
                          enumerate_aexp_inputs[A](va))
  case Minus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs[A](v),
                          enumerate_aexp_inputs[A](va))
  case Times(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs[A](v),
                          enumerate_aexp_inputs[A](va))
}

def enumerate_vars[A](a: aexp[VName.vname, A]): Set.set[VName.vname] =
  Set.sup_set[VName.vname](Set.image[Nat.nat,
                                      VName.vname](((aa: Nat.nat) =>
             VName.I(aa)),
            enumerate_aexp_inputs[A](a)),
                            Set.image[Nat.nat,
                                       VName.vname](((aa: Nat.nat) =>
              VName.R(aa)),
             enumerate_regs[A](a)))

def aexp_constrains[A : HOL.equal,
                     B : HOL.equal](x0: aexp[A, B], a: aexp[A, B]):
      Boolean
  =
  (x0, a) match {
  case (L(l), a) => equal_aexpa[A, B](L[B, A](l), a)
  case (V(va), v) => equal_aexpa[A, B](V[A, B](va), v)
  case (Plus(a1, a2), v) =>
    (equal_aexpa[A, B](Plus[A, B](a1, a2),
                        v)) || ((equal_aexpa[A,
      B](Plus[A, B](a1, a2),
          v)) || ((aexp_constrains[A, B](a1,
  v)) || (aexp_constrains[A, B](a2, v))))
  case (Minus(a1, a2), v) =>
    (equal_aexpa[A, B](Minus[A, B](a1, a2),
                        v)) || ((aexp_constrains[A,
          B](a1, v)) || (aexp_constrains[A, B](a2, v)))
  case (Times(a1, a2), v) =>
    (equal_aexpa[A, B](Times[A, B](a1, a2),
                        v)) || ((aexp_constrains[A,
          B](a1, v)) || (aexp_constrains[A, B](a2, v)))
}

def enumerate_aexp_ints[A, B : Value.aexp_value](x0: aexp[A, B]):
      Set.set[Int.int]
  =
  x0 match {
  case L(v) =>
    (if (Value.is_num[B](v))
      Set.insert[Int.int](Value.get_num[B](v), Set.bot_set[Int.int])
      else Set.bot_set[Int.int])
  case V(uu) => Set.bot_set[Int.int]
  case Plus(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A, B](a1),
                          enumerate_aexp_ints[A, B](a2))
  case Minus(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A, B](a1),
                          enumerate_aexp_ints[A, B](a2))
  case Times(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A, B](a1),
                          enumerate_aexp_ints[A, B](a2))
}

} /* object AExp */

object Complete_Lattices {

def Sup_set[A](x0: Set.set[Set.set[A]]): Set.set[A] = x0 match {
  case Set.seta(xs) =>
    Lista.fold[Set.set[A],
                Set.set[A]](((a: Set.set[A]) => (b: Set.set[A]) =>
                              Set.sup_set[A](a, b)),
                             xs, Set.bot_set[A])
}

} /* object Complete_Lattices */

object Code_Target_Nat {

def int_of_nat(n: Nat.nat): Int.int =
  Int.int_of_integer(Code_Numeral.integer_of_nat(n))

} /* object Code_Target_Nat */

object Lattices_Big {

def Max[A : Orderings.linorder](x0: Set.set[A]): A = x0 match {
  case Set.seta(x :: xs) =>
    Lista.fold[A, A](((a: A) => (b: A) => Orderings.max[A](a, b)), xs, x)
}

def Min[A : Orderings.linorder](x0: Set.set[A]): A = x0 match {
  case Set.seta(x :: xs) =>
    Lista.fold[A, A](((a: A) => (b: A) => Orderings.min[A](a, b)), xs, x)
}

} /* object Lattices_Big */

object Phantom_Type {

abstract sealed class phantom[A, B]
final case class phantoma[B, A](a: B) extends phantom[A, B]

} /* object Phantom_Type */

object Cardinality {

def finite_UNIV_nata: Phantom_Type.phantom[Nat.nat, Boolean] =
  Phantom_Type.phantoma[Boolean, Nat.nat](false)

def card_UNIV_nata: Phantom_Type.phantom[Nat.nat, Nat.nat] =
  Phantom_Type.phantoma[Nat.nat, Nat.nat](Nat.zero_nata)

trait finite_UNIV[A] {
  val `Cardinality.finite_UNIV`: Phantom_Type.phantom[A, Boolean]
}
def finite_UNIV[A](implicit A: finite_UNIV[A]): Phantom_Type.phantom[A, Boolean]
  = A.`Cardinality.finite_UNIV`
object finite_UNIV {
  implicit def `Cardinality.finite_UNIV_nat`: finite_UNIV[Nat.nat] = new
    finite_UNIV[Nat.nat] {
    val `Cardinality.finite_UNIV` = finite_UNIV_nata
  }
}

trait card_UNIV[A] extends finite_UNIV[A] {
  val `Cardinality.card_UNIV`: Phantom_Type.phantom[A, Nat.nat]
}
def card_UNIV[A](implicit A: card_UNIV[A]): Phantom_Type.phantom[A, Nat.nat] =
  A.`Cardinality.card_UNIV`
object card_UNIV {
  implicit def `Cardinality.card_UNIV_nat`: card_UNIV[Nat.nat] = new
    card_UNIV[Nat.nat] {
    val `Cardinality.card_UNIV` = card_UNIV_nata
    val `Cardinality.finite_UNIV` = finite_UNIV_nata
  }
}

def eq_set[A : card_UNIV](x0: Set.set[A], x1: Set.set[A]): Boolean = (x0, x1)
  match {
  case (Set.seta(xs), Set.seta(ys)) =>
    (Lista.list_all[A](((a: A) => ys.contains(a)),
                        xs)) && (Lista.list_all[A](((a: A) => xs.contains(a)),
            ys))
}

def subset[A : card_UNIV](x0: Set.set[A], x1: Set.set[A]): Boolean = (x0, x1)
  match {
  case (Set.seta(l1), Set.seta(l2)) =>
    Lista.list_all[A](((a: A) => l2.contains(a)), l1)
}

} /* object Cardinality */

object GExp {

abstract sealed class gexp[A, B]
final case class Bc[A, B](a: Boolean) extends gexp[A, B]
final case class Eq[A, B](a: AExp.aexp[A, B], b: AExp.aexp[A, B]) extends
  gexp[A, B]
final case class Gt[A, B](a: AExp.aexp[A, B], b: AExp.aexp[A, B]) extends
  gexp[A, B]
final case class In[A, B](a: A, b: List[B]) extends gexp[A, B]
final case class Nor[A, B](a: gexp[A, B], b: gexp[A, B]) extends gexp[A, B]

def equal_gexpa[A : HOL.equal, B : HOL.equal](x0: gexp[A, B], x1: gexp[A, B]):
      Boolean
  =
  (x0, x1) match {
  case (In(x41, x42), Nor(x51, x52)) => false
  case (Nor(x51, x52), In(x41, x42)) => false
  case (Gt(x31, x32), Nor(x51, x52)) => false
  case (Nor(x51, x52), Gt(x31, x32)) => false
  case (Gt(x31, x32), In(x41, x42)) => false
  case (In(x41, x42), Gt(x31, x32)) => false
  case (Eq(x21, x22), Nor(x51, x52)) => false
  case (Nor(x51, x52), Eq(x21, x22)) => false
  case (Eq(x21, x22), In(x41, x42)) => false
  case (In(x41, x42), Eq(x21, x22)) => false
  case (Eq(x21, x22), Gt(x31, x32)) => false
  case (Gt(x31, x32), Eq(x21, x22)) => false
  case (Bc(x1), Nor(x51, x52)) => false
  case (Nor(x51, x52), Bc(x1)) => false
  case (Bc(x1), In(x41, x42)) => false
  case (In(x41, x42), Bc(x1)) => false
  case (Bc(x1), Gt(x31, x32)) => false
  case (Gt(x31, x32), Bc(x1)) => false
  case (Bc(x1), Eq(x21, x22)) => false
  case (Eq(x21, x22), Bc(x1)) => false
  case (Nor(x51, x52), Nor(y51, y52)) =>
    (equal_gexpa[A, B](x51, y51)) && (equal_gexpa[A, B](x52, y52))
  case (In(x41, x42), In(y41, y42)) =>
    (HOL.eq[A](x41, y41)) && (Lista.equal_lista[B](x42, y42))
  case (Gt(x31, x32), Gt(y31, y32)) =>
    (AExp.equal_aexpa[A, B](x31, y31)) && (AExp.equal_aexpa[A, B](x32, y32))
  case (Eq(x21, x22), Eq(y21, y22)) =>
    (AExp.equal_aexpa[A, B](x21, y21)) && (AExp.equal_aexpa[A, B](x22, y22))
  case (Bc(x1), Bc(y1)) => x1 == y1
}

def gNot[A, B](g: gexp[A, B]): gexp[A, B] = Nor[A, B](g, g)

def Lt[A, B](a: AExp.aexp[A, B], b: AExp.aexp[A, B]): gexp[A, B] =
  Gt[A, B](b, a)

def Ge[A, B](v: AExp.aexp[A, B], va: AExp.aexp[A, B]): gexp[A, B] =
  gNot[A, B](Lt[A, B](v, va))

def Le[A, B](v: AExp.aexp[A, B], va: AExp.aexp[A, B]): gexp[A, B] =
  gNot[A, B](Gt[A, B](v, va))

def Ne[A, B](v: AExp.aexp[A, B], va: AExp.aexp[A, B]): gexp[A, B] =
  gNot[A, B](Eq[A, B](v, va))

def gOr[A, B](v: gexp[A, B], va: gexp[A, B]): gexp[A, B] =
  Nor[A, B](Nor[A, B](v, va), Nor[A, B](v, va))

def gAnd[A, B](v: gexp[A, B], va: gexp[A, B]): gexp[A, B] =
  Nor[A, B](Nor[A, B](v, v), Nor[A, B](va, va))

def gval[A, B : HOL.equal : Value.aexp_value](x0: gexp[A, B],
       uu: A => Option[B]):
      Trilean.trilean
  =
  (x0, uu) match {
  case (Bc(true), uu) => Trilean.truea()
  case (Bc(false), uv) => Trilean.falsea()
  case (Gt(a_1, a_2), s) =>
    Value.gt[B](AExp.aval[A, B](a_1, s), AExp.aval[A, B](a_2, s))
  case (Eq(a_1, a_2), s) =>
    Value.value_eq[B](AExp.aval[A, B](a_1, s), AExp.aval[A, B](a_2, s))
  case (In(v, l), s) =>
    (if ((Lista.map[B, Option[B]](((a: B) => Some[B](a)), l)).contains(s(v)))
      Trilean.truea() else Trilean.falsea())
  case (Nor(a_1, a_2), s) =>
    Trilean.maybe_not(Trilean.plus_trilean(gval[A, B](a_1, s),
    gval[A, B](a_2, s)))
}

def fold_In[A, B](uu: A, x1: List[B]): gexp[A, B] = (uu, x1) match {
  case (uu, Nil) => Bc[A, B](false)
  case (v, List(l)) => Eq[A, B](AExp.V[A, B](v), AExp.L[B, A](l))
  case (v, l :: va :: vb) =>
    Lista.fold[B, gexp[A, B]](Fun.comp[gexp[A, B], (gexp[A, B]) => gexp[A, B],
B](((a: gexp[A, B]) => (b: gexp[A, B]) => gOr[A, B](a, b)),
    ((x: B) => Eq[A, B](AExp.V[A, B](v), AExp.L[B, A](x)))),
                               va :: vb,
                               Eq[A, B](AExp.V[A, B](v), AExp.L[B, A](l)))
}

def rename_regs[A](uu: Nat.nat => Nat.nat, x1: gexp[VName.vname, A]):
      gexp[VName.vname, A]
  =
  (uu, x1) match {
  case (uu, Bc(b)) => Bc[VName.vname, A](b)
  case (f, Eq(a1, a2)) =>
    Eq[VName.vname, A](AExp.rename_regs[A](f, a1), AExp.rename_regs[A](f, a2))
  case (f, Gt(a1, a2)) =>
    Gt[VName.vname, A](AExp.rename_regs[A](f, a1), AExp.rename_regs[A](f, a2))
  case (f, In(VName.R(r), vs)) => In[VName.vname, A](VName.R(f(r)), vs)
  case (f, In(VName.I(va), vs)) => In[VName.vname, A](VName.I(va), vs)
  case (f, Nor(g1, g2)) =>
    Nor[VName.vname, A](rename_regs[A](f, g1), rename_regs[A](f, g2))
}

def apply_guards[A : HOL.equal : Value.aexp_value](g:
             List[gexp[VName.vname, A]],
            s: VName.vname => Option[A]):
      Boolean
  =
  Lista.list_all[Trilean.trilean](((ga: Trilean.trilean) =>
                                    Trilean.equal_trilean(ga, Trilean.truea())),
                                   Lista.map[gexp[VName.vname, A],
      Trilean.trilean](((ga: gexp[VName.vname, A]) =>
                         gval[VName.vname, A](ga, s)),
                        g))

def enumerate_regs[A](x0: gexp[VName.vname, A]): Set.set[Nat.nat] = x0 match {
  case Bc(uu) => Set.bot_set[Nat.nat]
  case Eq(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_regs[A](v), AExp.enumerate_regs[A](va))
  case Gt(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_regs[A](v), AExp.enumerate_regs[A](va))
  case In(VName.I(uv), va) => Set.bot_set[Nat.nat]
  case In(VName.R(n), va) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case Nor(v, va) =>
    Set.sup_set[Nat.nat](enumerate_regs[A](v), enumerate_regs[A](va))
}

def enumerate_gexp_inputs[A](x0: gexp[VName.vname, A]): Set.set[Nat.nat] = x0
  match {
  case Bc(uu) => Set.bot_set[Nat.nat]
  case Eq(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_inputs[A](v),
                          AExp.enumerate_aexp_inputs[A](va))
  case Gt(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_inputs[A](v),
                          AExp.enumerate_aexp_inputs[A](va))
  case In(VName.R(uv), va) => Set.bot_set[Nat.nat]
  case In(VName.I(n), va) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case Nor(v, va) =>
    Set.sup_set[Nat.nat](enumerate_gexp_inputs[A](v),
                          enumerate_gexp_inputs[A](va))
}

def enumerate_vars[A](g: gexp[VName.vname, A]): List[VName.vname] =
  Lista.sorted_list_of_set[VName.vname](Set.sup_set[VName.vname](Set.image[Nat.nat,
                                    VName.vname](((a: Nat.nat) => VName.R(a)),
          enumerate_regs[A](g)),
                          Set.image[Nat.nat,
                                     VName.vname](((a: Nat.nat) => VName.I(a)),
           enumerate_gexp_inputs[A](g))))

def gexp_constrains[A : HOL.equal,
                     B : HOL.equal](x0: gexp[A, B], uv: AExp.aexp[A, B]):
      Boolean
  =
  (x0, uv) match {
  case (Bc(uu), uv) => false
  case (Eq(a1, a2), a) =>
    (AExp.aexp_constrains[A, B](a1, a)) || (AExp.aexp_constrains[A, B](a2, a))
  case (Gt(a1, a2), a) =>
    (AExp.aexp_constrains[A, B](a1, a)) || (AExp.aexp_constrains[A, B](a2, a))
  case (Nor(g1, g2), a) =>
    (gexp_constrains[A, B](g1, a)) || (gexp_constrains[A, B](g2, a))
  case (In(v, l), a) => AExp.aexp_constrains[A, B](AExp.V[A, B](v), a)
}

def enumerate_gexp_ints[A, B : Value.aexp_value](x0: gexp[A, B]):
      Set.set[Int.int]
  =
  x0 match {
  case Bc(uu) => Set.bot_set[Int.int]
  case Eq(a1, a2) =>
    Set.sup_set[Int.int](AExp.enumerate_aexp_ints[A, B](a1),
                          AExp.enumerate_aexp_ints[A, B](a2))
  case Gt(a1, a2) =>
    Set.sup_set[Int.int](AExp.enumerate_aexp_ints[A, B](a1),
                          AExp.enumerate_aexp_ints[A, B](a2))
  case In(v, l) =>
    Lista.fold[B, Set.set[Int.int]](((x: B) => (acc: Set.set[Int.int]) =>
                                      (if (Value.is_num[B](x))
Set.insert[Int.int](Value.get_num[B](x), acc) else acc)),
                                     l, Set.bot_set[Int.int])
  case Nor(g1, g2) =>
    Set.sup_set[Int.int](enumerate_gexp_ints[A, B](g1),
                          enumerate_gexp_ints[A, B](g2))
}

} /* object GExp */

object Transition {

abstract sealed class transition_ext[A, B]
final case class
  transition_exta[A, B](a: String, b: Nat.nat,
                         c: List[GExp.gexp[VName.vname, A]],
                         d: List[AExp.aexp[VName.vname, A]],
                         e: List[(Nat.nat, AExp.aexp[VName.vname, A])], f: B)
  extends transition_ext[A, B]

def equal_transition_exta[A : HOL.equal,
                           B : HOL.equal](x0: transition_ext[A, B],
   x1: transition_ext[A, B]):
      Boolean
  =
  (x0, x1) match {
  case (transition_exta(labela, aritya, guardsa, outputsa, updatesa, morea),
         transition_exta(label, arity, guards, outputs, updates, more))
    => (labela ==
         label) && ((Nat.equal_nata(aritya,
                                     arity)) && ((Lista.equal_lista[GExp.gexp[VName.vname,
                                       A]](guardsa,
    guards)) && ((Lista.equal_lista[AExp.aexp[VName.vname,
       A]](outputsa,
            outputs)) && ((Lista.equal_lista[(Nat.nat,
       AExp.aexp[VName.vname,
                  A])](updatesa, updates)) && (HOL.eq[B](morea, more))))))
}

def Updates[A, B](x0: transition_ext[A, B]):
      List[(Nat.nat, AExp.aexp[VName.vname, A])]
  =
  x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => updates
}

def Outputs[A, B](x0: transition_ext[A, B]): List[AExp.aexp[VName.vname, A]] =
  x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => outputs
}

def Guards[A, B](x0: transition_ext[A, B]): List[GExp.gexp[VName.vname, A]] = x0
  match {
  case transition_exta(label, arity, guards, outputs, updates, more) => guards
}

def enumerate_regs[A](t: transition_ext[A, Unit]): Set.set[Nat.nat] =
  Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[GExp.gexp[VName.vname,
                            A],
                  Set.set[Nat.nat]](((a: GExp.gexp[VName.vname, A]) =>
                                      GExp.enumerate_regs[A](a)),
                                     Guards[A, Unit](t)))),
                          Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[AExp.aexp[VName.vname,
                             A],
                   Set.set[Nat.nat]](((a: AExp.aexp[VName.vname, A]) =>
                                       AExp.enumerate_regs[A](a)),
                                      Outputs[A, Unit](t))))),
     Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                                       AExp.aexp[VName.vname, A]),
                                      Set.set[Nat.nat]](((a:
                    (Nat.nat, AExp.aexp[VName.vname, A]))
                   =>
                  {
                    val (_, aa): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
                    AExp.enumerate_regs[A](aa)
                  }),
                 Updates[A, Unit](t))))),
                        Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                  AExp.aexp[VName.vname, A]),
                 Set.set[Nat.nat]](((a: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                                     {
                                       val
 (r, _): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
                                       Set.insert[Nat.nat](r,
                    Set.bot_set[Nat.nat])
                                     }),
                                    Updates[A, Unit](t)))))

def max_reg[A](t: transition_ext[A, Unit]): Option[Nat.nat] =
  (if (Cardinality.eq_set[Nat.nat](enumerate_regs[A](t), Set.bot_set[Nat.nat]))
    None else Some[Nat.nat](Lattices_Big.Max[Nat.nat](enumerate_regs[A](t))))

def Updates_update[A, B](updatesa:
                           (List[(Nat.nat, AExp.aexp[VName.vname, A])]) =>
                             List[(Nat.nat, AExp.aexp[VName.vname, A])],
                          x1: transition_ext[A, B]):
      transition_ext[A, B]
  =
  (updatesa, x1) match {
  case (updatesa, transition_exta(label, arity, guards, outputs, updates, more))
    => transition_exta[A, B](label, arity, guards, outputs, updatesa(updates),
                              more)
}

def Outputs_update[A, B](outputsa:
                           (List[AExp.aexp[VName.vname, A]]) =>
                             List[AExp.aexp[VName.vname, A]],
                          x1: transition_ext[A, B]):
      transition_ext[A, B]
  =
  (outputsa, x1) match {
  case (outputsa, transition_exta(label, arity, guards, outputs, updates, more))
    => transition_exta[A, B](label, arity, guards, outputsa(outputs), updates,
                              more)
}

def Guards_update[A, B](guardsa:
                          (List[GExp.gexp[VName.vname, A]]) =>
                            List[GExp.gexp[VName.vname, A]],
                         x1: transition_ext[A, B]):
      transition_ext[A, B]
  =
  (guardsa, x1) match {
  case (guardsa, transition_exta(label, arity, guards, outputs, updates, more))
    => transition_exta[A, B](label, arity, guardsa(guards), outputs, updates,
                              more)
}

def rename_regs[A](f: Nat.nat => Nat.nat, t: transition_ext[A, Unit]):
      transition_ext[A, Unit]
  =
  Updates_update[A, Unit](((_: List[(Nat.nat, AExp.aexp[VName.vname, A])]) =>
                            Lista.map[(Nat.nat, AExp.aexp[VName.vname, A]),
                                       (Nat.nat,
 AExp.aexp[VName.vname,
            A])](((a: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                   {
                     val (r, u): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
                     (f(r), AExp.rename_regs[A](f, u))
                   }),
                  Updates[A, Unit](t))),
                           Outputs_update[A,
   Unit](((_: List[AExp.aexp[VName.vname, A]]) =>
           Lista.map[AExp.aexp[VName.vname, A],
                      AExp.aexp[VName.vname,
                                 A]](((a: AExp.aexp[VName.vname, A]) =>
                                       AExp.rename_regs[A](f, a)),
                                      Outputs[A, Unit](t))),
          Guards_update[A, Unit](((_: List[GExp.gexp[VName.vname, A]]) =>
                                   Lista.map[GExp.gexp[VName.vname, A],
      GExp.gexp[VName.vname,
                 A]](((a: GExp.gexp[VName.vname, A]) =>
                       GExp.rename_regs[A](f, a)),
                      Guards[A, Unit](t))),
                                  t)))

def apply_outputs[A : Value.aexp_value](p: List[AExp.aexp[VName.vname, A]],
 s: VName.vname => Option[A]):
      List[Option[A]]
  =
  Lista.map[AExp.aexp[VName.vname, A],
             Option[A]](((pa: AExp.aexp[VName.vname, A]) =>
                          AExp.aval[VName.vname, A](pa, s)),
                         p)

def apply_updates[A : HOL.equal : Value.aexp_value](u:
              List[(Nat.nat, AExp.aexp[VName.vname, A])],
             old: VName.vname => Option[A]):
      (Map[Nat.nat, Option[A]]) => Map[Nat.nat, Option[A]]
  =
  ((a: Map[Nat.nat, Option[A]]) =>
    Lista.fold[(Nat.nat, AExp.aexp[VName.vname, A]),
                Map[Nat.nat, Option[A]]](((h:
     (Nat.nat, AExp.aexp[VName.vname, A]))
    =>
   (r: Map[Nat.nat, Option[A]]) =>
   r + ((h._1) -> (AExp.aval[VName.vname, A](h._2, old)))),
  u, a))

def enumerate_ints[A : Value.aexp_value](t: transition_ext[A, Unit]):
      Set.set[Int.int]
  =
  Set.sup_set[Int.int](Set.sup_set[Int.int](Set.sup_set[Int.int](Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[GExp.gexp[VName.vname,
                            A],
                  Set.set[Int.int]](((a: GExp.gexp[VName.vname, A]) =>
                                      GExp.enumerate_gexp_ints[VName.vname,
                        A](a)),
                                     Guards[A, Unit](t)))),
                          Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[AExp.aexp[VName.vname,
                             A],
                   Set.set[Int.int]](((a: AExp.aexp[VName.vname, A]) =>
                                       AExp.enumerate_aexp_ints[VName.vname,
                         A](a)),
                                      Outputs[A, Unit](t))))),
     Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[(Nat.nat,
                                       AExp.aexp[VName.vname, A]),
                                      Set.set[Int.int]](((a:
                    (Nat.nat, AExp.aexp[VName.vname, A]))
                   =>
                  {
                    val (_, aa): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
                    AExp.enumerate_aexp_ints[VName.vname, A](aa)
                  }),
                 Updates[A, Unit](t))))),
                        Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[(Nat.nat,
                  AExp.aexp[VName.vname, A]),
                 Set.set[Int.int]](((a: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                                     {
                                       val
 (r, _): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
                                       Set.insert[Int.int](Code_Target_Nat.int_of_nat(r),
                    Set.bot_set[Int.int])
                                     }),
                                    Updates[A, Unit](t)))))

def Label[A, B](x0: transition_ext[A, B]): String = x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => label
}

def Arity[A, B](x0: transition_ext[A, B]): Nat.nat = x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => arity
}

def same_structure[A](t1: transition_ext[A, Unit], t2: transition_ext[A, Unit]):
      Boolean
  =
  (Label[A, Unit](t1) ==
    Label[A, Unit](t2)) && ((Nat.equal_nata(Arity[A, Unit](t1),
     Arity[A, Unit](t2))) && (Nat.equal_nata(Nat.Nata((Outputs[A,
                        Unit](t1)).par.length),
      Nat.Nata((Outputs[A, Unit](t2)).par.length))))

def more[A, B](x0: transition_ext[A, B]): B = x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => more
}

} /* object Transition */

object Product_Lexorder {

def less_eq_prod[A : Orderings.ord, B : Orderings.ord](x0: (A, B), x1: (A, B)):
      Boolean
  =
  (x0, x1) match {
  case ((x1, y1), (x2, y2)) =>
    (Orderings.less[A](x1, x2)) || ((Orderings.less_eq[A](x1,
                   x2)) && (Orderings.less_eq[B](y1, y2)))
}

def less_prod[A : Orderings.ord, B : Orderings.ord](x0: (A, B), x1: (A, B)):
      Boolean
  =
  (x0, x1) match {
  case ((x1, y1), (x2, y2)) =>
    (Orderings.less[A](x1, x2)) || ((Orderings.less_eq[A](x1,
                   x2)) && (Orderings.less[B](y1, y2)))
}

} /* object Product_Lexorder */

object List_Lexorder {

def less_eq_list[A : HOL.equal : Orderings.order](x0: List[A], xs: List[A]):
      Boolean
  =
  (x0, xs) match {
  case (x :: xs, y :: ys) =>
    (Orderings.less[A](x, y)) || ((HOL.eq[A](x,
      y)) && (less_eq_list[A](xs, ys)))
  case (Nil, xs) => true
  case (x :: xs, Nil) => false
}

def less_list[A : HOL.equal : Orderings.order](xs: List[A], x1: List[A]):
      Boolean
  =
  (xs, x1) match {
  case (x :: xs, y :: ys) =>
    (Orderings.less[A](x, y)) || ((HOL.eq[A](x, y)) && (less_list[A](xs, ys)))
  case (Nil, x :: xs) => true
  case (xs, Nil) => false
}

} /* object List_Lexorder */

object AExp_Lexorder {

def less_aexp_aux[A : HOL.equal : Orderings.linorder,
                   B : HOL.equal : Orderings.linorder](x0: AExp.aexp[A, B],
                x1: AExp.aexp[A, B]):
      Boolean
  =
  (x0, x1) match {
  case (AExp.L(l1), AExp.L(l2)) => Orderings.less[B](l1, l2)
  case (AExp.L(l1), AExp.V(v)) => true
  case (AExp.L(l1), AExp.Plus(v, va)) => true
  case (AExp.L(l1), AExp.Minus(v, va)) => true
  case (AExp.L(l1), AExp.Times(v, va)) => true
  case (AExp.V(v1), AExp.L(l1)) => false
  case (AExp.V(v1), AExp.V(v2)) => Orderings.less[A](v1, v2)
  case (AExp.V(v1), AExp.Plus(v, va)) => true
  case (AExp.V(v1), AExp.Minus(v, va)) => true
  case (AExp.V(v1), AExp.Times(v, va)) => true
  case (AExp.Plus(e1, e2), AExp.L(l2)) => false
  case (AExp.Plus(e1, e2), AExp.V(v2)) => false
  case (AExp.Plus(e1a, e2a), AExp.Plus(e1, e2)) =>
    (less_aexp_aux[A, B](e1a, e1)) || ((AExp.equal_aexpa[A,
                  B](e1a, e1)) && (less_aexp_aux[A, B](e2a, e2)))
  case (AExp.Plus(e1, e2), AExp.Minus(v, va)) => true
  case (AExp.Plus(e1, e2), AExp.Times(v, va)) => true
  case (AExp.Minus(e1a, e2a), AExp.Minus(e1, e2)) =>
    (less_aexp_aux[A, B](e1a, e1)) || ((AExp.equal_aexpa[A,
                  B](e1a, e1)) && (less_aexp_aux[A, B](e2a, e2)))
  case (AExp.Minus(e1a, e2a), AExp.Times(e1, e2)) => true
  case (AExp.Minus(e1, e2), AExp.L(v)) => false
  case (AExp.Minus(e1, e2), AExp.V(v)) => false
  case (AExp.Minus(e1, e2), AExp.Plus(v, va)) => false
  case (AExp.Times(e1a, e2a), AExp.Times(e1, e2)) =>
    (less_aexp_aux[A, B](e1a, e1)) || ((AExp.equal_aexpa[A,
                  B](e1a, e1)) && (less_aexp_aux[A, B](e2a, e2)))
  case (AExp.Times(e1, e2), AExp.L(v)) => false
  case (AExp.Times(e1, e2), AExp.V(v)) => false
  case (AExp.Times(e1, e2), AExp.Plus(v, va)) => false
  case (AExp.Times(e1, e2), AExp.Minus(v, va)) => false
}

def height[A, B](x0: AExp.aexp[A, B]): Nat.nat = x0 match {
  case AExp.L(l2) => Nat.Nata((1))
  case AExp.V(v2) => Nat.Nata((1))
  case AExp.Plus(e1, e2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A, B](e1), height[A, B](e2)))
  case AExp.Minus(e1, e2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A, B](e1), height[A, B](e2)))
  case AExp.Times(e1, e2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A, B](e1), height[A, B](e2)))
}

def less_aexp[A : HOL.equal : Orderings.linorder,
               B : HOL.equal : Orderings.linorder](a1: AExp.aexp[A, B],
            a2: AExp.aexp[A, B]):
      Boolean
  =
  {
    val h1: Nat.nat = height[A, B](a1)
    val h2: Nat.nat = height[A, B](a2);
    (if (Nat.equal_nata(h1, h2)) less_aexp_aux[A, B](a1, a2)
      else Nat.less_nat(h1, h2))
  }

def less_eq_aexp[A : HOL.equal : Orderings.linorder,
                  B : HOL.equal : Orderings.linorder](e1: AExp.aexp[A, B],
               e2: AExp.aexp[A, B]):
      Boolean
  =
  (less_aexp[A, B](e1, e2)) || (AExp.equal_aexpa[A, B](e1, e2))

} /* object AExp_Lexorder */

object GExp_Lexorder {

def less_gexp_aux[A : HOL.equal : Orderings.linorder,
                   B : HOL.equal : Orderings.linorder](x0: GExp.gexp[A, B],
                x1: GExp.gexp[A, B]):
      Boolean
  =
  (x0, x1) match {
  case (GExp.Bc(b1), GExp.Bc(b2)) => Orderings.less_bool(b1, b2)
  case (GExp.Bc(b1), GExp.Eq(v, va)) => true
  case (GExp.Bc(b1), GExp.Gt(v, va)) => true
  case (GExp.Bc(b1), GExp.In(v, va)) => true
  case (GExp.Bc(b1), GExp.Nor(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.Bc(b2)) => false
  case (GExp.Eq(e1a, e2a), GExp.Eq(e1, e2)) =>
    (AExp_Lexorder.less_aexp[A, B](e1a, e1)) || ((AExp.equal_aexpa[A,
                            B](e1a, e1)) && (AExp_Lexorder.less_aexp[A,
                              B](e2a, e2)))
  case (GExp.Eq(e1, e2), GExp.Gt(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.In(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.Nor(v, va)) => true
  case (GExp.Gt(e1, e2), GExp.Bc(b2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Eq(e1, e2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Gt(e1, e2)) =>
    (AExp_Lexorder.less_aexp[A, B](e1a, e1)) || ((AExp.equal_aexpa[A,
                            B](e1a, e1)) && (AExp_Lexorder.less_aexp[A,
                              B](e2a, e2)))
  case (GExp.Gt(e1, e2), GExp.In(v, va)) => true
  case (GExp.Gt(e1, e2), GExp.Nor(v, va)) => true
  case (GExp.In(vb, vc), GExp.Nor(v, va)) => true
  case (GExp.In(vb, vc), GExp.In(v, va)) =>
    (Orderings.less[A](vb, v)) || ((HOL.eq[A](vb,
       v)) && (List_Lexorder.less_list[B](vc, va)))
  case (GExp.In(vb, vc), GExp.Bc(v)) => false
  case (GExp.In(vb, vc), GExp.Eq(v, va)) => false
  case (GExp.In(vb, vc), GExp.Gt(v, va)) => false
  case (GExp.Nor(g1a, g2a), GExp.Nor(g1, g2)) =>
    (less_gexp_aux[A, B](g1a, g1)) || ((GExp.equal_gexpa[A,
                  B](g1a, g1)) && (less_gexp_aux[A, B](g2a, g2)))
  case (GExp.Nor(g1, g2), GExp.Bc(v)) => false
  case (GExp.Nor(g1, g2), GExp.Eq(v, va)) => false
  case (GExp.Nor(g1, g2), GExp.Gt(v, va)) => false
  case (GExp.Nor(g1, g2), GExp.In(v, va)) => false
}

def height[A, B](x0: GExp.gexp[A, B]): Nat.nat = x0 match {
  case GExp.Bc(uu) => Nat.Nata((1))
  case GExp.Eq(a_1, a_2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](AExp_Lexorder.height[A, B](a_1),
   AExp_Lexorder.height[A, B](a_2)))
  case GExp.Gt(a_1, a_2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](AExp_Lexorder.height[A, B](a_1),
   AExp_Lexorder.height[A, B](a_2)))
  case GExp.In(v, l) =>
    Nat.plus_nata(Code_Numeral.nat_of_integer(BigInt(2)),
                   Nat.Nata(l.par.length))
  case GExp.Nor(g_1, g_2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A, B](g_1), height[A, B](g_2)))
}

def less_gexp[A : HOL.equal : Orderings.linorder,
               B : HOL.equal : Orderings.linorder](a1: GExp.gexp[A, B],
            a2: GExp.gexp[A, B]):
      Boolean
  =
  {
    val h1: Nat.nat = height[A, B](a1)
    val h2: Nat.nat = height[A, B](a2);
    (if (Nat.equal_nata(h1, h2)) less_gexp_aux[A, B](a1, a2)
      else Nat.less_nat(h1, h2))
  }

def less_eq_gexp[A : HOL.equal : Orderings.linorder,
                  B : HOL.equal : Orderings.linorder](e1: GExp.gexp[A, B],
               e2: GExp.gexp[A, B]):
      Boolean
  =
  (less_gexp[A, B](e1, e2)) || (GExp.equal_gexpa[A, B](e1, e2))

} /* object GExp_Lexorder */

object Transition_Lexorder {

def less_transition_ext[A : HOL.equal : Orderings.linorder,
                         B : Orderings.linorder](t1:
           Transition.transition_ext[A, B],
          t2: Transition.transition_ext[A, B]):
      Boolean
  =
  Product_Lexorder.less_prod[String,
                              (Nat.nat,
                                (List[GExp.gexp[VName.vname, A]],
                                  (List[AExp.aexp[VName.vname, A]],
                                    (List[(Nat.nat, AExp.aexp[VName.vname, A])],
                                      B))))]((Transition.Label[A, B](t1),
       (Transition.Arity[A, B](t1),
         (Transition.Guards[A, B](t1),
           (Transition.Outputs[A, B](t1),
             (Transition.Updates[A, B](t1), Transition.more[A, B](t1)))))),
      (Transition.Label[A, B](t2),
        (Transition.Arity[A, B](t2),
          (Transition.Guards[A, B](t2),
            (Transition.Outputs[A, B](t2),
              (Transition.Updates[A, B](t2), Transition.more[A, B](t2)))))))

def less_eq_transition_ext[A : HOL.equal : Orderings.linorder,
                            B : HOL.equal : Orderings.linorder](t1:
                          Transition.transition_ext[A, B],
                         t2: Transition.transition_ext[A, B]):
      Boolean
  =
  (less_transition_ext[A, B](t1, t2)) || (Transition.equal_transition_exta[A,
                                    B](t1, t2))

} /* object Transition_Lexorder */

object Option_ord {

def bot_optiona[A : Orderings.order]: Option[A] = None

def less_eq_option[A : Orderings.preorder](xa0: Option[A], x: Option[A]):
      Boolean
  =
  (xa0, x) match {
  case (Some(x), Some(y)) => Orderings.less_eq[A](x, y)
  case (Some(x), None) => false
  case (None, x) => true
}

def less_option[A : Orderings.preorder](x: Option[A], xa1: Option[A]): Boolean =
  (x, xa1) match {
  case (Some(x), Some(y)) => Orderings.less[A](x, y)
  case (None, Some(x)) => true
  case (x, None) => false
}

} /* object Option_ord */

object Finite_Set {

def card[A](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.seta(xs) => Nat.Nata((xs.par.distinct.toList).par.length)
}

} /* object Finite_Set */

object FSet {

abstract sealed class fset[A]
final case class fset_of_list[A](a: List[A]) extends fset[A]

def size_fset[A](x0: fset[A]): Nat.nat = x0 match {
  case fset_of_list(as) => Nat.Nata((as.par.distinct.toList).par.length)
}

def fBall[A](x0: fset[A], f: A => Boolean): Boolean = (x0, f) match {
  case (fset_of_list(l), f) => Lista.list_all[A](f, l)
}

def equal_fseta[A : HOL.equal](x: fset[A], xa1: fset[A]): Boolean = (x, xa1)
  match {
  case (x, fset_of_list(y)) =>
    (Nat.equal_nata(size_fset[A](x),
                     Nat.Nata((y.par.distinct.toList).par.length))) && (fBall[A](x,
  ((a: A) => y.contains(a))))
}

def fBex[A](x0: fset[A], f: A => Boolean): Boolean = (x0, f) match {
  case (fset_of_list(l), f) => Lista.list_ex[A](f, l)
}

def fimage[A, B](f: A => B, x1: fset[A]): fset[B] = (f, x1) match {
  case (f, fset_of_list(as)) =>
    fset_of_list[B](Lista.map[A, B](f, as.par.distinct.toList))
}

def sup_fset[A](x0: fset[A], x1: fset[A]): fset[A] = (x0, x1) match {
  case (fset_of_list(f1), fset_of_list(f2)) =>
    fset_of_list[A]((f1 ++ f2).par.distinct.toList)
}

def bot_fset[A]: fset[A] = fset_of_list[A](Nil)

def ffUnion[A](x0: fset[fset[A]]): fset[A] = x0 match {
  case fset_of_list(as) =>
    Lista.fold[fset[A],
                fset[A]](((a: fset[A]) => (b: fset[A]) => sup_fset[A](a, b)),
                          as, bot_fset[A])
}

def ffilter[A](f: A => Boolean, x1: fset[A]): fset[A] = (f, x1) match {
  case (f, fset_of_list(as)) =>
    fset_of_list[A](Lista.filter[A](f, as.par.distinct.toList))
}

def finsert[A](a: A, x1: fset[A]): fset[A] = (a, x1) match {
  case (a, fset_of_list(as)) => fset_of_list[A](Lista.insert[A](a, as))
}

def fmember[A](a: A, x1: fset[A]): Boolean = (a, x1) match {
  case (a, fset_of_list(as)) => as.contains(a)
}

def fset[A](x0: fset[A]): Set.set[A] = x0 match {
  case fset_of_list(l) =>
    Lista.fold[A, Set.set[A]](((a: A) => (b: Set.set[A]) =>
                                Set.insert[A](a, b)),
                               l, Set.bot_set[A])
}

def fthe_elem[A](x0: fset[A]): A = x0 match {
  case fset_of_list(List(x)) => x
}

def fMax[A : Orderings.linorder](x0: fset[A]): A = x0 match {
  case fset_of_list(h :: t) => t.par.fold(h)(Orderings.max)
}

def fMin[A : Orderings.linorder](x0: fset[A]): A = x0 match {
  case fset_of_list(h :: t) => t.par.fold(h)(Orderings.min)
}

def sorted_list_of_fset[A : Orderings.linorder](x0: fset[A]): List[A] = x0 match
  {
  case fset_of_list(l) => (l.par.distinct.toList).sortWith((Orderings.less))
}

def less_eq_fset[A](x0: fset[A], a: fset[A]): Boolean = (x0, a) match {
  case (fset_of_list(l), a) =>
    Lista.list_all[A](((x: A) => fmember[A](x, a)), l)
}

def less_fset[A](sa: fset[A], s: fset[A]): Boolean =
  (less_eq_fset[A](sa, s)) && (Nat.less_nat(size_fset[A](sa), size_fset[A](s)))

def minus_fset[A](x0: fset[A], xs: fset[A]): fset[A] = (x0, xs) match {
  case (fset_of_list(a), xs) =>
    fset_of_list[A]((Lista.filter[A](((x: A) => ! (fmember[A](x, xs))),
                                      a)).par.distinct.toList)
}

} /* object FSet */

object FSet_Utils {

def fSum[A : Groups.comm_monoid_add](x0: FSet.fset[A]): A = x0 match {
  case FSet.fset_of_list(l) =>
    Lista.fold[A, A](((a: A) => (b: A) => Groups.plus[A](a, b)),
                      l.par.distinct.toList, Groups.zero[A])
}

def fprod[A, B](x0: FSet.fset[A], x1: FSet.fset[B]): FSet.fset[(A, B)] =
  (x0, x1) match {
  case (FSet.fset_of_list(xs), FSet.fset_of_list(ys)) =>
    FSet.fset_of_list[(A, B)]((Lista.maps[A,
   (A, B)](((x: A) => Lista.map[B, (A, B)](((a: B) => (x, a)), ys)),
            xs)).par.distinct.toList)
}

def fremove[A : HOL.equal](aa: A, x1: FSet.fset[A]): FSet.fset[A] = (aa, x1)
  match {
  case (aa, FSet.fset_of_list(a)) =>
    FSet.fset_of_list[A](Lista.filter[A](((x: A) => ! (HOL.eq[A](x, aa))), a))
}

def ffold_ord[A : HOL.equal : Orderings.linorder,
               B](f: A => B => B, s: FSet.fset[A], b: B):
      B
  =
  (if (HOL.eq[FSet.fset[A]](s, FSet.bot_fset[A])) b
    else {
           val h: A = FSet.fMin[A](s)
           val t: FSet.fset[A] = fremove[A](h, s);
           ffold_ord[A, B](f, t, (f(h))(b))
         })

def fis_singleton[A](s: FSet.fset[A]): Boolean =
  Nat.equal_nata(FSet.size_fset[A](s), Nat.Nata((1)))

} /* object FSet_Utils */

object Code_Generation {

def mutex[A : HOL.equal,
           B : HOL.equal](uu: GExp.gexp[A, B], uv: GExp.gexp[A, B]):
      Boolean
  =
  (uu, uv) match {
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.Eq(AExp.V(v), AExp.L(l))) =>
    (if (HOL.eq[A](va, v)) ! (HOL.eq[B](la, l)) else false)
  case (GExp.In(va, la), GExp.Eq(AExp.V(v), AExp.L(l))) =>
    (HOL.eq[A](va, v)) && (! (la.contains(l)))
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.In(v, l)) =>
    (HOL.eq[A](v, va)) && (! (l.contains(la)))
  case (GExp.In(va, la), GExp.In(v, l)) =>
    (HOL.eq[A](va, v)) && (Set.is_empty[B](Set.inf_set[B](Set.seta[B](la),
                   Set.seta[B](l))))
  case (GExp.Bc(v), uv) => false
  case (GExp.Eq(AExp.L(vb), va), uv) => false
  case (GExp.Eq(AExp.Plus(vb, vc), va), uv) => false
  case (GExp.Eq(AExp.Minus(vb, vc), va), uv) => false
  case (GExp.Eq(AExp.Times(vb, vc), va), uv) => false
  case (GExp.Eq(v, AExp.V(vb)), uv) => false
  case (GExp.Eq(v, AExp.Plus(vb, vc)), uv) => false
  case (GExp.Eq(v, AExp.Minus(vb, vc)), uv) => false
  case (GExp.Eq(v, AExp.Times(vb, vc)), uv) => false
  case (GExp.Gt(v, va), uv) => false
  case (GExp.In(v, va), GExp.Bc(vb)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.L(vd), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Plus(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Minus(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Times(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.V(vd))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Plus(vd, ve))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Minus(vd, ve))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Times(vd, ve))) => false
  case (GExp.In(v, va), GExp.Gt(vb, vc)) => false
  case (GExp.In(v, va), GExp.Nor(vb, vc)) => false
  case (GExp.Nor(v, va), uv) => false
  case (uu, GExp.Bc(v)) => false
  case (uu, GExp.Eq(AExp.L(vb), va)) => false
  case (uu, GExp.Eq(AExp.Plus(vb, vc), va)) => false
  case (uu, GExp.Eq(AExp.Minus(vb, vc), va)) => false
  case (uu, GExp.Eq(AExp.Times(vb, vc), va)) => false
  case (uu, GExp.Eq(v, AExp.V(vb))) => false
  case (uu, GExp.Eq(v, AExp.Plus(vb, vc))) => false
  case (uu, GExp.Eq(v, AExp.Minus(vb, vc))) => false
  case (uu, GExp.Eq(v, AExp.Times(vb, vc))) => false
  case (uu, GExp.Gt(v, va)) => false
  case (uu, GExp.Nor(v, va)) => false
}

def choice_cases[A : HOL.equal : Value.aexp_value](t1:
             Transition.transition_ext[A, Unit],
            t2: Transition.transition_ext[A, Unit]):
      Boolean
  =
  (if (Lista.list_ex[(GExp.gexp[VName.vname, A],
                       GExp.gexp[VName.vname,
                                  A])](((a:
   (GExp.gexp[VName.vname, A], GExp.gexp[VName.vname, A]))
  =>
 {
   val (aa, b): (GExp.gexp[VName.vname, A], GExp.gexp[VName.vname, A]) = a;
   mutex[VName.vname, A](aa, b)
 }),
Lista.product[GExp.gexp[VName.vname, A],
               GExp.gexp[VName.vname,
                          A]](Transition.Guards[A, Unit](t1),
                               Transition.Guards[A, Unit](t2))))
    false
    else (if (Lista.equal_lista[GExp.gexp[VName.vname,
   A]](Transition.Guards[A, Unit](t1), Transition.Guards[A, Unit](t2)))
           Dirties.satisfiable[A](Lista.foldr[GExp.gexp[VName.vname, A],
       GExp.gexp[VName.vname,
                  A]](((a: GExp.gexp[VName.vname, A]) =>
                        (b: GExp.gexp[VName.vname, A]) =>
                        GExp.gAnd[VName.vname, A](a, b)),
                       Transition.Guards[A, Unit](t1),
                       GExp.Bc[VName.vname, A](true)))
           else Dirties.satisfiable[A](Lista.foldr[GExp.gexp[VName.vname, A],
            GExp.gexp[VName.vname,
                       A]](((a: GExp.gexp[VName.vname, A]) =>
                             (b: GExp.gexp[VName.vname, A]) =>
                             GExp.gAnd[VName.vname, A](a, b)),
                            Transition.Guards[A, Unit](t1) ++
                              Transition.Guards[A, Unit](t2),
                            GExp.Bc[VName.vname, A](true)))))

def infer_with_log[A : HOL.equal : Orderings.linorder : Value.aexp_value](failedMerges:
                                    Set.set[(Nat.nat, Nat.nat)],
                                   k: Nat.nat,
                                   e: FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                   r: (List[Nat.nat]) =>
(List[Nat.nat]) =>
  (FSet.fset[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
    Nat.nat,
                                   m: (List[Nat.nat]) =>
(List[Nat.nat]) =>
  Nat.nat =>
    (FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat),
                     Transition.transition_ext[A, Unit]))]) =>
        (FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[A, Unit]))]) =>
          ((FSet.fset[((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit])]) =>
            Boolean) =>
            Option[FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))]],
                                   check:
                                     (FSet.fset[((Nat.nat, Nat.nat),
          Transition.transition_ext[A, Unit])]) =>
                                       Boolean,
                                   np: (FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
 FSet.fset[(Nat.nat,
             ((Nat.nat, Nat.nat),
               ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  {
    val scores: FSet.fset[Inference.score_ext[Unit]] =
      (if (Nat.equal_nata(k, Nat.Nata((1)))) Inference.score_1[A](e, r)
        else Inference.k_score[A](k, e, r));
    (Inference.inference_step[A](failedMerges, e,
                                  FSet.ffilter[Inference.score_ext[Unit]](((s:
                                      Inference.score_ext[Unit])
                                     =>
                                    ! (Set.member[(Nat.nat,
            Nat.nat)]((Inference.S1[Unit](s), Inference.S2[Unit](s)),
                       failedMerges))),
                                   scores),
                                  m, check, np)
       match {
       case (None, _) => e
       case (Some(newa), x) =>
         (if (FSet.less_fset[Nat.nat](Inference.S[A](newa), Inference.S[A](e)))
           {
             Log.logStates(newa, (FSet.size_fset[Nat.nat](Inference.S[A](e))));
             infer_with_log[A](x, k, newa, r, m, check, np)
           }
           else e)
     })
  }

} /* object Code_Generation */

object Inference {

abstract sealed class score_ext[A]
final case class score_exta[A](a: Nat.nat, b: Nat.nat, c: Nat.nat, d: A) extends
  score_ext[A]

def equal_score_exta[A : HOL.equal](x0: score_ext[A], x1: score_ext[A]): Boolean
  =
  (x0, x1) match {
  case (score_exta(scorea, s1a, s2a, morea), score_exta(score, s1, s2, more)) =>
    (Nat.equal_nata(scorea,
                     score)) && ((Nat.equal_nata(s1a,
          s1)) && ((Nat.equal_nata(s2a, s2)) && (HOL.eq[A](morea, more))))
}

def Score[A](x0: score_ext[A]): Nat.nat = x0 match {
  case score_exta(score, s1, s2, more) => score
}

def more[A](x0: score_ext[A]): A = x0 match {
  case score_exta(score, s1, s2, more) => more
}

def S2[A](x0: score_ext[A]): Nat.nat = x0 match {
  case score_exta(score, s1, s2, more) => s2
}

def S1[A](x0: score_ext[A]): Nat.nat = x0 match {
  case score_exta(score, s1, s2, more) => s1
}

def less_score_ext[A : Orderings.linorder](t1: score_ext[A], t2: score_ext[A]):
      Boolean
  =
  Product_Lexorder.less_prod[Nat.nat,
                              (Nat.nat,
                                (Nat.nat,
                                  A))]((Score[A](t2),
 (S1[A](t1), (S2[A](t1), more[A](t1)))),
(Score[A](t1), (S1[A](t2), (S2[A](t2), more[A](t2)))))

def less_eq_score_ext[A : HOL.equal : Orderings.linorder](s1: score_ext[A],
                   s2: score_ext[A]):
      Boolean
  =
  (less_score_ext[A](s1, s2)) || (equal_score_exta[A](s1, s2))

def S[A](m: FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))]):
      FSet.fset[Nat.nat]
  =
  FSet.sup_fset[Nat.nat](FSet.fimage[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit])),
                                      Nat.nat](((a:
           (List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
          =>
         {
           val (_, aa):
                 (List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
             = a
           val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
             = aa;
           ({
              val (s, _): (Nat.nat, Nat.nat) = ab;
              ((_: Transition.transition_ext[A, Unit]) => s)
            })(b)
         }),
        m),
                          FSet.fimage[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
                                       Nat.nat](((a:
            (List[Nat.nat],
              ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
           =>
          {
            val (_, aa):
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
              = a
            val (ab, b):
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
              = aa;
            ({
               val (_, s): (Nat.nat, Nat.nat) = ab;
               ((_: Transition.transition_ext[A, Unit]) => s)
             })(b)
          }),
         m))

def tm[A](e: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
               ((Nat.nat, Nat.nat),
                 Transition.transition_ext[A,
    Unit])](((a: (List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
               =>
              a._2),
             e)

def dest[A](uid: List[Nat.nat],
             t: FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  (((FSet.fthe_elem[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A,
           Unit]))](FSet.ffilter[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A,
                        Unit]))](((x: (List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                                    =>
                                   Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                        Set.seta[Nat.nat](x._1))),
                                  t)))._2)._1)._2

def uids[A](e: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))]):
      FSet.fset[Nat.nat]
  =
  FSet.ffUnion[Nat.nat](FSet.fimage[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit])),
                                     FSet.fset[Nat.nat]](Fun.comp[List[Nat.nat],
                           FSet.fset[Nat.nat],
                           (List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[A,
                  Unit]))](((a: List[Nat.nat]) =>
                             FSet.fset_of_list[Nat.nat](a)),
                            ((a: (List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit])))
                               =>
                              a._1)),
                  e))

def infer[A : HOL.equal : Orderings.linorder : Value.aexp_value](f:
                           Set.set[(Nat.nat, Nat.nat)],
                          k: Nat.nat,
                          e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                          r: (List[Nat.nat]) =>
                               (List[Nat.nat]) =>
                                 (FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                   Nat.nat,
                          m: (List[Nat.nat]) =>
                               (List[Nat.nat]) =>
                                 Nat.nat =>
                                   (FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                     (FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                       (FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
 ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]) =>
   Boolean) =>
   Option[FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))]],
                          check:
                            (FSet.fset[((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit])]) =>
                              Boolean,
                          np: (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat),
      ((Transition.transition_ext[A, Unit], List[Nat.nat]),
        (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  Code_Generation.infer_with_log[A](f, k, e, r, m, check, np)

def learn[A : HOL.equal : Orderings.linorder : Value.aexp_value](n: Nat.nat,
                          pta: FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                          l: List[List[(String, (List[A], List[A]))]],
                          r: (List[Nat.nat]) =>
                               (List[Nat.nat]) =>
                                 (FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                   Nat.nat,
                          m: (List[Nat.nat]) =>
                               (List[Nat.nat]) =>
                                 Nat.nat =>
                                   (FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                     (FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                       (FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
 ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]) =>
   Boolean) =>
   Option[FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))]],
                          np: (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat),
      ((Transition.transition_ext[A, Unit], List[Nat.nat]),
        (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  {
    val check:
          (FSet.fset[((Nat.nat, Nat.nat),
                       Transition.transition_ext[A, Unit])]) =>
            Boolean
      = ((a: FSet.fset[((Nat.nat, Nat.nat),
                         Transition.transition_ext[A, Unit])])
           =>
          EFSM.accepts_log[A](Set.seta[List[(String, (List[A], List[A]))]](l),
                               a));
    infer[A](Set.bot_set[(Nat.nat, Nat.nat)], n, pta, r, m, check, np)
  }

def bool2nat(x0: Boolean): Nat.nat = x0 match {
  case true => Nat.Nata((1))
  case false => Nat.zero_nata
}

def score_transitions[A : HOL.equal](t1: Transition.transition_ext[A, Unit],
                                      t2: Transition.transition_ext[A, Unit]):
      Nat.nat
  =
  (if ((Transition.Label[A, Unit](t1) ==
         Transition.Label[A, Unit](t2)) && ((Nat.equal_nata(Transition.Arity[A,
                                      Unit](t1),
                     Transition.Arity[A, Unit](t2))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[A,
                      Unit](t1)).par.length),
                                 Nat.Nata((Transition.Outputs[A,
                       Unit](t2)).par.length)))))
    Nat.plus_nata(Nat.plus_nata(Nat.plus_nata(Nat.plus_nata(Nat.Nata((1)),
                     bool2nat(Transition.equal_transition_exta[A,
                        Unit](t1, t2))),
       Finite_Set.card[GExp.gexp[VName.vname,
                                  A]](Set.inf_set[GExp.gexp[VName.vname,
                     A]](Set.seta[GExp.gexp[VName.vname,
     A]](Transition.Guards[A, Unit](t2)),
                          Set.seta[GExp.gexp[VName.vname,
      A]](Transition.Guards[A, Unit](t2))))),
                                 Finite_Set.card[(Nat.nat,
           AExp.aexp[VName.vname,
                      A])](Set.inf_set[(Nat.nat,
 AExp.aexp[VName.vname,
            A])](Set.seta[(Nat.nat,
                            AExp.aexp[VName.vname,
                                       A])](Transition.Updates[A, Unit](t2)),
                  Set.seta[(Nat.nat,
                             AExp.aexp[VName.vname,
A])](Transition.Updates[A, Unit](t2))))),
                   Finite_Set.card[AExp.aexp[VName.vname,
      A]](Set.inf_set[AExp.aexp[VName.vname,
                                 A]](Set.seta[AExp.aexp[VName.vname,
                 A]](Transition.Outputs[A, Unit](t2)),
                                      Set.seta[AExp.aexp[VName.vname,
                  A]](Transition.Outputs[A, Unit](t2)))))
    else Nat.zero_nata)

def order_nondeterministic_pairs[A : HOL.equal : Orderings.linorder](s:
                               FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat),
     ((Transition.transition_ext[A, Unit], List[Nat.nat]),
       (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      List[(Nat.nat,
             ((Nat.nat, Nat.nat),
               ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (Transition.transition_ext[A, Unit], List[Nat.nat]))))]
  =
  Lista.map[(Nat.nat,
              (Nat.nat,
                ((Nat.nat, Nat.nat),
                  ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (Transition.transition_ext[A, Unit], List[Nat.nat]))))),
             (Nat.nat,
               ((Nat.nat, Nat.nat),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (Transition.transition_ext[A, Unit],
                     List[Nat.nat]))))](((a:
    (Nat.nat,
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (Transition.transition_ext[A, Unit], List[Nat.nat]))))))
   =>
  a._2),
 FSet.sorted_list_of_fset[(Nat.nat,
                            (Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[A, Unit],
                                   List[Nat.nat]),
                                  (Transition.transition_ext[A, Unit],
                                    List[Nat.nat])))))](FSet.fimage[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[A, Unit],
                                   List[Nat.nat]),
                                  (Transition.transition_ext[A, Unit],
                                    List[Nat.nat])))),
                             (Nat.nat,
                               (Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   ((Transition.transition_ext[A, Unit],
                                      List[Nat.nat]),
                                     (Transition.transition_ext[A, Unit],
                                       List[Nat.nat])))))](((sa:
                       (Nat.nat,
                         ((Nat.nat, Nat.nat),
                           ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                             (Transition.transition_ext[A, Unit],
                               List[Nat.nat])))))
                      =>
                     {
                       val a: (Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  ((Transition.transition_ext[A, Unit],
                                     List[Nat.nat]),
                                    (Transition.transition_ext[A, Unit],
                                      List[Nat.nat]))))
                         = sa
                       val (_, aa):
                             (Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 ((Transition.transition_ext[A, Unit],
                                    List[Nat.nat]),
                                   (Transition.transition_ext[A, Unit],
                                     List[Nat.nat]))))
                         = a
                       val (_, ab):
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[A, Unit],
                                  List[Nat.nat]),
                                 (Transition.transition_ext[A, Unit],
                                   List[Nat.nat])))
                         = aa
                       val (ac, b):
                             ((Transition.transition_ext[A, Unit],
                                List[Nat.nat]),
                               (Transition.transition_ext[A, Unit],
                                 List[Nat.nat]))
                         = ab;
                       ({
                          val (t1, _):
                                (Transition.transition_ext[A, Unit],
                                  List[Nat.nat])
                            = ac;
                          ((ad: (Transition.transition_ext[A, Unit],
                                  List[Nat.nat]))
                             =>
                            {
                              val (t2, _):
                                    (Transition.transition_ext[A, Unit],
                                      List[Nat.nat])
                                = ad;
                              (score_transitions[A](t1, t2), sa)
                            })
                        })(b)
                     }),
                    s)))

def insert_transition[A : HOL.equal](uid: List[Nat.nat], from: Nat.nat,
                                      to: Nat.nat,
                                      t: Transition.transition_ext[A, Unit],
                                      e:
FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (if (FSet.fBall[(List[Nat.nat],
                    ((Nat.nat, Nat.nat),
                      Transition.transition_ext[A,
         Unit]))](e, ((a: (List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit])))
                        =>
                       {
                         val (_, aa):
                               (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[A, Unit]))
                           = a
                         val (ab, b):
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit])
                           = aa;
                         ({
                            val (froma, toa): (Nat.nat, Nat.nat) = ab;
                            ((ta: Transition.transition_ext[A, Unit]) =>
                              ! ((Nat.equal_nata(from,
          froma)) && ((Nat.equal_nata(to, toa)) && (Transition.equal_transition_exta[A,
      Unit](t, ta)))))
                          })(b)
                       })))
    FSet.finsert[(List[Nat.nat],
                   ((Nat.nat, Nat.nat),
                     Transition.transition_ext[A,
        Unit]))]((uid, ((from, to), t)), e)
    else FSet.fimage[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[A, Unit])),
                      (List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A,
             Unit]))](((a: (List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[A, Unit])))
                         =>
                        {
                          val (uida, aa):
                                (List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit]))
                            = a
                          val (ab, b):
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit])
                            = aa;
                          ({
                             val (froma, toa): (Nat.nat, Nat.nat) = ab;
                             ((ta: Transition.transition_ext[A, Unit]) =>
                               (if ((Nat.equal_nata(from,
             froma)) && ((Nat.equal_nata(to,
  toa)) && (Transition.equal_transition_exta[A, Unit](t, ta))))
                                 (Lista.union[Nat.nat].apply(uida).apply(uid),
                                   ((froma, toa), ta))
                                 else (uida, ((froma, toa), ta))))
                           })(b)
                        }),
                       e))

def make_distinct[A : HOL.equal : Orderings.linorder](e:
                FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  FSet_Utils.ffold_ord[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit])),
                        FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A,
                         Unit]))]](((a: (List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                                      =>
                                     {
                                       val
 (uid, aa):
   (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
 = a
                                       val
 (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]) = aa;
                                       ({
  val (ac, ba): (Nat.nat, Nat.nat) = ab;
  ((c: Transition.transition_ext[A, Unit]) =>
    (d: FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
      =>
    insert_transition[A](uid, ac, ba, c, d))
})(b)
                                     }),
                                    e, FSet.bot_fset[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])

def merge_transitions_aux[A : HOL.equal : Orderings.linorder](e:
                        FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit]))],
                       oldID: List[Nat.nat], newID: List[Nat.nat]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  {
    val a: (List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
      = FSet.fthe_elem[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A,
              Unit]))](FSet.ffilter[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit]))](((a:
  (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
 =>
{
  val (uids, _):
        (List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
    = a;
  Lista.equal_lista[Nat.nat](oldID, uids)
}),
                                       e))
    val (uids1, aa):
          (List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
      = a
    val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]) = aa;
    ({
       val (_, _): (Nat.nat, Nat.nat) = ab;
       ((old: Transition.transition_ext[A, Unit]) =>
         {
           val ac: (List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
             = FSet.fthe_elem[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A,
                     Unit]))](FSet.ffilter[(List[Nat.nat],
     ((Nat.nat, Nat.nat),
       Transition.transition_ext[A, Unit]))](((ac:
         (List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
        =>
       {
         val (uids, _):
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
           = ac;
         Lista.equal_lista[Nat.nat](newID, uids)
       }),
      e))
           val (uids2, ad):
                 (List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
             = ac
           val (ae, ba):
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
             = ad;
           ({
              val (origin, dest): (Nat.nat, Nat.nat) = ae;
              ((newa: Transition.transition_ext[A, Unit]) =>
                make_distinct[A](FSet.finsert[(List[Nat.nat],
        ((Nat.nat, Nat.nat),
          Transition.transition_ext[A, Unit]))]((Lista.union[Nat.nat].apply(uids1).apply(uids2),
          ((origin, dest), newa)),
         FSet.minus_fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A,
                Unit]))](e, FSet.finsert[(List[Nat.nat],
   ((Nat.nat, Nat.nat),
     Transition.transition_ext[A, Unit]))]((uids1, ((origin, dest), old)),
    FSet.finsert[(List[Nat.nat],
                   ((Nat.nat, Nat.nat),
                     Transition.transition_ext[A,
        Unit]))]((uids2, ((origin, dest), newa)),
                  FSet.bot_fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit]))]))))))
            })(ba)
         })
     })(b)
  }

def directly_subsumes[A : HOL.equal : Orderings.order : Value.aexp_value](e1:
                                    FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                   e2: FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                   s1: Nat.nat, s2: Nat.nat,
                                   t1: Transition.transition_ext[A, Unit],
                                   t2: Transition.transition_ext[A, Unit]):
      Boolean
  =
  (if (Transition.equal_transition_exta[A, Unit](t1, t2)) true
    else Dirties.scalaDirectlySubsumes[A](e1, e2, s1, s2, t1, t2))

def origin[A](uid: List[Nat.nat],
               t: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  (((FSet.fthe_elem[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A,
           Unit]))](FSet.ffilter[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A,
                        Unit]))](((x: (List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                                    =>
                                   Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                        Set.seta[Nat.nat](x._1))),
                                  t)))._2)._1)._1

def merge_transitions[A : HOL.equal : Orderings.linorder : Value.aexp_value](failedMerges:
                                       Set.set[(Nat.nat, Nat.nat)],
                                      oldEFSM:
FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                      preDestMerge:
FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                      destMerge:
FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                      t_1: Transition.transition_ext[A, Unit],
                                      u_1: List[Nat.nat],
                                      t_2: Transition.transition_ext[A, Unit],
                                      u_2: List[Nat.nat],
                                      modifier:
(List[Nat.nat]) =>
  (List[Nat.nat]) =>
    Nat.nat =>
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat),
                     Transition.transition_ext[A, Unit]))]) =>
        (FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[A, Unit]))]) =>
          (FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[A, Unit]))]) =>
            ((FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit])]) =>
              Boolean) =>
              Option[FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[A, Unit]))]],
                                      check:
(FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]) =>
  Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  (if (Lista.list_all[Nat.nat](((id: Nat.nat) =>
                                 directly_subsumes[A](oldEFSM, destMerge,
               origin[A](List(id), oldEFSM), origin[A](u_1, destMerge), t_2,
               t_1)),
                                u_1))
    Some[FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[A,
          Unit]))]](merge_transitions_aux[A](destMerge, u_1, u_2))
    else (if (Lista.list_all[Nat.nat](((id: Nat.nat) =>
directly_subsumes[A](oldEFSM, destMerge, origin[A](List(id), oldEFSM),
                      origin[A](u_2, destMerge), t_1, t_2)),
                                       u_2))
           Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A,
                 Unit]))]](merge_transitions_aux[A](destMerge, u_2, u_1))
           else (((((((modifier(u_1))(u_2))(origin[A](u_1,
               destMerge)))(destMerge))(preDestMerge))(oldEFSM))(check)
                   match {
                   case None => None
                   case Some(e) =>
                     Some[FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit]))]](make_distinct[A](e))
                 })))

def deterministic[A : HOL.equal](t: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                  np: (FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
FSet.fset[(Nat.nat,
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      Boolean
  =
  FSet.equal_fseta[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (Transition.transition_ext[A, Unit],
                           List[Nat.nat]))))](np(t),
       FSet.bot_fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                           (Transition.transition_ext[A, Unit],
                             List[Nat.nat]))))])

def merge_states_aux[A](s1: Nat.nat, s2: Nat.nat,
                         e: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[A,
      Unit]))](((a: (List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                  =>
                 {
                   val (uid, aa):
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))
                     = a
                   val (ab, b):
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit])
                     = aa;
                   ({
                      val (origin, dest): (Nat.nat, Nat.nat) = ab;
                      ((t: Transition.transition_ext[A, Unit]) =>
                        (uid, (((if (Nat.equal_nata(origin, s1)) s2
                                  else origin),
                                 (if (Nat.equal_nata(dest, s1)) s2 else dest)),
                                t)))
                    })(b)
                 }),
                e)

def merge_states[A](x: Nat.nat, y: Nat.nat,
                     t: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (if (Nat.equal_nata(x, y)) t
    else (if (Nat.less_nat(y, x)) merge_states_aux[A](x, y, t)
           else merge_states_aux[A](y, x, t)))

def resolve_nondeterminism[A : HOL.equal : Orderings.linorder : Value.aexp_value](failedMerges:
    Set.set[(Nat.nat, Nat.nat)],
   x1: List[(Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (Transition.transition_ext[A, Unit], List[Nat.nat]))))],
   uu: FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
   newEFSM:
     FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
   uv: (List[Nat.nat]) =>
         (List[Nat.nat]) =>
           Nat.nat =>
             (FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]) =>
               (FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit]))]) =>
                 (FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit]))]) =>
                   ((FSet.fset[((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit])]) =>
                     Boolean) =>
                     Option[FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]],
   check:
     (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]) =>
       Boolean,
   np: (FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat),
                      Transition.transition_ext[A, Unit]))]) =>
         FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (Transition.transition_ext[A, Unit],
                           List[Nat.nat]))))]):
      (Option[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]],
        Set.set[(Nat.nat, Nat.nat)])
  =
  (failedMerges, x1, uu, newEFSM, uv, check, np) match {
  case (failedMerges, Nil, uu, newEFSM, uv, check, np) =>
    ((if ((deterministic[A](newEFSM, np)) && (check(tm[A](newEFSM))))
       Some[FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))]](newEFSM)
       else None),
      failedMerges)
  case (failedMerges,
         (from, ((dest_1, dest_2), ((t_1, u_1), (t_2, u_2)))) :: ss, oldEFSM,
         newEFSM, m, check, np)
    => (if ((Set.member[(Nat.nat,
                          Nat.nat)]((dest_1, dest_2),
                                     failedMerges)) || (Set.member[(Nat.nat,
                             Nat.nat)]((dest_2, dest_1), failedMerges)))
         (None, failedMerges)
         else {
                val destMerge:
                      FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit]))]
                  = merge_states[A](dest_1, dest_2, newEFSM);
                (merge_transitions[A](failedMerges, oldEFSM, newEFSM, destMerge,
                                       t_1, u_1, t_2, u_2, m, check)
                   match {
                   case None =>
                     resolve_nondeterminism[A](Set.insert[(Nat.nat,
                    Nat.nat)]((dest_1, dest_2), failedMerges),
        ss, oldEFSM, newEFSM, m, check, np)
                   case Some(newa) =>
                     {
                       val newScores:
                             List[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      ((Transition.transition_ext[A, Unit],
 List[Nat.nat]),
(Transition.transition_ext[A, Unit], List[Nat.nat]))))]
                         = order_nondeterministic_pairs[A](np(newa));
                       (if (Product_Lexorder.less_prod[Nat.nat,
                (Nat.nat,
                  Nat.nat)]((FSet.size_fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))](newa),
                              (FSet.size_fset[Nat.nat](S[A](newa)),
                                Nat.Nata(newScores.par.length))),
                             (FSet.size_fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))](newEFSM),
                               (FSet.size_fset[Nat.nat](S[A](newEFSM)),
                                 Nat.Nata(ss.par.length)))))
                         (resolve_nondeterminism[A](failedMerges, newScores,
             oldEFSM, newa, m, check, np)
                            match {
                            case (None, failedMergesa) =>
                              resolve_nondeterminism[A](Set.insert[(Nat.nat,
                             Nat.nat)]((dest_1, dest_2), failedMergesa),
                 ss, oldEFSM, newEFSM, m, check, np)
                            case (Some(newb), failedMergesa) =>
                              (Some[FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]](newb),
                                failedMergesa)
                          })
                         else (None, failedMerges))
                     }
                 })
              })
}

def merge[A : HOL.equal : Orderings.linorder : Value.aexp_value](failedMerges:
                           Set.set[(Nat.nat, Nat.nat)],
                          e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                          s_1: Nat.nat, s_2: Nat.nat,
                          m: (List[Nat.nat]) =>
                               (List[Nat.nat]) =>
                                 Nat.nat =>
                                   (FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                     (FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                       (FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
 ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]) =>
   Boolean) =>
   Option[FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))]],
                          check:
                            (FSet.fset[((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit])]) =>
                              Boolean,
                          np: (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat),
      ((Transition.transition_ext[A, Unit], List[Nat.nat]),
        (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      (Option[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]],
        Set.set[(Nat.nat, Nat.nat)])
  =
  (if ((Nat.equal_nata(s_1, s_2)) || ((Set.member[(Nat.nat,
            Nat.nat)]((s_1, s_2),
                       failedMerges)) || (Set.member[(Nat.nat,
               Nat.nat)]((s_2, s_1), failedMerges))))
    (None, failedMerges)
    else {
           val ea: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))]
             = make_distinct[A](merge_states[A](s_1, s_2, e));
           resolve_nondeterminism[A](failedMerges,
                                      order_nondeterministic_pairs[A](np(ea)),
                                      e, ea, m, check, np)
         })

def step_score[A](xs: List[(List[Nat.nat], List[Nat.nat])],
                   e: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit]))],
                   s: (List[Nat.nat]) =>
                        (List[Nat.nat]) =>
                          (FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit]))]) =>
                            Nat.nat):
      Nat.nat
  =
  Lista.foldr[(List[Nat.nat], List[Nat.nat]),
               Nat.nat](((a: (List[Nat.nat], List[Nat.nat])) =>
                          {
                            val (id1, id2): (List[Nat.nat], List[Nat.nat]) = a;
                            ((acc: Nat.nat) =>
                              {
                                val score: Nat.nat = ((s(id1))(id2))(e);
                                (if (Nat.equal_nata(score, Nat.zero_nata))
                                  Nat.zero_nata else Nat.plus_nata(score, acc))
                              })
                          }),
                         xs, Nat.zero_nata)

def score_from_list[A](p1: FSet.fset[List[List[Nat.nat]]],
                        p2: FSet.fset[List[List[Nat.nat]]],
                        e: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit]))],
                        s: (List[Nat.nat]) =>
                             (List[Nat.nat]) =>
                               (FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                 Nat.nat):
      Nat.nat
  =
  {
    val pairs: FSet.fset[List[(List[Nat.nat], List[Nat.nat])]] =
      FSet.fimage[(List[List[Nat.nat]], List[List[Nat.nat]]),
                   List[(List[Nat.nat],
                          List[Nat.nat])]](((a:
       (List[List[Nat.nat]], List[List[Nat.nat]]))
      =>
     {
       val (aa, b): (List[List[Nat.nat]], List[List[Nat.nat]]) = a;
       aa.par.zip(b).toList
     }),
    FSet_Utils.fprod[List[List[Nat.nat]], List[List[Nat.nat]]](p1, p2))
    val a: FSet.fset[Nat.nat] =
      FSet.fimage[List[(List[Nat.nat], List[Nat.nat])],
                   Nat.nat](((l: List[(List[Nat.nat], List[Nat.nat])]) =>
                              step_score[A](l, e, s)),
                             pairs);
    FSet_Utils.fSum[Nat.nat](a)
  }

def outgoing_transitions[A](s: Nat.nat,
                             e: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(Nat.nat, (Transition.transition_ext[A, Unit], List[Nat.nat]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
               (Nat.nat,
                 (Transition.transition_ext[A, Unit],
                   List[Nat.nat]))](((a:
(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                                       =>
                                      {
val (uid, aa):
      (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
  = a
val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]) = aa;
({
   val (_, to): (Nat.nat, Nat.nat) = ab;
   ((t: Transition.transition_ext[A, Unit]) => (to, (t, uid)))
 })(b)
                                      }),
                                     FSet.ffilter[(List[Nat.nat],
            ((Nat.nat, Nat.nat),
              Transition.transition_ext[A,
 Unit]))](((a: (List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
             =>
            {
              val (_, aa):
                    (List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
                = a
              val (ab, b):
                    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
                = aa;
              ({
                 val (origin, _): (Nat.nat, Nat.nat) = ab;
                 ((_: Transition.transition_ext[A, Unit]) =>
                   Nat.equal_nata(origin, s))
               })(b)
            }),
           e))

def paths_of_length[A](m: Nat.nat,
                        uu: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                        uv: Nat.nat):
      FSet.fset[List[List[Nat.nat]]]
  =
  (if (Nat.equal_nata(m, Nat.zero_nata))
    FSet.finsert[List[List[Nat.nat]]](Nil, FSet.bot_fset[List[List[Nat.nat]]])
    else {
           val outgoing:
                 FSet.fset[(Nat.nat,
                             (Transition.transition_ext[A, Unit],
                               List[Nat.nat]))]
             = outgoing_transitions[A](uv, uu)
           val a: FSet.fset[List[List[Nat.nat]]] =
             FSet.ffUnion[List[List[Nat.nat]]](FSet.fimage[(Nat.nat,
                     (Transition.transition_ext[A, Unit], List[Nat.nat])),
                    FSet.fset[List[List[Nat.nat]]]](((a:
                (Nat.nat, (Transition.transition_ext[A, Unit], List[Nat.nat])))
               =>
              {
                val (d, (_, id)):
                      (Nat.nat,
                        (Transition.transition_ext[A, Unit], List[Nat.nat]))
                  = a;
                FSet.fimage[List[List[Nat.nat]],
                             List[List[Nat.nat]]](((aa: List[List[Nat.nat]]) =>
            id :: aa),
           paths_of_length[A](Nat.minus_nat(m, Nat.Nata((1))), uu, d))
              }),
             outgoing));
           FSet.ffilter[List[List[Nat.nat]]](((l: List[List[Nat.nat]]) =>
       Nat.equal_nata(Nat.Nata(l.par.length),
                       Nat.Suc(Nat.minus_nat(m, Nat.Nata((1)))))),
      a)
         })

def k_score[A](k: Nat.nat,
                e: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))],
                strat:
                  (List[Nat.nat]) =>
                    (List[Nat.nat]) =>
                      (FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit]))]) =>
                        Nat.nat):
      FSet.fset[score_ext[Unit]]
  =
  {
    val states: FSet.fset[Nat.nat] = S[A](e)
    val pairs_to_score: FSet.fset[(Nat.nat, Nat.nat)] =
      FSet.ffilter[(Nat.nat,
                     Nat.nat)](((a: (Nat.nat, Nat.nat)) =>
                                 {
                                   val (aa, b): (Nat.nat, Nat.nat) = a;
                                   Nat.less_nat(aa, b)
                                 }),
                                FSet_Utils.fprod[Nat.nat,
          Nat.nat](states, states))
    val paths:
          FSet.fset[(Nat.nat,
                      (Nat.nat,
                        (FSet.fset[List[List[Nat.nat]]],
                          FSet.fset[List[List[Nat.nat]]])))]
      = FSet.fimage[(Nat.nat, Nat.nat),
                     (Nat.nat,
                       (Nat.nat,
                         (FSet.fset[List[List[Nat.nat]]],
                           FSet.fset[List[List[Nat.nat]]])))](((a:
                          (Nat.nat, Nat.nat))
                         =>
                        {
                          val (s1, s2): (Nat.nat, Nat.nat) = a;
                          (s1, (s2, (paths_of_length[A](k, e, s1),
                                      paths_of_length[A](k, e, s2))))
                        }),
                       pairs_to_score)
    val a: FSet.fset[score_ext[Unit]] =
      FSet.fimage[(Nat.nat,
                    (Nat.nat,
                      (FSet.fset[List[List[Nat.nat]]],
                        FSet.fset[List[List[Nat.nat]]]))),
                   score_ext[Unit]](((a:
(Nat.nat,
  (Nat.nat, (FSet.fset[List[List[Nat.nat]]], FSet.fset[List[List[Nat.nat]]]))))
                                       =>
                                      {
val (s1, (s2, (p1, p2))):
      (Nat.nat,
        (Nat.nat,
          (FSet.fset[List[List[Nat.nat]]], FSet.fset[List[List[Nat.nat]]])))
  = a;
score_exta[Unit](score_from_list[A](p1, p2, e, strat), s1, s2, ())
                                      }),
                                     paths);
    FSet.ffilter[score_ext[Unit]](((x: score_ext[Unit]) =>
                                    Nat.less_nat(Nat.zero_nata,
          Score[Unit](x))),
                                   a)
  }

def max_int[A : Value.aexp_value](e: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      Int.int
  =
  EFSM.max_int[A](tm[A](e))

def max_reg[A](e: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit]))]):
      Option[Nat.nat]
  =
  EFSM.max_reg[A](tm[A](e))

def max_uid[A](e: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit]))]):
      Option[Nat.nat]
  =
  {
    val uidsa: FSet.fset[Nat.nat] = uids[A](e);
    (if (FSet.equal_fseta[Nat.nat](uidsa, FSet.bot_fset[Nat.nat])) None
      else Some[Nat.nat](FSet.fMax[Nat.nat](uidsa)))
  }

def score_state_pair[A](strat:
                          (List[Nat.nat]) =>
                            (List[Nat.nat]) =>
                              (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                Nat.nat,
                         e: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                         s1: Nat.nat, s2: Nat.nat):
      Nat.nat
  =
  {
    val t1: FSet.fset[(Nat.nat,
                        (Transition.transition_ext[A, Unit], List[Nat.nat]))]
      = outgoing_transitions[A](s1, e)
    val t2: FSet.fset[(Nat.nat,
                        (Transition.transition_ext[A, Unit], List[Nat.nat]))]
      = outgoing_transitions[A](s2, e);
    FSet_Utils.fSum[Nat.nat](FSet.fimage[((Nat.nat,
    (Transition.transition_ext[A, Unit], List[Nat.nat])),
   (Nat.nat, (Transition.transition_ext[A, Unit], List[Nat.nat]))),
  Nat.nat](((a: ((Nat.nat, (Transition.transition_ext[A, Unit], List[Nat.nat])),
                  (Nat.nat,
                    (Transition.transition_ext[A, Unit], List[Nat.nat]))))
              =>
             {
               val (aa, b):
                     ((Nat.nat,
                        (Transition.transition_ext[A, Unit], List[Nat.nat])),
                       (Nat.nat,
                         (Transition.transition_ext[A, Unit], List[Nat.nat])))
                 = a;
               ({
                  val (_, (_, t1a)):
                        (Nat.nat,
                          (Transition.transition_ext[A, Unit], List[Nat.nat]))
                    = aa;
                  ((ab: (Nat.nat,
                          (Transition.transition_ext[A, Unit], List[Nat.nat])))
                     =>
                    {
                      val (_, (_, t2a)):
                            (Nat.nat,
                              (Transition.transition_ext[A, Unit],
                                List[Nat.nat]))
                        = ab;
                      ((strat(t1a))(t2a))(e)
                    })
                })(b)
             }),
            FSet_Utils.fprod[(Nat.nat,
                               (Transition.transition_ext[A, Unit],
                                 List[Nat.nat])),
                              (Nat.nat,
                                (Transition.transition_ext[A, Unit],
                                  List[Nat.nat]))](t1, t2)))
  }

def score_1[A](e: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit]))],
                strat:
                  (List[Nat.nat]) =>
                    (List[Nat.nat]) =>
                      (FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit]))]) =>
                        Nat.nat):
      FSet.fset[score_ext[Unit]]
  =
  {
    val states: FSet.fset[Nat.nat] = S[A](e)
    val pairs_to_score: FSet.fset[(Nat.nat, Nat.nat)] =
      FSet.ffilter[(Nat.nat,
                     Nat.nat)](((a: (Nat.nat, Nat.nat)) =>
                                 {
                                   val (aa, b): (Nat.nat, Nat.nat) = a;
                                   Nat.less_nat(aa, b)
                                 }),
                                FSet_Utils.fprod[Nat.nat,
          Nat.nat](states, states))
    val a: FSet.fset[score_ext[Unit]] =
      FSet.fimage[(Nat.nat, Nat.nat),
                   score_ext[Unit]](((a: (Nat.nat, Nat.nat)) =>
                                      {
val (s1, s2): (Nat.nat, Nat.nat) = a;
score_exta[Unit](score_state_pair[A](strat, e, s1, s2), s1, s2, ())
                                      }),
                                     pairs_to_score);
    FSet.ffilter[score_ext[Unit]](((x: score_ext[Unit]) =>
                                    Nat.less_nat(Nat.zero_nata,
          Score[Unit](x))),
                                   a)
  }

def all_regs[A](e: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))]):
      Set.set[Nat.nat]
  =
  EFSM.all_regs[A](tm[A](e))

def max_uid_total[A](e: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  (max_uid[A](e) match {
     case None => Nat.zero_nata
     case Some(u) => u
   })

def make_outputs[A](x0: List[A]): List[AExp.aexp[VName.vname, A]] = x0 match {
  case Nil => Nil
  case h :: t => AExp.L[A, VName.vname](h) :: make_outputs[A](t)
}

def make_guard[A](x0: List[A], uu: Nat.nat): List[GExp.gexp[VName.vname, A]] =
  (x0, uu) match {
  case (Nil, uu) => Nil
  case (h :: t, n) =>
    GExp.Eq[VName.vname,
             A](AExp.V[VName.vname, A](VName.I(n)),
                 AExp.L[A, VName.vname](h)) ::
      make_guard[A](t, Nat.plus_nata(n, Nat.Nata((1))))
}

def add_transition[A : HOL.equal](e: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                   s: Nat.nat, label: String, inputs: List[A],
                                   outputs: List[A]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  FSet.finsert[(List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[A,
      Unit]))]((List(Nat.plus_nata(max_uid_total[A](e), Nat.Nata((1)))),
                 ((s, Nat.plus_nata(EFSM.maxS[A](tm[A](e)), Nat.Nata((1)))),
                   Transition.transition_exta[A,
       Unit](label, Nat.Nata(inputs.par.length),
              make_guard[A](inputs, Nat.zero_nata), make_outputs[A](outputs),
              Nil, ()))),
                e)

def make_branch[A : HOL.equal : Value.aexp_value](e:
            FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))],
           uu: Nat.nat, uv: Map[Nat.nat, Option[A]],
           x3: List[(String, (List[A], List[A]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (e, uu, uv, x3) match {
  case (e, uu, uv, Nil) => e
  case (e, s, r, (label, (inputs, outputs)) :: t) =>
    (EFSM.step[A](tm[A](e), s, r, label, inputs) match {
       case None =>
         make_branch[A](add_transition[A](e, s, label, inputs, outputs),
                         Nat.plus_nata(EFSM.maxS[A](tm[A](e)), Nat.Nata((1))),
                         r, t)
       case Some((_, (sa, (outputsa, updated)))) =>
         (if (Lista.equal_lista[Option[A]](outputsa,
    Lista.map[A, Option[A]](((a: A) => Some[A](a)), outputs)))
           make_branch[A](e, sa, updated, t)
           else make_branch[A](add_transition[A](e, s, label, inputs, outputs),
                                Nat.plus_nata(EFSM.maxS[A](tm[A](e)),
       Nat.Nata((1))),
                                r, t))
     })
}

def make_pta_aux[A : HOL.equal : Orderings.order : Value.aexp_value](l:
                               List[List[(String, (List[A], List[A]))]],
                              e: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  Lista.fold[List[(String, (List[A], List[A]))],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit]))]](((h: List[(String, (List[A], List[A]))]) =>
                           (ea: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
                             =>
                           make_branch[A](ea, Nat.zero_nata,
   AExp.null_state[Nat.nat, Option[A]], h)),
                          l, e)

def make_pta[A : HOL.equal : Orderings.order : Value.aexp_value](log:
                           List[List[(String, (List[A], List[A]))]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  make_pta_aux[A](log, FSet.bot_fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit]))])

def i_possible_steps[A : HOL.equal : Value.aexp_value](e:
                 FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[A, Unit]))],
                s: Nat.nat, r: Map[Nat.nat, Option[A]], l: String, i: List[A]):
      FSet.fset[(List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
               (List[Nat.nat],
                 (Nat.nat,
                   Transition.transition_ext[A,
      Unit]))](((a: (List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                  =>
                 {
                   val (uid, aa):
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))
                     = a
                   val (ab, b):
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit])
                     = aa;
                   ({
                      val (_, dest): (Nat.nat, Nat.nat) = ab;
                      ((t: Transition.transition_ext[A, Unit]) =>
                        (uid, (dest, t)))
                    })(b)
                 }),
                FSet.ffilter[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A,
                    Unit]))](((a: (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit])))
                                =>
                               {
                                 val (_, aa):
                                       (List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
                                   = a
                                 val (ab, b):
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit])
                                   = aa;
                                 ({
                                    val (origin, _): (Nat.nat, Nat.nat) = ab;
                                    ((t: Transition.transition_ext[A, Unit]) =>
                                      (Nat.equal_nata(origin,
               s)) && ((Transition.Label[A, Unit](t) ==
                         l) && ((Nat.equal_nata(Nat.Nata(i.par.length),
         Transition.Arity[A, Unit](t))) && (GExp.apply_guards[A](Transition.Guards[A,
    Unit](t),
                          AExp.join_ir[A](i, r))))))
                                  })(b)
                               }),
                              e))

def test_trace[A : HOL.equal : Value.aexp_value](x0:
           List[(String, (List[A], List[A]))],
          uu: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))],
          uv: Nat.nat, uw: Map[Nat.nat, Option[A]]):
      (List[(String,
              (List[A],
                (Nat.nat,
                  (Nat.nat,
                    (Map[Nat.nat, Option[A]],
                      (List[Nat.nat], (List[A], List[Option[A]])))))))],
        List[(String, (List[A], List[A]))])
  =
  (x0, uu, uv, uw) match {
  case (Nil, uu, uv, uw) => (Nil, Nil)
  case ((l, (i, expected)) :: es, e, s, r) =>
    {
      val ps: FSet.fset[(List[Nat.nat],
                          (Nat.nat, Transition.transition_ext[A, Unit]))]
        = i_possible_steps[A](e, s, r, l, i);
      (if (FSet_Utils.fis_singleton[(List[Nat.nat],
                                      (Nat.nat,
Transition.transition_ext[A, Unit]))](ps))
        {
          val (id, (sa, t)):
                (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))
            = FSet.fthe_elem[(List[Nat.nat],
                               (Nat.nat,
                                 Transition.transition_ext[A, Unit]))](ps)
          val ra: Map[Nat.nat, Option[A]] =
            (Transition.apply_updates[A](Transition.Updates[A, Unit](t),
  AExp.join_ir[A](i, r))).apply(r)
          val actual: List[Option[A]] =
            Transition.apply_outputs[A](Transition.Outputs[A, Unit](t),
 AExp.join_ir[A](i, r))
          val a: (List[(String,
                         (List[A],
                           (Nat.nat,
                             (Nat.nat,
                               (Map[Nat.nat, Option[A]],
                                 (List[Nat.nat],
                                   (List[A], List[Option[A]])))))))],
                   List[(String, (List[A], List[A]))])
            = test_trace[A](es, e, sa, ra)
          val (est, aa):
                (List[(String,
                        (List[A],
                          (Nat.nat,
                            (Nat.nat,
                              (Map[Nat.nat, Option[A]],
                                (List[Nat.nat],
                                  (List[A], List[Option[A]])))))))],
                  List[(String, (List[A], List[A]))])
            = a;
          ((l, (i, (s, (sa, (r, (id, (expected, actual))))))) :: est, aa)
        }
        else (Nil, (l, (i, expected)) :: es))
    }
}

def test_log[A : HOL.equal : Orderings.order : Value.aexp_value](l:
                           List[List[(String, (List[A], List[A]))]],
                          e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      List[(List[(String,
                   (List[A],
                     (Nat.nat,
                       (Nat.nat,
                         (Map[Nat.nat, Option[A]],
                           (List[Nat.nat], (List[A], List[Option[A]])))))))],
             List[(String, (List[A], List[A]))])]
  =
  Lista.map[List[(String, (List[A], List[A]))],
             (List[(String,
                     (List[A],
                       (Nat.nat,
                         (Nat.nat,
                           (Map[Nat.nat, Option[A]],
                             (List[Nat.nat], (List[A], List[Option[A]])))))))],
               List[(String,
                      (List[A],
                        List[A]))])](((t: List[(String, (List[A], List[A]))]) =>
                                       test_trace[A](t, e, Nat.zero_nata,
              AExp.null_state[Nat.nat, Option[A]])),
                                      l)

def get_by_ids[A](e: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[A, Unit]))],
                   uid: List[Nat.nat]):
      Transition.transition_ext[A, Unit]
  =
  (Fun.comp[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]),
             Transition.transition_ext[A, Unit],
             (List[Nat.nat],
               ((Nat.nat, Nat.nat),
                 Transition.transition_ext[A,
    Unit]))](((a: ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])) =>
               a._2),
              ((a: (List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                 =>
                a._2))).apply(FSet.fthe_elem[(List[Nat.nat],
       ((Nat.nat, Nat.nat),
         Transition.transition_ext[A, Unit]))](FSet.ffilter[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A,
           Unit]))](((a: (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit])))
                       =>
                      {
                        val (tids, _):
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit]))
                          = a;
                        Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
             Set.seta[Nat.nat](tids))
                      }),
                     e)))

def replace_transition[A](e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                           uid: List[Nat.nat],
                           newa: Transition.transition_ext[A, Unit]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[A,
      Unit]))](((a: (List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                  =>
                 {
                   val (uids, aa):
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))
                     = a
                   val (ab, b):
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit])
                     = aa;
                   ({
                      val (from, to): (Nat.nat, Nat.nat) = ab;
                      ((t: Transition.transition_ext[A, Unit]) =>
                        (if (Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                  Set.seta[Nat.nat](uids)))
                          (uids, ((from, to), newa))
                          else (uids, ((from, to), t))))
                    })(b)
                 }),
                e)

def replace_all[A](e: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit]))],
                    ids: List[List[Nat.nat]],
                    newa: Transition.transition_ext[A, Unit]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  Lista.fold[List[Nat.nat],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit]))]](((id: List[Nat.nat]) =>
                           (acc: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
                             =>
                           replace_transition[A](acc, id, newa)),
                          ids, e)

def max_reg_total[A](e: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  (max_reg[A](e) match {
     case None => Nat.zero_nata
     case Some(r) => r
   })

def null_modifier[A](f: List[Nat.nat], uu: List[Nat.nat], uv: Nat.nat,
                      uw: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit]))],
                      ux: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit]))],
                      uy: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit]))],
                      uz: (FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[A, Unit])]) =>
                            Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  None

def inference_step[A : HOL.equal : Orderings.linorder : Value.aexp_value](failedMerges:
                                    Set.set[(Nat.nat, Nat.nat)],
                                   e: FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                   s: FSet.fset[score_ext[Unit]],
                                   m: (List[Nat.nat]) =>
(List[Nat.nat]) =>
  Nat.nat =>
    (FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat),
                     Transition.transition_ext[A, Unit]))]) =>
        (FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[A, Unit]))]) =>
          ((FSet.fset[((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit])]) =>
            Boolean) =>
            Option[FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))]],
                                   check:
                                     (FSet.fset[((Nat.nat, Nat.nat),
          Transition.transition_ext[A, Unit])]) =>
                                       Boolean,
                                   np: (FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
 FSet.fset[(Nat.nat,
             ((Nat.nat, Nat.nat),
               ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      (Option[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]],
        Set.set[(Nat.nat, Nat.nat)])
  =
  (if (FSet.equal_fseta[score_ext[Unit]](s, FSet.bot_fset[score_ext[Unit]]))
    (None, failedMerges)
    else {
           val h: score_ext[Unit] = FSet.fMin[score_ext[Unit]](s)
           val t: FSet.fset[score_ext[Unit]] =
             FSet_Utils.fremove[score_ext[Unit]](h, s);
           (merge[A](failedMerges, e, S1[Unit](h), S2[Unit](h), m, check, np)
              match {
              case (None, failedMergesa) =>
                inference_step[A](Set.insert[(Nat.nat,
       Nat.nat)]((S1[Unit](h), S2[Unit](h)), failedMergesa),
                                   e, t, m, check, np)
              case (Some(newa), failedMergesa) =>
                (Some[FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A,
                       Unit]))]](newa),
                  failedMergesa)
            })
         })

def nondeterministic[A : HOL.equal](t: FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                     np: (FSet.fset[(List[Nat.nat],
              ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
   FSet.fset[(Nat.nat,
               ((Nat.nat, Nat.nat),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      Boolean
  =
  ! (deterministic[A](t, np))

def replace_transitions[A](e: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                            ts: List[(List[Nat.nat],
                                       Transition.transition_ext[A, Unit])]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  Lista.fold[(List[Nat.nat], Transition.transition_ext[A, Unit]),
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit]))]](((a: (List[Nat.nat],
                                Transition.transition_ext[A, Unit]))
                            =>
                           {
                             val (uid, newa):
                                   (List[Nat.nat],
                                     Transition.transition_ext[A, Unit])
                               = a;
                             ((acc: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
                                =>
                               replace_transition[A](acc, uid, newa))
                           }),
                          ts, e)

def state_nondeterminism[A : HOL.equal](og: Nat.nat,
 nt: FSet.fset[(Nat.nat, (Transition.transition_ext[A, Unit], List[Nat.nat]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (Transition.transition_ext[A, Unit], List[Nat.nat]))))]
  =
  (if (Nat.less_nat(FSet.size_fset[(Nat.nat,
                                     (Transition.transition_ext[A, Unit],
                                       List[Nat.nat]))](nt),
                     Code_Numeral.nat_of_integer(BigInt(2))))
    FSet.bot_fset[(Nat.nat,
                    ((Nat.nat, Nat.nat),
                      ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                        (Transition.transition_ext[A, Unit], List[Nat.nat]))))]
    else FSet.ffUnion[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                            (Transition.transition_ext[A, Unit],
                              List[Nat.nat]))))](FSet.fimage[(Nat.nat,
                       (Transition.transition_ext[A, Unit], List[Nat.nat])),
                      FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    ((Transition.transition_ext[A, Unit],
                                       List[Nat.nat]),
                                      (Transition.transition_ext[A, Unit],
List[Nat.nat]))))]](((x: (Nat.nat,
                           (Transition.transition_ext[A, Unit], List[Nat.nat])))
                       =>
                      {
                        val (dest, t):
                              (Nat.nat,
                                (Transition.transition_ext[A, Unit],
                                  List[Nat.nat]))
                          = x;
                        FSet.fimage[(Nat.nat,
                                      (Transition.transition_ext[A, Unit],
List[Nat.nat])),
                                     (Nat.nat,
                                       ((Nat.nat, Nat.nat),
 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
   (Transition.transition_ext[A, Unit],
     List[Nat.nat]))))](((y: (Nat.nat,
                               (Transition.transition_ext[A, Unit],
                                 List[Nat.nat])))
                           =>
                          {
                            val (desta, ta):
                                  (Nat.nat,
                                    (Transition.transition_ext[A, Unit],
                                      List[Nat.nat]))
                              = y;
                            (og, ((dest, desta), (t, ta)))
                          }),
                         FSet_Utils.fremove[(Nat.nat,
      (Transition.transition_ext[A, Unit], List[Nat.nat]))](x, nt))
                      }),
                     nt)))

def try_heuristics_check[A](uu: (FSet.fset[((Nat.nat, Nat.nat),
     Transition.transition_ext[A, Unit])]) =>
                                  Boolean,
                             x1: List[(List[Nat.nat]) =>
(List[Nat.nat]) =>
  Nat.nat =>
    (FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat),
                     Transition.transition_ext[A, Unit]))]) =>
        (FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[A, Unit]))]) =>
          ((FSet.fset[((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit])]) =>
            Boolean) =>
            Option[FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))]]]):
      (List[Nat.nat]) =>
        (List[Nat.nat]) =>
          Nat.nat =>
            (FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]) =>
              (FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))]) =>
                (FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[A, Unit]))]) =>
                  ((FSet.fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit])]) =>
                    Boolean) =>
                    Option[FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit]))]]
  =
  (uu, x1) match {
  case (uu, Nil) =>
    ((a: List[Nat.nat]) => (b: List[Nat.nat]) => (c: Nat.nat) =>
      (d: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))])
        =>
      (e: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))])
        =>
      (f: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))])
        =>
      (g: (FSet.fset[((Nat.nat, Nat.nat),
                       Transition.transition_ext[A, Unit])]) =>
            Boolean)
        =>
      null_modifier[A](a, b, c, d, e, f, g))
  case (check, h :: t) =>
    ((a: List[Nat.nat]) => (b: List[Nat.nat]) => (c: Nat.nat) =>
      (d: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))])
        =>
      (e: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))])
        =>
      (f: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))])
        =>
      (ch: (FSet.fset[((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit])]) =>
             Boolean)
        =>
      (((((((h(a))(b))(c))(d))(e))(f))(ch) match {
         case None =>
           (try_heuristics_check[A](check,
                                     t)).apply(a).apply(b).apply(c).apply(d).apply(e).apply(f).apply(ch)
         case Some(aa) =>
           Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit]))]](aa)
       }))
}

def nondeterministic_pairs[A : HOL.equal : Value.aexp_value](t:
                       FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (Transition.transition_ext[A, Unit], List[Nat.nat]))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (Transition.transition_ext[A, Unit],
                       List[Nat.nat]))))](((a:
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (Transition.transition_ext[A, Unit], List[Nat.nat])))))
     =>
    {
      val (_, aa):
            (Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (Transition.transition_ext[A, Unit], List[Nat.nat]))))
        = a
      val (_, ab):
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                (Transition.transition_ext[A, Unit], List[Nat.nat])))
        = aa
      val (ac, b):
            ((Transition.transition_ext[A, Unit], List[Nat.nat]),
              (Transition.transition_ext[A, Unit], List[Nat.nat]))
        = ab;
      ({
         val (ta, _): (Transition.transition_ext[A, Unit], List[Nat.nat]) = ac;
         ((ad: (Transition.transition_ext[A, Unit], List[Nat.nat])) =>
           {
             val (taa, _): (Transition.transition_ext[A, Unit], List[Nat.nat]) =
               ad;
             (Transition.Label[A, Unit](ta) ==
               Transition.Label[A, Unit](taa)) && ((Nat.equal_nata(Transition.Arity[A,
     Unit](ta),
                            Transition.Arity[A,
      Unit](taa))) && (EFSM.choice[A](ta, taa)))
           })
       })(b)
    }),
   FSet.ffUnion[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (Transition.transition_ext[A, Unit],
                        List[Nat.nat]))))](FSet.fimage[Nat.nat,
                FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              ((Transition.transition_ext[A, Unit],
                                 List[Nat.nat]),
                                (Transition.transition_ext[A, Unit],
                                  List[Nat.nat]))))]](((s: Nat.nat) =>
                state_nondeterminism[A](s, outgoing_transitions[A](s, t))),
               S[A](t))))

def nondeterministic_pairs_labar[A : HOL.equal : Value.aexp_value](t:
                             FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (Transition.transition_ext[A, Unit], List[Nat.nat]))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (Transition.transition_ext[A, Unit],
                       List[Nat.nat]))))](((a:
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (Transition.transition_ext[A, Unit], List[Nat.nat])))))
     =>
    {
      val (_, aa):
            (Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (Transition.transition_ext[A, Unit], List[Nat.nat]))))
        = a
      val (ab, b):
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                (Transition.transition_ext[A, Unit], List[Nat.nat])))
        = aa;
      ({
         val (_, _): (Nat.nat, Nat.nat) = ab;
         ((ac: ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (Transition.transition_ext[A, Unit], List[Nat.nat])))
            =>
           {
             val (ad, ba):
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (Transition.transition_ext[A, Unit], List[Nat.nat]))
               = ac;
             ({
                val (ta, _): (Transition.transition_ext[A, Unit], List[Nat.nat])
                  = ad;
                ((ae: (Transition.transition_ext[A, Unit], List[Nat.nat])) =>
                  {
                    val (taa, _):
                          (Transition.transition_ext[A, Unit], List[Nat.nat])
                      = ae;
                    (Transition.Label[A, Unit](ta) ==
                      Transition.Label[A,
Unit](taa)) && ((Nat.equal_nata(Transition.Arity[A, Unit](ta),
                                 Transition.Arity[A,
           Unit](taa))) && ((EFSM.choice[A](ta,
     taa)) || (Lista.equal_lista[AExp.aexp[VName.vname,
    A]](Transition.Outputs[A, Unit](ta), Transition.Outputs[A, Unit](taa)))))
                  })
              })(ba)
           })
       })(b)
    }),
   FSet.ffUnion[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (Transition.transition_ext[A, Unit],
                        List[Nat.nat]))))](FSet.fimage[Nat.nat,
                FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              ((Transition.transition_ext[A, Unit],
                                 List[Nat.nat]),
                                (Transition.transition_ext[A, Unit],
                                  List[Nat.nat]))))]](((s: Nat.nat) =>
                state_nondeterminism[A](s, outgoing_transitions[A](s, t))),
               S[A](t))))

def nondeterministic_pairs_labar_dest[A : HOL.equal : Value.aexp_value](t:
                                  FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (Transition.transition_ext[A, Unit], List[Nat.nat]))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (Transition.transition_ext[A, Unit],
                       List[Nat.nat]))))](((a:
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (Transition.transition_ext[A, Unit], List[Nat.nat])))))
     =>
    {
      val (_, aa):
            (Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (Transition.transition_ext[A, Unit], List[Nat.nat]))))
        = a
      val (ab, b):
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                (Transition.transition_ext[A, Unit], List[Nat.nat])))
        = aa;
      ({
         val (d, da): (Nat.nat, Nat.nat) = ab;
         ((ac: ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (Transition.transition_ext[A, Unit], List[Nat.nat])))
            =>
           {
             val (ad, ba):
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (Transition.transition_ext[A, Unit], List[Nat.nat]))
               = ac;
             ({
                val (ta, _): (Transition.transition_ext[A, Unit], List[Nat.nat])
                  = ad;
                ((ae: (Transition.transition_ext[A, Unit], List[Nat.nat])) =>
                  {
                    val (taa, _):
                          (Transition.transition_ext[A, Unit], List[Nat.nat])
                      = ae;
                    (Transition.Label[A, Unit](ta) ==
                      Transition.Label[A,
Unit](taa)) && ((Nat.equal_nata(Transition.Arity[A, Unit](ta),
                                 Transition.Arity[A,
           Unit](taa))) && ((EFSM.choice[A](ta,
     taa)) || ((Lista.equal_lista[AExp.aexp[VName.vname,
     A]](Transition.Outputs[A, Unit](ta),
          Transition.Outputs[A, Unit](taa))) && (Nat.equal_nata(d, da)))))
                  })
              })(ba)
           })
       })(b)
    }),
   FSet.ffUnion[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (Transition.transition_ext[A, Unit],
                        List[Nat.nat]))))](FSet.fimage[Nat.nat,
                FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              ((Transition.transition_ext[A, Unit],
                                 List[Nat.nat]),
                                (Transition.transition_ext[A, Unit],
                                  List[Nat.nat]))))]](((s: Nat.nat) =>
                state_nondeterminism[A](s, outgoing_transitions[A](s, t))),
               S[A](t))))

} /* object Inference */

object EFSM {

def S[A](m: FSet.fset[((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit])]):
      FSet.fset[Nat.nat]
  =
  FSet.sup_fset[Nat.nat](FSet.fimage[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[A, Unit]),
                                      Nat.nat](((a:
           ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
          =>
         {
           val (aa, b): ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
             = a;
           ({
              val (s, _): (Nat.nat, Nat.nat) = aa;
              ((_: Transition.transition_ext[A, Unit]) => s)
            })(b)
         }),
        m),
                          FSet.fimage[((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit]),
                                       Nat.nat](((a:
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
           =>
          {
            val (aa, b):
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
              = a;
            ({
               val (_, s): (Nat.nat, Nat.nat) = aa;
               ((_: Transition.transition_ext[A, Unit]) => s)
             })(b)
          }),
         m))

def maxS[A : HOL.equal](t: FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[A, Unit])]):
      Nat.nat
  =
  (if (FSet.equal_fseta[((Nat.nat, Nat.nat),
                          Transition.transition_ext[A,
             Unit])](t, FSet.bot_fset[((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit])]))
    Nat.zero_nata
    else FSet.fMax[Nat.nat](FSet.sup_fset[Nat.nat](FSet.fimage[((Nat.nat,
                          Nat.nat),
                         Transition.transition_ext[A, Unit]),
                        Nat.nat](((a: ((Nat.nat, Nat.nat),
Transition.transition_ext[A, Unit]))
                                    =>
                                   {
                                     val (aa, b):
   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
                                       = a;
                                     ({
val (origin, _): (Nat.nat, Nat.nat) = aa;
((_: Transition.transition_ext[A, Unit]) => origin)
                                      })(b)
                                   }),
                                  t),
            FSet.fimage[((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]),
                         Nat.nat](((a: ((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit]))
                                     =>
                                    {
                                      val
(aa, b): ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]) = a;
                                      ({
 val (_, dest): (Nat.nat, Nat.nat) = aa;
 ((_: Transition.transition_ext[A, Unit]) => dest)
                                       })(b)
                                    }),
                                   t))))

def possible_steps[A : HOL.equal : Value.aexp_value](e:
               FSet.fset[((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit])],
              s: Nat.nat, r: Map[Nat.nat, Option[A]], l: String, i: List[A]):
      FSet.fset[(Nat.nat, Transition.transition_ext[A, Unit])]
  =
  FSet.fimage[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]),
               (Nat.nat,
                 Transition.transition_ext[A,
    Unit])](((a: ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])) =>
              {
                val (aa, b):
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
                  = a;
                ({
                   val (_, ab): (Nat.nat, Nat.nat) = aa;
                   ((ba: Transition.transition_ext[A, Unit]) => (ab, ba))
                 })(b)
              }),
             FSet.ffilter[((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit])](((a: ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit]))
                          =>
                         {
                           val (aa, b):
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[A, Unit])
                             = a;
                           ({
                              val (origin, _): (Nat.nat, Nat.nat) = aa;
                              ((t: Transition.transition_ext[A, Unit]) =>
                                (Nat.equal_nata(origin,
         s)) && ((Transition.Label[A, Unit](t) ==
                   l) && ((Nat.equal_nata(Nat.Nata(i.par.length),
   Transition.Arity[A, Unit](t))) && (GExp.apply_guards[A](Transition.Guards[A,
                                      Unit](t),
                    AExp.join_ir[A](i, r))))))
                            })(b)
                         }),
                        e))

def step[A : HOL.equal : Value.aexp_value](e:
     FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])],
    s: Nat.nat, r: Map[Nat.nat, Option[A]], l: String, i: List[A]):
      Option[(Transition.transition_ext[A, Unit],
               (Nat.nat, (List[Option[A]], Map[Nat.nat, Option[A]])))]
  =
  (Dirties.randomMember[(Nat.nat,
                          Transition.transition_ext[A,
             Unit])](possible_steps[A](e, s, r, l, i))
     match {
     case None => None
     case Some((sa, t)) =>
       Some[(Transition.transition_ext[A, Unit],
              (Nat.nat,
                (List[Option[A]],
                  Map[Nat.nat, Option[A]])))]((t,
        (sa, (Transition.apply_outputs[A](Transition.Outputs[A, Unit](t),
   AExp.join_ir[A](i, r)),
               (Transition.apply_updates[A](Transition.Updates[A, Unit](t),
     AExp.join_ir[A](i, r))).apply(r)))))
   })

def choice[A : HOL.equal : Value.aexp_value](ta:
       Transition.transition_ext[A, Unit],
      t: Transition.transition_ext[A, Unit]):
      Boolean
  =
  Code_Generation.choice_cases[A](ta, t)

def enumerate_ints[A : Value.aexp_value](e:
   FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]):
      Set.set[Int.int]
  =
  Complete_Lattices.Sup_set[Int.int](Set.image[((Nat.nat, Nat.nat),
         Transition.transition_ext[A, Unit]),
        Set.set[Int.int]](((a: ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))
                             =>
                            {
                              val (_, aa):
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit])
                                = a;
                              Transition.enumerate_ints[A](aa)
                            }),
                           FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[A, Unit])](e)))

def max_int[A : Value.aexp_value](e: FSet.fset[((Nat.nat, Nat.nat),
         Transition.transition_ext[A, Unit])]):
      Int.int
  =
  Lattices_Big.Max[Int.int](Set.insert[Int.int](Int.zero_int,
         enumerate_ints[A](e)))

def max_reg[A](e: FSet.fset[((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit])]):
      Option[Nat.nat]
  =
  {
    val maxes: FSet.fset[Option[Nat.nat]] =
      FSet.fimage[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]),
                   Option[Nat.nat]](((a:
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
                                       =>
                                      {
val (_, aa): ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]) = a;
Transition.max_reg[A](aa)
                                      }),
                                     e);
    (if (FSet.equal_fseta[Option[Nat.nat]](maxes,
    FSet.bot_fset[Option[Nat.nat]]))
      None else FSet.fMax[Option[Nat.nat]](maxes))
  }

def all_regs[A](e: FSet.fset[((Nat.nat, Nat.nat),
                               Transition.transition_ext[A, Unit])]):
      Set.set[Nat.nat]
  =
  Complete_Lattices.Sup_set[Nat.nat](Set.image[((Nat.nat, Nat.nat),
         Transition.transition_ext[A, Unit]),
        Set.set[Nat.nat]](((a: ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))
                             =>
                            {
                              val (_, aa):
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit])
                                = a;
                              Transition.enumerate_regs[A](aa)
                            }),
                           FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[A, Unit])](e)))

def accepts_trace_prim[A : HOL.equal : Value.aexp_value](uu:
                   FSet.fset[((Nat.nat, Nat.nat),
                               Transition.transition_ext[A, Unit])],
                  uv: Nat.nat, uw: Map[Nat.nat, Option[A]],
                  x3: List[(String, (List[A], List[A]))]):
      Boolean
  =
  (uu, uv, uw, x3) match {
  case (uu, uv, uw, Nil) => true
  case (e, s, d, (l, (i, p)) :: t) =>
    {
      val poss_steps: FSet.fset[(Nat.nat, Transition.transition_ext[A, Unit])] =
        possible_steps[A](e, s, d, l, i);
      (if (FSet_Utils.fis_singleton[(Nat.nat,
                                      Transition.transition_ext[A,
                         Unit])](poss_steps))
        {
          val (sa, ta): (Nat.nat, Transition.transition_ext[A, Unit]) =
            FSet.fthe_elem[(Nat.nat,
                             Transition.transition_ext[A, Unit])](poss_steps);
          (if (Lista.equal_lista[Option[A]](Transition.apply_outputs[A](Transition.Outputs[A,
            Unit](ta),
                                 AExp.join_ir[A](i, d)),
     Lista.map[A, Option[A]](((a: A) => Some[A](a)), p)))
            accepts_trace_prim[A](e, sa,
                                   (Transition.apply_updates[A](Transition.Updates[A,
    Unit](ta),
                         AExp.join_ir[A](i, d))).apply(d),
                                   t)
            else false)
        }
        else FSet.fBex[(Nat.nat,
                         Transition.transition_ext[A,
            Unit])](poss_steps,
                     ((a: (Nat.nat, Transition.transition_ext[A, Unit])) =>
                       {
                         val (sa, ta):
                               (Nat.nat, Transition.transition_ext[A, Unit])
                           = a;
                         (Lista.equal_lista[Option[A]](Transition.apply_outputs[A](Transition.Outputs[A,
                       Unit](ta),
    AExp.join_ir[A](i, d)),
                Lista.map[A, Option[A]](((aa: A) => Some[A](aa)),
 p))) && (accepts_trace_prim[A](e, sa,
                                 (Transition.apply_updates[A](Transition.Updates[A,
  Unit](ta),
                       AExp.join_ir[A](i, d))).apply(d),
                                 t))
                       })))
    }
}

def accepts_trace[A : HOL.equal : Value.aexp_value](e:
              FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit])],
             s: Nat.nat, d: Map[Nat.nat, Option[A]],
             l: List[(String, (List[A], List[A]))]):
      Boolean
  =
  accepts_trace_prim[A](e, s, d, l)

def accepts_log[A : HOL.equal : Orderings.order : Value.aexp_value](l:
                              Set.set[List[(String, (List[A], List[A]))]],
                             e: FSet.fset[((Nat.nat, Nat.nat),
    Transition.transition_ext[A, Unit])]):
      Boolean
  =
  Set.Ball[List[(String,
                  (List[A],
                    List[A]))]](l, ((a: List[(String, (List[A], List[A]))]) =>
                                     accepts_trace[A](e, Nat.zero_nata,
               AExp.null_state[Nat.nat, Option[A]], a)))

def recognises_prim[A : HOL.equal : Value.aexp_value](e:
                FSet.fset[((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit])],
               s: Nat.nat, d: Map[Nat.nat, Option[A]],
               x3: List[(String, List[A])]):
      Boolean
  =
  (e, s, d, x3) match {
  case (e, s, d, Nil) => true
  case (e, s, d, (l, i) :: t) =>
    {
      val poss_steps: FSet.fset[(Nat.nat, Transition.transition_ext[A, Unit])] =
        possible_steps[A](e, s, d, l, i);
      FSet.fBex[(Nat.nat,
                  Transition.transition_ext[A,
     Unit])](poss_steps,
              ((a: (Nat.nat, Transition.transition_ext[A, Unit])) =>
                {
                  val (sa, ta): (Nat.nat, Transition.transition_ext[A, Unit]) =
                    a;
                  recognises_prim[A](e, sa,
                                      (Transition.apply_updates[A](Transition.Updates[A,
       Unit](ta),
                            AExp.join_ir[A](i, d))).apply(d),
                                      t)
                }))
    }
}

def recognises_execution[A : HOL.equal : Value.aexp_value](e:
                     FSet.fset[((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit])],
                    s: Nat.nat, r: Map[Nat.nat, Option[A]],
                    t: List[(String, List[A])]):
      Boolean
  =
  recognises_prim[A](e, s, r, t)

} /* object EFSM */

object EFSM_Dot {

def toString_vname(x0: VName.vname): String = x0 match {
  case VName.I(n) =>
    "i<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub>"
  case VName.R(n) =>
    "r<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub>"
}

trait to_string[A] {
  val `EFSM_Dot.toString`: A => String
}
def toString[A](a: A)(implicit A: to_string[A]): String =
  A.`EFSM_Dot.toString`(a)
object to_string {
  implicit def `EFSM_Dot.to_string_vname`: to_string[VName.vname] = new
    to_string[VName.vname] {
    val `EFSM_Dot.toString` = (a: VName.vname) => toString_vname(a)
  }
}

def aexp2dot[A : to_string, B : to_string](x0: AExp.aexp[A, B]): String = x0
  match {
  case AExp.L(v) => toString[B](v)
  case AExp.V(v) => toString[A](v)
  case AExp.Plus(a1, a2) => aexp2dot[A, B](a1) + " + " + aexp2dot[A, B](a2)
  case AExp.Minus(a1, a2) => aexp2dot[A, B](a1) + " - " + aexp2dot[A, B](a2)
  case AExp.Times(a1, a2) =>
    aexp2dot[A, B](a1) + " &times; " + aexp2dot[A, B](a2)
}

def updates2dot_aux[A : to_string](l: List[(Nat.nat,
     AExp.aexp[VName.vname, A])]):
      List[String]
  =
  Lista.map[(Nat.nat, AExp.aexp[VName.vname, A]),
             String](((a: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                       {
                         val (r, u): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
                         toString_vname(VName.R(r)) + " := " +
                           aexp2dot[VName.vname, A](u)
                       }),
                      l)

def updates2dot[A : to_string](x0: List[(Nat.nat, AExp.aexp[VName.vname, A])]):
      String
  =
  x0 match {
  case Nil => ""
  case v :: va =>
    "&#91;" + (updates2dot_aux[A](v :: va)).mkString(", ") + "&#93;"
}

def outputs2dot[A : to_string](x0: List[AExp.aexp[VName.vname, A]],
                                uu: Nat.nat):
      List[String]
  =
  (x0, uu) match {
  case (Nil, uu) => Nil
  case (h :: t, n) =>
    "o<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub> := " +
      aexp2dot[VName.vname, A](h) ::
      outputs2dot[A](t, Nat.plus_nata(n, Nat.Nata((1))))
}

def latter2dot[A : to_string](t: Transition.transition_ext[A, Unit]): String =
  {
    val l: String =
      (outputs2dot[A](Transition.Outputs[A, Unit](t),
                       Nat.Nata((1)))).mkString(", ") +
        updates2dot[A](Transition.Updates[A, Unit](t));
    (if (l == "") "" else "/" + l)
  }

def gexp2dot[A : to_string, B : to_string](x0: GExp.gexp[A, B]): String = x0
  match {
  case GExp.Bc(true) => "True"
  case GExp.Bc(false) => "False"
  case GExp.Eq(a1, a2) => aexp2dot[A, B](a1) + " = " + aexp2dot[A, B](a2)
  case GExp.Gt(a1, a2) => aexp2dot[A, B](a1) + " &gt; " + aexp2dot[A, B](a2)
  case GExp.In(v, l) =>
    toString[A](v) + "&isin;{" +
      (Lista.map[B, String](((a: B) => toString[B](a)), l)).mkString(", ") +
      "}"
  case GExp.Nor(g1, g2) =>
    "!(" + gexp2dot[A, B](g1) + "&or;" + gexp2dot[A, B](g2) + ")"
}

def guards2dot_aux[A : to_string, B : to_string](l: List[GExp.gexp[A, B]]):
      List[String]
  =
  Lista.map[GExp.gexp[A, B],
             String](((a: GExp.gexp[A, B]) => gexp2dot[A, B](a)), l)

def guards2dot[A : to_string, B : to_string](x0: List[GExp.gexp[A, B]]): String
  =
  x0 match {
  case Nil => ""
  case v :: va =>
    "&#91;" + (guards2dot_aux[A, B](v :: va)).mkString(", ") + "&#93;"
}

def transition2dot[A : to_string](t: Transition.transition_ext[A, Unit]): String
  =
  Transition.Label[A, Unit](t) + ":" +
    Code_Numeral.integer_of_nat(Transition.Arity[A, Unit](t)).toString() +
    guards2dot[VName.vname, A](Transition.Guards[A, Unit](t)) +
    latter2dot[A](t)

def efsm2dot[A : to_string : HOL.equal : Orderings.linorder](e:
                       FSet.fset[((Nat.nat, Nat.nat),
                                   Transition.transition_ext[A, Unit])]):
      String
  =
  "digraph EFSM{" + "\u000A" + "  graph [rankdir=" + "\"" + "LR" + "\"" +
    ", fontname=" +
    "\"" +
    "Latin Modern Math" +
    "\"" +
    "];" +
    "\u000A" +
    "  node [color=" +
    "\"" +
    "black" +
    "\"" +
    ", fillcolor=" +
    "\"" +
    "white" +
    "\"" +
    ", shape=" +
    "\"" +
    "circle" +
    "\"" +
    ", style=" +
    "\"" +
    "filled" +
    "\"" +
    ", fontname=" +
    "\"" +
    "Latin Modern Math" +
    "\"" +
    "];" +
    "\u000A" +
    "  edge [fontname=" +
    "\"" +
    "Latin Modern Math" +
    "\"" +
    "];" +
    "\u000A" +
    "\u000A" +
    "  s0[fillcolor=" +
    "\"" +
    "gray" +
    "\"" +
    ", label=<s<sub>0</sub>>];" +
    "\u000A" +
    (Lista.map[Nat.nat,
                String](((s: Nat.nat) =>
                          "  s" + Code_Numeral.integer_of_nat(s).toString() +
                            "[label=<s<sub>" +
                            Code_Numeral.integer_of_nat(s).toString() +
                            "</sub>>];"),
                         FSet.sorted_list_of_fset[Nat.nat](FSet_Utils.fremove[Nat.nat](Nat.zero_nata,
        EFSM.S[A](e))))).mkString("\u000A") +
    "\u000A" +
    "\u000A" +
    (Lista.map[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]),
                String](((a: ((Nat.nat, Nat.nat),
                               Transition.transition_ext[A, Unit]))
                           =>
                          {
                            val (aa, b):
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit])
                              = a;
                            ({
                               val (from, to): (Nat.nat, Nat.nat) = aa;
                               ((t: Transition.transition_ext[A, Unit]) =>
                                 "  s" +
                                   Code_Numeral.integer_of_nat(from).toString() +
                                   "->s" +
                                   Code_Numeral.integer_of_nat(to).toString() +
                                   "[label=<<i>" +
                                   transition2dot[A](t) +
                                   "</i>>];")
                             })(b)
                          }),
                         FSet.sorted_list_of_fset[((Nat.nat, Nat.nat),
            Transition.transition_ext[A, Unit])](e))).mkString("\u000A") +
    "\u000A" +
    "}"

def show_nats(l: List[Nat.nat]): String =
  (Lista.map[Nat.nat,
              String](((a: Nat.nat) =>
                        Code_Numeral.integer_of_nat(a).toString()),
                       l)).mkString(", ")

def iefsm2dot[A : to_string : HOL.equal : Orderings.linorder](e:
                        FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit]))]):
      String
  =
  "digraph EFSM{" + "\u000A" + "  graph [rankdir=" + "\"" + "LR" + "\"" +
    ", fontname=" +
    "\"" +
    "Latin Modern Math" +
    "\"" +
    "];" +
    "\u000A" +
    "  node [color=" +
    "\"" +
    "black" +
    "\"" +
    ", fillcolor=" +
    "\"" +
    "white" +
    "\"" +
    ", shape=" +
    "\"" +
    "circle" +
    "\"" +
    ", style=" +
    "\"" +
    "filled" +
    "\"" +
    ", fontname=" +
    "\"" +
    "Latin Modern Math" +
    "\"" +
    "];" +
    "\u000A" +
    "  edge [fontname=" +
    "\"" +
    "Latin Modern Math" +
    "\"" +
    "];" +
    "\u000A" +
    "\u000A" +
    "  s0[fillcolor=" +
    "\"" +
    "gray" +
    "\"" +
    ", label=<s<sub>0</sub>>];" +
    "\u000A" +
    (Lista.map[Nat.nat,
                String](((s: Nat.nat) =>
                          "  s" + Code_Numeral.integer_of_nat(s).toString() +
                            "[label=<s<sub>" +
                            Code_Numeral.integer_of_nat(s).toString() +
                            "</sub>>];"),
                         FSet.sorted_list_of_fset[Nat.nat](FSet_Utils.fremove[Nat.nat](Nat.zero_nata,
        Inference.S[A](e))))).mkString("\u000A") +
    "\u000A" +
    "\u000A" +
    (Lista.map[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
                String](((a: (List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit])))
                           =>
                          {
                            val (uid, aa):
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit]))
                              = a
                            val (ab, b):
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit])
                              = aa;
                            ({
                               val (from, to): (Nat.nat, Nat.nat) = ab;
                               ((t: Transition.transition_ext[A, Unit]) =>
                                 "  s" +
                                   Code_Numeral.integer_of_nat(from).toString() +
                                   "->s" +
                                   Code_Numeral.integer_of_nat(to).toString() +
                                   "[label=<<i> [" +
                                   show_nats(Lista.sort_key[Nat.nat,
                     Nat.nat](((x: Nat.nat) => x), uid)) +
                                   "]" +
                                   transition2dot[A](t) +
                                   "</i>>];")
                             })(b)
                          }),
                         FSet.sorted_list_of_fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat),
              Transition.transition_ext[A, Unit]))](e))).mkString("\u000A") +
    "\u000A" +
    "}"

} /* object EFSM_Dot */

object Group_By {

def group_by[A](f: A => A => Boolean, x1: List[A]): List[List[A]] = (f, x1)
  match {
  case (f, Nil) => Nil
  case (f, h :: t) =>
    {
      val group: List[A] = Lista.takeWhile[A](f(h), t)
      val dropped: List[A] = Lista.drop[A](Nat.Nata(group.par.length), t);
      (h :: group) :: group_by[A](f, dropped)
    }
}

} /* object Group_By */

object efsm2sal {

def escape(s: String, replacements: List[(String, String)]): String =
  Lista.fold[(String, String),
              String](((a: (String, String)) =>
                        {
                          val (old, newa): (String, String) = a;
                          ((sa: String) => sa.replaceAll(old, newa))
                        }),
                       replacements, s)

def replacements: List[(String, String)] =
  List(("/", "_SOL__"), ("\\" + "\\", "_BSOL__"), (" ", "_SPACE__"),
        ("\\" + "(", "_LPAR__"), ("\\" + ")", "_RPAR__"),
        ("\\" + ".", "_PERIOD__"), ("@", "_COMMAT__"))

def aexp2sal(x0: AExp.aexp[VName.vname, Value.value]): String = x0 match {
  case AExp.L(Value.Numa(n)) =>
    "Some(Num(" + Code_Numeral.integer_of_int(n).toString() + "))"
  case AExp.L(Value.Str(n)) =>
    "Some(Str(String__" +
      (if (n == "") "_EMPTY__" else escape(n, replacements)) +
      "))"
  case AExp.V(VName.I(i)) =>
    "Some(i(" + Code_Numeral.integer_of_nat(i).toString() + "))"
  case AExp.V(VName.R(r)) => "r__" + Code_Numeral.integer_of_nat(r).toString()
  case AExp.Plus(a1, a2) =>
    "value_plus(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case AExp.Minus(a1, a2) =>
    "value_minus(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case AExp.Times(a1, a2) =>
    "value_times(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
}

def gexp2sal(x0: GExp.gexp[VName.vname, Value.value]): String = x0 match {
  case GExp.Bc(true) => "True"
  case GExp.Bc(false) => "False"
  case GExp.Eq(a1, a2) => "value_eq(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case GExp.Gt(a1, a2) => "value_gt(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case GExp.In(v, l) =>
    (Lista.map[Value.value,
                String](((la: Value.value) =>
                          "gval(value_eq(" +
                            aexp2sal(AExp.V[VName.vname, Value.value](v)) +
                            ", " +
                            aexp2sal(AExp.L[Value.value, VName.vname](la)) +
                            "))"),
                         l)).mkString(" OR ")
  case GExp.Nor(g1, g2) =>
    "NOT (gval(" + gexp2sal(g1) + ") OR gval( " + gexp2sal(g2) + "))"
}

def guards2sal(x0: List[GExp.gexp[VName.vname, Value.value]]): String = x0 match
  {
  case Nil => "TRUE"
  case v :: va =>
    (Lista.map[GExp.gexp[VName.vname, Value.value],
                String](((a: GExp.gexp[VName.vname, Value.value]) =>
                          gexp2sal(a)),
                         v :: va)).mkString(" AND ")
}

def aexp2sal_num(x0: AExp.aexp[VName.vname, Value.value], uu: Nat.nat): String =
  (x0, uu) match {
  case (AExp.L(Value.Numa(n)), uu) =>
    "Some(Num(" + Code_Numeral.integer_of_int(n).toString() + "))"
  case (AExp.L(Value.Str(n)), uv) =>
    "Some(Str(String__" +
      (if (n == "") "_EMPTY__" else escape(n, replacements)) +
      "))"
  case (AExp.V(VName.I(i)), uw) =>
    "Some(i(" + Code_Numeral.integer_of_nat(i).toString() + "))"
  case (AExp.V(VName.R(i)), m) =>
    "r__" + Code_Numeral.integer_of_nat(i).toString() + "." +
      Code_Numeral.integer_of_nat(m).toString()
  case (AExp.Plus(a1, a2), ux) =>
    "value_plus(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case (AExp.Minus(a1, a2), uy) =>
    "value_minus(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case (AExp.Times(a1, a2), uz) =>
    "value_times(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
}

def gexp2sal_num(x0: GExp.gexp[VName.vname, Value.value], uu: Nat.nat): String =
  (x0, uu) match {
  case (GExp.Bc(true), uu) => "True"
  case (GExp.Bc(false), uv) => "False"
  case (GExp.Eq(a1, a2), m) =>
    "gval(value_eq(" + aexp2sal_num(a1, m) + ", " + aexp2sal_num(a2, m) + "))"
  case (GExp.Gt(a1, a2), m) =>
    "gval(value_gt(" + aexp2sal_num(a1, m) + ", " + aexp2sal_num(a2, m) + "))"
  case (GExp.In(v, l), m) =>
    (Lista.map[Value.value,
                String](((la: Value.value) =>
                          "gval(value_eq(" +
                            aexp2sal_num(AExp.V[VName.vname, Value.value](v),
  m) +
                            ", " +
                            aexp2sal_num(AExp.L[Value.value, VName.vname](la),
  m) +
                            "))"),
                         l)).mkString(" OR ")
  case (GExp.Nor(g1, g2), m) =>
    "NOT (" + gexp2sal_num(g1, m) + " OR " + gexp2sal_num(g2, m) + ")"
}

def guards2sal_num(x0: List[GExp.gexp[VName.vname, Value.value]], uu: Nat.nat):
      String
  =
  (x0, uu) match {
  case (Nil, uu) => "TRUE"
  case (v :: va, m) =>
    (Lista.map[GExp.gexp[VName.vname, Value.value],
                String](((g: GExp.gexp[VName.vname, Value.value]) =>
                          gexp2sal_num(g, m)),
                         v :: va)).mkString(" AND ")
}

} /* object efsm2sal */

object Store_Reuse {

abstract sealed class ioTag
final case class In() extends ioTag
final case class Out() extends ioTag

def equal_ioTaga(x0: ioTag, x1: ioTag): Boolean = (x0, x1) match {
  case (In(), Out()) => false
  case (Out(), In()) => false
  case (Out(), Out()) => true
  case (In(), In()) => true
}

def less_ioTag(x0: ioTag, uu: ioTag): Boolean = (x0, uu) match {
  case (In(), Out()) => true
  case (Out(), uu) => false
  case (In(), In()) => false
}

def less_eq_ioTag(x: ioTag, y: ioTag): Boolean =
  (less_ioTag(x, y)) || (equal_ioTaga(x, y))

def count[A : HOL.equal](uu: A, x1: List[A]): Nat.nat = (uu, x1) match {
  case (uu, Nil) => Nat.zero_nata
  case (a, h :: t) =>
    (if (HOL.eq[A](a, h)) Nat.plus_nata(Nat.Nata((1)), count[A](a, t))
      else count[A](a, t))
}

def index[A](x0: List[A], uu: Nat.nat, uv: ioTag, uw: Nat.nat):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  (x0, uu, uv, uw) match {
  case (Nil, uu, uv, uw) => FSet.bot_fset[(Nat.nat, (ioTag, Nat.nat))]
  case (h :: t, actionNo, io, ind) =>
    FSet.finsert[(Nat.nat,
                   (ioTag,
                     Nat.nat))]((actionNo, (io, ind)),
                                 index[A](t, actionNo, io,
   Nat.plus_nata(ind, Nat.Nata((1)))))
}

def i_step[A : HOL.equal : Value.aexp_value](tr: List[(String, List[A])],
      e: FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
      s: Nat.nat, r: Map[Nat.nat, Option[A]], l: String, i: List[A]):
      Option[(Transition.transition_ext[A, Unit],
               (Nat.nat, (List[Nat.nat], Map[Nat.nat, Option[A]])))]
  =
  {
    val poss_steps:
          FSet.fset[(List[Nat.nat],
                      (Nat.nat, Transition.transition_ext[A, Unit]))]
      = Inference.i_possible_steps[A](e, s, r, l, i)
    val possibilities:
          FSet.fset[(List[Nat.nat],
                      (Nat.nat, Transition.transition_ext[A, Unit]))]
      = FSet.ffilter[(List[Nat.nat],
                       (Nat.nat,
                         Transition.transition_ext[A,
            Unit]))](((a: (List[Nat.nat],
                            (Nat.nat, Transition.transition_ext[A, Unit])))
                        =>
                       {
                         val (_, (sa, t)):
                               (List[Nat.nat],
                                 (Nat.nat, Transition.transition_ext[A, Unit]))
                           = a;
                         EFSM.recognises_execution[A](Inference.tm[A](e), sa,
               (Transition.apply_updates[A](Transition.Updates[A, Unit](t),
     AExp.join_ir[A](i, r))).apply(r),
               tr)
                       }),
                      poss_steps);
    (Dirties.randomMember[(List[Nat.nat],
                            (Nat.nat,
                              Transition.transition_ext[A,
                 Unit]))](possibilities)
       match {
       case None => None
       case Some((u, (sa, t))) =>
         Some[(Transition.transition_ext[A, Unit],
                (Nat.nat,
                  (List[Nat.nat],
                    Map[Nat.nat, Option[A]])))]((t,
          (sa, (u, (Transition.apply_updates[A](Transition.Updates[A, Unit](t),
         AExp.join_ir[A](i, r))).apply(r)))))
     })
  }

def lookup[A](x0: (Nat.nat, (ioTag, Nat.nat)),
               t: List[(String, (List[A], List[A]))]):
      A
  =
  (x0, t) match {
  case ((actionNo, (In(), inx)), t) =>
    {
      val (_, (inputs, _)): (String, (List[A], List[A])) =
        t(Code_Numeral.integer_of_nat(actionNo).toInt);
      inputs(Code_Numeral.integer_of_nat(inx).toInt)
    }
  case ((actionNo, (Out(), inx)), t) =>
    {
      val (_, (_, outputs)): (String, (List[A], List[A])) =
        t(Code_Numeral.integer_of_nat(actionNo).toInt);
      outputs(Code_Numeral.integer_of_nat(inx).toInt)
    }
}

def remove_guard_add_update[A : HOL.equal : Orderings.order : Value.aexp_value](t:
  Transition.transition_ext[A, Unit],
 inputX: Nat.nat, outputX: Nat.nat):
      Transition.transition_ext[A, Unit]
  =
  Transition.transition_exta[A, Unit](Transition.Label[A, Unit](t),
                                       Transition.Arity[A, Unit](t),
                                       Lista.filter[GExp.gexp[VName.vname,
                       A]](((g: GExp.gexp[VName.vname, A]) =>
                             ! (GExp.gexp_constrains[VName.vname,
              A](g, AExp.V[VName.vname, A](VName.I(inputX))))),
                            Transition.Guards[A, Unit](t)),
                                       Transition.Outputs[A, Unit](t),
                                       (outputX,
 AExp.V[VName.vname, A](VName.I(inputX))) ::
 Transition.Updates[A, Unit](t),
                                       ())

def replaceAll[A : HOL.equal](e: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                               old: Transition.transition_ext[A, Unit],
                               newa: Transition.transition_ext[A, Unit]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[A,
      Unit]))](((a: (List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                  =>
                 {
                   val (uid, aa):
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))
                     = a
                   val (ab, b):
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit])
                     = aa;
                   ({
                      val (from, dest): (Nat.nat, Nat.nat) = ab;
                      ((t: Transition.transition_ext[A, Unit]) =>
                        (if (Transition.equal_transition_exta[A, Unit](t, old))
                          (uid, ((from, dest), newa))
                          else (uid, ((from, dest), t))))
                    })(b)
                 }),
                e)

def generalise_transitions[A : HOL.equal](x0:
    List[((((Transition.transition_ext[A, Unit], List[Nat.nat]),
             (ioTag, Nat.nat)),
            ((Transition.transition_ext[A, Unit], List[Nat.nat]),
              (ioTag, Nat.nat))),
           (((Transition.transition_ext[A, Unit], List[Nat.nat]),
              (ioTag, Nat.nat)),
             ((Transition.transition_ext[A, Unit], List[Nat.nat]),
               (ioTag, Nat.nat))))],
   e: FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (x0, e) match {
  case (Nil, e) => e
  case (h :: t, e) =>
    {
      val a: ((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat))),
               (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat))))
        = h
      val (aa, b):
            ((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (ioTag, Nat.nat))),
              (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat))))
        = a;
      ({
         val (ab, ba):
               (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))
           = aa;
         ({
            val (ac, bb):
                  ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))
              = ab;
            ({
               val (orig1, _):
                     (Transition.transition_ext[A, Unit], List[Nat.nat])
                 = ac;
               ((_: (ioTag, Nat.nat)) =>
                 (ad: ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                        (ioTag, Nat.nat)))
                   =>
                 {
                   val (ae, bc):
                         ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                           (ioTag, Nat.nat))
                     = ad;
                   ({
                      val (orig2, _):
                            (Transition.transition_ext[A, Unit], List[Nat.nat])
                        = ae;
                      ((_: (ioTag, Nat.nat)) =>
                        (af: (((Transition.transition_ext[A, Unit],
                                 List[Nat.nat]),
                                (ioTag, Nat.nat)),
                               ((Transition.transition_ext[A, Unit],
                                  List[Nat.nat]),
                                 (ioTag, Nat.nat))))
                          =>
                        {
                          val (ag, bd):
                                (((Transition.transition_ext[A, Unit],
                                    List[Nat.nat]),
                                   (ioTag, Nat.nat)),
                                  ((Transition.transition_ext[A, Unit],
                                     List[Nat.nat]),
                                    (ioTag, Nat.nat)))
                            = af;
                          ({
                             val (ah, be):
                                   ((Transition.transition_ext[A, Unit],
                                      List[Nat.nat]),
                                     (ioTag, Nat.nat))
                               = ag;
                             ({
                                val (gen1, _):
                                      (Transition.transition_ext[A, Unit],
List[Nat.nat])
                                  = ah;
                                ((_: (ioTag, Nat.nat)) =>
                                  (ai: ((Transition.transition_ext[A, Unit],
  List[Nat.nat]),
 (ioTag, Nat.nat)))
                                    =>
                                  {
                                    val (aj, bf):
  ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))
                                      = ai;
                                    ({
                                       val
 (gen2, _): (Transition.transition_ext[A, Unit], List[Nat.nat]) = aj;
                                       ((_: (ioTag, Nat.nat)) =>
 generalise_transitions[A](t, replaceAll[A](replaceAll[A](e, orig1, gen1),
     orig2, gen2)))
                                     })(bf)
                                  })
                              })(be)
                           })(bd)
                        })
                    })(bc)
                 })
             })(bb)
          })(ba)
       })(b)
    }
}

def generalise_output[A : Orderings.order : Value.aexp_value](t:
                        Transition.transition_ext[A, Unit],
                       regX: Nat.nat, outputX: Nat.nat):
      Transition.transition_ext[A, Unit]
  =
  Transition.transition_exta[A, Unit](Transition.Label[A, Unit](t),
                                       Transition.Arity[A, Unit](t),
                                       Transition.Guards[A, Unit](t),
                                       Lista.list_update[AExp.aexp[VName.vname,
                            A]](Transition.Outputs[A, Unit](t), outputX,
                                 AExp.V[VName.vname, A](VName.R(regX))),
                                       Transition.Updates[A, Unit](t), ())

def strip_uids[A](x: (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                        (ioTag, Nat.nat)),
                       ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (ioTag, Nat.nat)))):
      ((Transition.transition_ext[A, Unit], (ioTag, Nat.nat)),
        (Transition.transition_ext[A, Unit], (ioTag, Nat.nat)))
  =
  {
    val a: (((Transition.transition_ext[A, Unit], List[Nat.nat]),
              (ioTag, Nat.nat)),
             ((Transition.transition_ext[A, Unit], List[Nat.nat]),
               (ioTag, Nat.nat)))
      = x
    val (aa, b):
          (((Transition.transition_ext[A, Unit], List[Nat.nat]),
             (ioTag, Nat.nat)),
            ((Transition.transition_ext[A, Unit], List[Nat.nat]),
              (ioTag, Nat.nat)))
      = a;
    ({
       val (ab, ba):
             ((Transition.transition_ext[A, Unit], List[Nat.nat]),
               (ioTag, Nat.nat))
         = aa;
       ({
          val (t1, _): (Transition.transition_ext[A, Unit], List[Nat.nat]) = ab;
          ((ac: (ioTag, Nat.nat)) =>
            {
              val (io1, in1): (ioTag, Nat.nat) = ac;
              ((ad: ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (ioTag, Nat.nat)))
                 =>
                {
                  val (ae, bb):
                        ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                          (ioTag, Nat.nat))
                    = ad;
                  ({
                     val (t2, _):
                           (Transition.transition_ext[A, Unit], List[Nat.nat])
                       = ae;
                     ((af: (ioTag, Nat.nat)) =>
                       {
                         val (io2, in2): (ioTag, Nat.nat) = af;
                         ((t1, (io1, in1)), (t2, (io2, in2)))
                       })
                   })(bb)
                })
            })
        })(ba)
     })(b)
  }

def modify[A : HOL.equal : Orderings.order : Value.aexp_value](matches:
                         List[(((Transition.transition_ext[A, Unit],
                                  List[Nat.nat]),
                                 (ioTag, Nat.nat)),
                                ((Transition.transition_ext[A, Unit],
                                   List[Nat.nat]),
                                  (ioTag, Nat.nat)))],
                        u1: List[Nat.nat], u2: List[Nat.nat],
                        old: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  {
    val relevant:
          List[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))]
      = Lista.filter[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                        (ioTag, Nat.nat)),
                       ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (ioTag,
                           Nat.nat)))](((a:
   (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
     ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))))
  =>
 {
   val (aa, b):
         (((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (ioTag, Nat.nat)),
           ((Transition.transition_ext[A, Unit], List[Nat.nat]),
             (ioTag, Nat.nat)))
     = a;
   ({
      val (ab, ba):
            ((Transition.transition_ext[A, Unit], List[Nat.nat]),
              (ioTag, Nat.nat))
        = aa;
      ({
         val (_, u1a): (Transition.transition_ext[A, Unit], List[Nat.nat]) = ab;
         ((ac: (ioTag, Nat.nat)) =>
           {
             val (io, _): (ioTag, Nat.nat) = ac;
             ((ad: ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)))
                =>
               {
                 val (ae, bb):
                       ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (ioTag, Nat.nat))
                   = ad;
                 ({
                    val (_, u2a):
                          (Transition.transition_ext[A, Unit], List[Nat.nat])
                      = ae;
                    ((af: (ioTag, Nat.nat)) =>
                      {
                        val (ioa, _): (ioTag, Nat.nat) = af;
                        (equal_ioTaga(io, In())) && ((equal_ioTaga(ioa,
                            Out())) && ((Lista.equal_lista[Nat.nat](u1,
                             u1a)) || ((Lista.equal_lista[Nat.nat](u2,
                            u1a)) || ((Lista.equal_lista[Nat.nat](u1,
                           u2a)) || (Lista.equal_lista[Nat.nat](u2, u2a))))))
                      })
                  })(bb)
               })
           })
       })(ba)
    })(b)
 }),
matches)
    val newReg: Nat.nat = (Inference.max_reg[A](old) match {
                             case None => Nat.Nata((1))
                             case Some(r) => Nat.plus_nata(r, Nat.Nata((1)))
                           })
    val replacements:
          List[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (ioTag, Nat.nat))),
                   (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (ioTag, Nat.nat)),
                     ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
   ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))))
=>
                                       {
 val (aa, b):
       (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
         ((Transition.transition_ext[A, Unit], List[Nat.nat]),
           (ioTag, Nat.nat)))
   = a;
 ({
    val (ab, ba):
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (ioTag, Nat.nat))
      = aa;
    ({
       val (t1, u1a): (Transition.transition_ext[A, Unit], List[Nat.nat]) = ab;
       ((ac: (ioTag, Nat.nat)) =>
         {
           val (io1, inx1): (ioTag, Nat.nat) = ac;
           ((ad: ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))
              =>
             {
               val (ae, bb):
                     ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                       (ioTag, Nat.nat))
                 = ad;
               ({
                  val (t2, u2a):
                        (Transition.transition_ext[A, Unit], List[Nat.nat])
                    = ae;
                  ((af: (ioTag, Nat.nat)) =>
                    {
                      val (io2, inx2): (ioTag, Nat.nat) = af;
                      (((remove_guard_add_update[A](t1, inx1, newReg), u1a),
                         (io1, inx1)),
                        ((generalise_output[A](t2, newReg, inx2), u2a),
                          (io2, inx2)))
                    })
                })(bb)
             })
         })
     })(ba)
  })(b)
                                       }),
                                      relevant)
    val comparisons:
          List[((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat))))]
      = relevant.par.zip(replacements).toList
    val stripped_replacements:
          List[((Transition.transition_ext[A, Unit], (ioTag, Nat.nat)),
                 (Transition.transition_ext[A, Unit], (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (ioTag, Nat.nat))),
                   ((Transition.transition_ext[A, Unit], (ioTag, Nat.nat)),
                     (Transition.transition_ext[A, Unit],
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
   ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))))
=>
                                       strip_uids[A](a)),
                                      replacements)
    val to_replace:
          List[((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat))))]
      = Lista.filter[((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (ioTag, Nat.nat)),
                        ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                          (ioTag, Nat.nat))),
                       (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                          (ioTag, Nat.nat)),
                         ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                           (ioTag,
                             Nat.nat))))](((a:
      ((((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
         ((Transition.transition_ext[A, Unit], List[Nat.nat]),
           (ioTag, Nat.nat))),
        (((Transition.transition_ext[A, Unit], List[Nat.nat]),
           (ioTag, Nat.nat)),
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (ioTag, Nat.nat)))))
     =>
    {
      val (_, s):
            ((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (ioTag, Nat.nat))),
              (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat))))
        = a;
      Nat.less_nat(Nat.Nata((1)),
                    count[((Transition.transition_ext[A, Unit],
                             (ioTag, Nat.nat)),
                            (Transition.transition_ext[A, Unit],
                              (ioTag,
                                Nat.nat)))](strip_uids[A](s),
     stripped_replacements))
    }),
   comparisons);
    (if (to_replace.isEmpty) None
      else Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A,
                 Unit]))]](generalise_transitions[A](to_replace, old)))
  }

def io_index[A](actionNo: Nat.nat, inputs: List[A], outputs: List[A]):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  FSet.sup_fset[(Nat.nat,
                  (ioTag,
                    Nat.nat))](index[A](inputs, actionNo, In(), Nat.zero_nata),
                                index[A](outputs, actionNo, Out(),
  Nat.zero_nata))

def indices[A](e: List[(String, (List[A], List[A]))]):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  Dirties.foldl[FSet.fset[(Nat.nat, (ioTag, Nat.nat))],
                 (Nat.nat,
                   (String,
                     (List[A],
                       List[A])))](((a: FSet.fset[(Nat.nat, (ioTag, Nat.nat))])
                                      =>
                                     (x:
(Nat.nat, (String, (List[A], List[A]))))
                                       =>
                                     FSet.sup_fset[(Nat.nat,
             (ioTag,
               Nat.nat))](a, {
                               val (actionNo, aa):
                                     (Nat.nat, (String, (List[A], List[A])))
                                 = x
                               val (_, ab): (String, (List[A], List[A])) = aa
                               val (ac, b): (List[A], List[A]) = ab;
                               io_index[A](actionNo, ac, b)
                             })),
                                    FSet.bot_fset[(Nat.nat, (ioTag, Nat.nat))],
                                    Lista.enumerate[(String,
              (List[A], List[A]))](Nat.zero_nata, e))

def remove_guards_add_update[A](t: Transition.transition_ext[A, Unit],
                                 inputX: Nat.nat, outputX: Nat.nat):
      Transition.transition_ext[A, Unit]
  =
  Transition.transition_exta[A, Unit](Transition.Label[A, Unit](t),
                                       Transition.Arity[A, Unit](t), Nil,
                                       Transition.Outputs[A, Unit](t),
                                       (outputX,
 AExp.V[VName.vname, A](VName.I(inputX))) ::
 Transition.Updates[A, Unit](t),
                                       ())

def structural_count[A](uu: ((Transition.transition_ext[A, Unit],
                               (ioTag, Nat.nat)),
                              (Transition.transition_ext[A, Unit],
                                (ioTag, Nat.nat))),
                         x1: List[((Transition.transition_ext[A, Unit],
                                     (ioTag, Nat.nat)),
                                    (Transition.transition_ext[A, Unit],
                                      (ioTag, Nat.nat)))]):
      Nat.nat
  =
  (uu, x1) match {
  case (uu, Nil) => Nat.zero_nata
  case (a, ((t1, (io1, i1)), (t2, (io2, i2))) :: t) =>
    {
      val b: ((Transition.transition_ext[A, Unit], (ioTag, Nat.nat)),
               (Transition.transition_ext[A, Unit], (ioTag, Nat.nat)))
        = a
      val (ba, c):
            ((Transition.transition_ext[A, Unit], (ioTag, Nat.nat)),
              (Transition.transition_ext[A, Unit], (ioTag, Nat.nat)))
        = b;
      ({
         val (t1a, (io1a, i1a)):
               (Transition.transition_ext[A, Unit], (ioTag, Nat.nat))
           = ba;
         ((bb: (Transition.transition_ext[A, Unit], (ioTag, Nat.nat))) =>
           {
             val (t2a, (io2a, i2a)):
                   (Transition.transition_ext[A, Unit], (ioTag, Nat.nat))
               = bb;
             (if ((Transition.same_structure[A](t1a,
         t1)) && ((Transition.same_structure[A](t2a,
         t2)) && ((equal_ioTaga(io1a,
                                 io1)) && ((equal_ioTaga(io2a,
                  io2)) && ((Nat.equal_nata(i1a,
     i1)) && (Nat.equal_nata(i2a, i2)))))))
               Nat.plus_nata(Nat.Nata((1)), structural_count[A](a, t))
               else structural_count[A](a, t))
           })
       })(c)
    }
}

def generalise_input[A](t: Transition.transition_ext[A, Unit], r: Nat.nat,
                         i: Nat.nat):
      Transition.transition_ext[A, Unit]
  =
  Transition.transition_exta[A, Unit](Transition.Label[A, Unit](t),
                                       Transition.Arity[A, Unit](t),
                                       Lista.map[GExp.gexp[VName.vname, A],
          GExp.gexp[VName.vname,
                     A]](((g: GExp.gexp[VName.vname, A]) =>
                           (g match {
                              case GExp.Bc(_) => g
                              case GExp.Eq(AExp.L(_), _) => g
                              case GExp.Eq(AExp.V(VName.I(ia)), AExp.L(_)) =>
                                (if (Nat.equal_nata(i, ia))
                                  GExp.Eq[VName.vname,
   A](AExp.V[VName.vname, A](VName.I(i)), AExp.V[VName.vname, A](VName.R(r)))
                                  else g)
                              case GExp.Eq(AExp.V(VName.I(_)), AExp.V(_)) => g
                              case GExp.Eq(AExp.V(VName.I(_)), AExp.Plus(_, _))
                                => g
                              case GExp.Eq(AExp.V(VName.I(_)), AExp.Minus(_, _))
                                => g
                              case GExp.Eq(AExp.V(VName.I(_)), AExp.Times(_, _))
                                => g
                              case GExp.Eq(AExp.V(VName.R(_)), _) => g
                              case GExp.Eq(AExp.Plus(_, _), _) => g
                              case GExp.Eq(AExp.Minus(_, _), _) => g
                              case GExp.Eq(AExp.Times(_, _), _) => g
                              case GExp.Gt(_, _) => g
                              case GExp.In(_, _) => g
                              case GExp.Nor(_, _) => g
                            })),
                          Transition.Guards[A, Unit](t)),
                                       Transition.Outputs[A, Unit](t),
                                       Transition.Updates[A, Unit](t), ())

def modify_2[A : HOL.equal](matches:
                              List[(((Transition.transition_ext[A, Unit],
                                       List[Nat.nat]),
                                      (ioTag, Nat.nat)),
                                     ((Transition.transition_ext[A, Unit],
List[Nat.nat]),
                                       (ioTag, Nat.nat)))],
                             u1: List[Nat.nat], u2: List[Nat.nat],
                             old: FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  {
    val relevant:
          List[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))]
      = Lista.filter[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                        (ioTag, Nat.nat)),
                       ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (ioTag,
                           Nat.nat)))](((a:
   (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
     ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))))
  =>
 {
   val (aa, b):
         (((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (ioTag, Nat.nat)),
           ((Transition.transition_ext[A, Unit], List[Nat.nat]),
             (ioTag, Nat.nat)))
     = a;
   ({
      val (ab, ba):
            ((Transition.transition_ext[A, Unit], List[Nat.nat]),
              (ioTag, Nat.nat))
        = aa;
      ({
         val (_, u1a): (Transition.transition_ext[A, Unit], List[Nat.nat]) = ab;
         ((ac: (ioTag, Nat.nat)) =>
           {
             val (io, _): (ioTag, Nat.nat) = ac;
             ((ad: ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)))
                =>
               {
                 val (ae, bb):
                       ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (ioTag, Nat.nat))
                   = ad;
                 ({
                    val (_, u2a):
                          (Transition.transition_ext[A, Unit], List[Nat.nat])
                      = ae;
                    ((af: (ioTag, Nat.nat)) =>
                      {
                        val (ioa, _): (ioTag, Nat.nat) = af;
                        (equal_ioTaga(io, In())) && ((equal_ioTaga(ioa,
                            In())) && ((Lista.equal_lista[Nat.nat](u1,
                            u1a)) || ((Lista.equal_lista[Nat.nat](u2,
                           u1a)) || ((Lista.equal_lista[Nat.nat](u1,
                          u2a)) || (Lista.equal_lista[Nat.nat](u2, u2a))))))
                      })
                  })(bb)
               })
           })
       })(ba)
    })(b)
 }),
matches)
    val newReg: Nat.nat = (Inference.max_reg[A](old) match {
                             case None => Nat.Nata((1))
                             case Some(r) => Nat.plus_nata(r, Nat.Nata((1)))
                           })
    val replacements:
          List[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (ioTag, Nat.nat))),
                   (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (ioTag, Nat.nat)),
                     ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
   ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))))
=>
                                       {
 val (aa, b):
       (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
         ((Transition.transition_ext[A, Unit], List[Nat.nat]),
           (ioTag, Nat.nat)))
   = a;
 ({
    val (ab, ba):
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (ioTag, Nat.nat))
      = aa;
    ({
       val (t1, u1a): (Transition.transition_ext[A, Unit], List[Nat.nat]) = ab;
       ((ac: (ioTag, Nat.nat)) =>
         {
           val (io1, inx1): (ioTag, Nat.nat) = ac;
           ((ad: ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))
              =>
             {
               val (ae, bb):
                     ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                       (ioTag, Nat.nat))
                 = ad;
               ({
                  val (t2, u2a):
                        (Transition.transition_ext[A, Unit], List[Nat.nat])
                    = ae;
                  ((af: (ioTag, Nat.nat)) =>
                    {
                      val (io2, inx2): (ioTag, Nat.nat) = af;
                      (((remove_guards_add_update[A](t1, inx1, newReg), u1a),
                         (io1, inx1)),
                        ((generalise_input[A](t2, newReg, inx2), u2a),
                          (io2, inx2)))
                    })
                })(bb)
             })
         })
     })(ba)
  })(b)
                                       }),
                                      relevant)
    val comparisons:
          List[((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat))))]
      = relevant.par.zip(replacements).toList
    val stripped_replacements:
          List[((Transition.transition_ext[A, Unit], (ioTag, Nat.nat)),
                 (Transition.transition_ext[A, Unit], (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                      (ioTag, Nat.nat))),
                   ((Transition.transition_ext[A, Unit], (ioTag, Nat.nat)),
                     (Transition.transition_ext[A, Unit],
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
   ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))))
=>
                                       strip_uids[A](a)),
                                      replacements)
    val to_replace:
          List[((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (ioTag, Nat.nat))))]
      = Lista.filter[((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                         (ioTag, Nat.nat)),
                        ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                          (ioTag, Nat.nat))),
                       (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                          (ioTag, Nat.nat)),
                         ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                           (ioTag,
                             Nat.nat))))](((a:
      ((((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
         ((Transition.transition_ext[A, Unit], List[Nat.nat]),
           (ioTag, Nat.nat))),
        (((Transition.transition_ext[A, Unit], List[Nat.nat]),
           (ioTag, Nat.nat)),
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (ioTag, Nat.nat)))))
     =>
    {
      val (_, s):
            ((((Transition.transition_ext[A, Unit], List[Nat.nat]),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (ioTag, Nat.nat))),
              (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat))))
        = a;
      Nat.less_nat(Nat.Nata((1)),
                    structural_count[A](strip_uids[A](s),
 stripped_replacements))
    }),
   comparisons);
    (if (to_replace.isEmpty) None
      else Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A,
                 Unit]))]](generalise_transitions[A](to_replace, old)))
  }

def exec2trace[A, B, C](t: List[(A, (B, C))]): List[(A, B)] =
  Lista.map[(A, (B, C)),
             (A, B)](((a: (A, (B, C))) =>
                       {
                         val (label, (inputs, _)): (A, (B, C)) = a;
                         (label, inputs)
                       }),
                      t)

def walk_up_to[A : HOL.equal : Value.aexp_value](n: Nat.nat,
          e: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))],
          s: Nat.nat, r: Map[Nat.nat, Option[A]],
          x4: List[(String, (List[A], List[A]))]):
      (Transition.transition_ext[A, Unit], List[Nat.nat])
  =
  (n, e, s, r, x4) match {
  case (n, e, s, r, h :: t) =>
    {
      val (Some((transition, (sa, (uid, updated))))):
            Option[(Transition.transition_ext[A, Unit],
                     (Nat.nat, (List[Nat.nat], Map[Nat.nat, Option[A]])))]
        = i_step[A](exec2trace[String, List[A], List[A]](t), e, s, r, h._1,
                     (h._2)._1);
      (if (Nat.equal_nata(n, Nat.zero_nata)) (transition, uid)
        else walk_up_to[A](Nat.minus_nat(n, Nat.Nata((1))), e, sa, updated, t))
    }
}

def get_by_id_intratrace_matches[A : HOL.equal](e:
          List[(String, (List[A], List[A]))]):
      FSet.fset[((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat)))]
  =
  FSet.ffilter[((Nat.nat, (ioTag, Nat.nat)),
                 (Nat.nat,
                   (ioTag,
                     Nat.nat)))](((a: ((Nat.nat, (ioTag, Nat.nat)),
(Nat.nat, (ioTag, Nat.nat))))
                                    =>
                                   {
                                     val (aa, b):
   ((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat)))
                                       = a;
                                     (HOL.eq[A](lookup[A](aa, e),
         lookup[A](b, e))) && ((Nat.less_eq_nat(aa._1,
         b._1)) && (! (Product_Type.equal_proda[Nat.nat,
         (ioTag, Nat.nat)](aa, b))))
                                   }),
                                  FSet_Utils.fprod[(Nat.nat, (ioTag, Nat.nat)),
            (Nat.nat, (ioTag, Nat.nat))](indices[A](e), indices[A](e)))

def find_intertrace_matches_aux[A : HOL.equal : Orderings.order : Value.aexp_value](intras:
      FSet.fset[((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat)))],
     e: FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
     t: List[(String, (List[A], List[A]))]):
      FSet.fset[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)))]
  =
  FSet.fimage[((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat))),
               (((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag,
                     Nat.nat)))](((a: ((Nat.nat, (ioTag, Nat.nat)),
(Nat.nat, (ioTag, Nat.nat))))
                                    =>
                                   {
                                     val (aa, b):
   ((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat)))
                                       = a;
                                     ({
val (e1, (io1, inx1)): (Nat.nat, (ioTag, Nat.nat)) = aa;
((ab: (Nat.nat, (ioTag, Nat.nat))) =>
  {
    val (e2, (io2, inx2)): (Nat.nat, (ioTag, Nat.nat)) = ab;
    ((walk_up_to[A](e1, e, Nat.zero_nata, AExp.null_state[Nat.nat, Option[A]],
                     t),
       (io1, inx1)),
      (walk_up_to[A](e2, e, Nat.zero_nata, AExp.null_state[Nat.nat, Option[A]],
                      t),
        (io2, inx2)))
  })
                                      })(b)
                                   }),
                                  intras)

def find_intertrace_matches[A : HOL.equal : Orderings.linorder : Value.aexp_value](l:
     List[List[(String, (List[A], List[A]))]],
    e: FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      List[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
              (ioTag, Nat.nat)),
             ((Transition.transition_ext[A, Unit], List[Nat.nat]),
               (ioTag, Nat.nat)))]
  =
  Lista.filter[(((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                   (ioTag,
                     Nat.nat)))](((a: (((Transition.transition_ext[A, Unit],
  List[Nat.nat]),
 (ioTag, Nat.nat)),
((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))))
                                    =>
                                   {
                                     val (aa, b):
   (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
     ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)))
                                       = a;
                                     ({
val (e1, (_, _)):
      ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat))
  = aa;
((ab: ((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)))
   =>
  {
    val (e2, (_, _)):
          ((Transition.transition_ext[A, Unit], List[Nat.nat]),
            (ioTag, Nat.nat))
      = ab;
    ! (Product_Type.equal_proda[Transition.transition_ext[A, Unit],
                                 List[Nat.nat]](e1, e2))
  })
                                      })(b)
                                   }),
                                  Lista.maps[(List[(String,
             (List[A], List[A]))],
       FSet.fset[((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat)))]),
      (((Transition.transition_ext[A, Unit], List[Nat.nat]), (ioTag, Nat.nat)),
        ((Transition.transition_ext[A, Unit], List[Nat.nat]),
          (ioTag,
            Nat.nat)))](((a: (List[(String, (List[A], List[A]))],
                               FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
   (Nat.nat, (ioTag, Nat.nat)))]))
                           =>
                          {
                            val (t, m):
                                  (List[(String, (List[A], List[A]))],
                                    FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
        (Nat.nat, (ioTag, Nat.nat)))])
                              = a;
                            FSet.sorted_list_of_fset[(((Transition.transition_ext[A,
   Unit],
                 List[Nat.nat]),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)))](find_intertrace_matches_aux[A](m, e, t))
                          }),
                         l.par.zip(Lista.map[List[(String, (List[A], List[A]))],
      FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
                  (Nat.nat,
                    (ioTag,
                      Nat.nat)))]](((a: List[(String, (List[A], List[A]))]) =>
                                     get_by_id_intratrace_matches[A](a)),
                                    l)).toList))

def heuristic_1[A : HOL.equal : Orderings.linorder : Value.aexp_value](l:
                                 List[List[(String, (List[A], List[A]))]],
                                t1: List[Nat.nat], t2: List[Nat.nat],
                                s: Nat.nat,
                                newa: FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                uu: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                old: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                check:
                                  (FSet.fset[((Nat.nat, Nat.nat),
       Transition.transition_ext[A, Unit])]) =>
                                    Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  (modify[A](find_intertrace_matches[A](l, old), t1, t2, newa) match {
     case None => None
     case Some(e) =>
       (if (check(Inference.tm[A](e)))
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]](e)
         else None)
   })

def heuristic_2[A : HOL.equal : Orderings.linorder : Value.aexp_value](l:
                                 List[List[(String, (List[A], List[A]))]],
                                t1: List[Nat.nat], t2: List[Nat.nat],
                                s: Nat.nat,
                                newa: FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                uu: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                old: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                check:
                                  (FSet.fset[((Nat.nat, Nat.nat),
       Transition.transition_ext[A, Unit])]) =>
                                    Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  (modify_2[A](find_intertrace_matches[A](l, old), t1, t2, newa) match {
     case None => None
     case Some(e) =>
       (if (check(Inference.tm[A](e)))
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]](e)
         else None)
   })

} /* object Store_Reuse */

object Same_Register {

def replace_with[A](e: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit]))],
                     r1: Nat.nat, r2: Nat.nat):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[A,
      Unit]))](((a: (List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                  =>
                 {
                   val (u, (tf, t)):
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))
                     = a;
                   (u, (tf, Transition.rename_regs[A](Fun.fun_upd[Nat.nat,
                           Nat.nat](Fun.id[Nat.nat], r1, r2),
               t)))
                 }),
                e)

def merge_if_same[A : HOL.equal : Orderings.linorder](e:
                FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit]))],
               uu: (FSet.fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit])]) =>
                     Boolean,
               x2: List[(Nat.nat, Nat.nat)]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (e, uu, x2) match {
  case (e, uu, Nil) => e
  case (e, check, (r1, r2) :: rs) =>
    {
      val transitions: FSet.fset[Transition.transition_ext[A, Unit]] =
        FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
                     Transition.transition_ext[A,
        Unit]](Fun.comp[((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]),
                         Transition.transition_ext[A, Unit],
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A,
                Unit]))](((a: ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit]))
                            =>
                           a._2),
                          ((a: (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[A, Unit])))
                             =>
                            a._2)),
                e);
      (if (FSet.fBex[(Transition.transition_ext[A, Unit],
                       Transition.transition_ext[A,
          Unit])](FSet.ffilter[(Transition.transition_ext[A, Unit],
                                 Transition.transition_ext[A,
                    Unit])](((a: (Transition.transition_ext[A, Unit],
                                   Transition.transition_ext[A, Unit]))
                               =>
                              {
                                val (aa, b):
                                      (Transition.transition_ext[A, Unit],
Transition.transition_ext[A, Unit])
                                  = a;
                                Transition_Lexorder.less_transition_ext[A,
                                 Unit](aa, b)
                              }),
                             FSet_Utils.fprod[Transition.transition_ext[A,
                                 Unit],
       Transition.transition_ext[A, Unit]](transitions, transitions)),
                   ((a: (Transition.transition_ext[A, Unit],
                          Transition.transition_ext[A, Unit]))
                      =>
                     {
                       val (t1, t2):
                             (Transition.transition_ext[A, Unit],
                               Transition.transition_ext[A, Unit])
                         = a;
                       (Transition.same_structure[A](t1,
              t2)) && ((Set.member[Nat.nat](r1,
     Transition.enumerate_regs[A](t1))) && (Set.member[Nat.nat](r2,
                         Transition.enumerate_regs[A](t2))))
                     })))
        {
          val newE: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit]))]
            = replace_with[A](e, r1, r2);
          (if (check(Inference.tm[A](newE))) merge_if_same[A](newE, check, rs)
            else merge_if_same[A](e, check, rs))
        }
        else merge_if_same[A](e, check, rs))
    }
}

def merge_regs[A : HOL.equal : Orderings.linorder](e:
             FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))],
            check:
              (FSet.fset[((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit])]) =>
                Boolean):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  {
    val regs: Set.set[Nat.nat] = Inference.all_regs[A](e)
    val a: List[(Nat.nat, Nat.nat)] =
      Lista.sorted_list_of_set[(Nat.nat,
                                 Nat.nat)](Set.filter[(Nat.nat,
                Nat.nat)](((a: (Nat.nat, Nat.nat)) =>
                            {
                              val (aa, b): (Nat.nat, Nat.nat) = a;
                              Nat.less_nat(aa, b)
                            }),
                           Product_Type.product[Nat.nat, Nat.nat](regs, regs)));
    merge_if_same[A](e, check, a)
  }

def same_register[A : HOL.equal : Orderings.linorder](t1ID: List[Nat.nat],
               t2ID: List[Nat.nat], s: Nat.nat,
               newa: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[A, Unit]))],
               uu: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))],
               old: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit]))],
               check:
                 (FSet.fset[((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit])]) =>
                   Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  {
    val newaa:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
      = merge_regs[A](newa, check);
    (if (FSet.equal_fseta[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A,
                 Unit]))](newaa, newa))
      None
      else Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit]))]](newaa))
  }

} /* object Same_Register */

object Value_Lexorder {

def less_value(x0: Value.value, x1: Value.value): Boolean = (x0, x1) match {
  case (Value.Numa(n), Value.Str(s)) => true
  case (Value.Str(s), Value.Numa(n)) => false
  case (Value.Str(s1), Value.Str(s2)) => s1 < s2
  case (Value.Numa(n1), Value.Numa(n2)) => Int.less_int(n1, n2)
}

def less_eq_value(v1: Value.value, v2: Value.value): Boolean =
  (less_value(v1, v2)) || (Value.equal_valuea(v1, v2))

} /* object Value_Lexorder */

object Increment_Reset {

def guardMatch_code(uu: List[GExp.gexp[VName.vname, Value.value]],
                     uv: List[GExp.gexp[VName.vname, Value.value]]):
      Boolean
  =
  (uu, uv) match {
  case (List(GExp.Eq(AExp.V(VName.I(ia)), AExp.L(Value.Numa(na)))),
         List(GExp.Eq(AExp.V(VName.I(i)), AExp.L(Value.Numa(n)))))
    => (Nat.equal_nata(ia, Nat.zero_nata)) && (Nat.equal_nata(i, Nat.zero_nata))
  case (Nil, uv) => false
  case (GExp.Bc(vb) :: va, uv) => false
  case (GExp.Eq(AExp.L(vd), vc) :: va, uv) => false
  case (GExp.Eq(AExp.V(VName.R(ve)), vc) :: va, uv) => false
  case (GExp.Eq(AExp.Plus(vd, ve), vc) :: va, uv) => false
  case (GExp.Eq(AExp.Minus(vd, ve), vc) :: va, uv) => false
  case (GExp.Eq(AExp.Times(vd, ve), vc) :: va, uv) => false
  case (GExp.Eq(vb, AExp.L(Value.Str(ve))) :: va, uv) => false
  case (GExp.Eq(vb, AExp.V(vd)) :: va, uv) => false
  case (GExp.Eq(vb, AExp.Plus(vd, ve)) :: va, uv) => false
  case (GExp.Eq(vb, AExp.Minus(vd, ve)) :: va, uv) => false
  case (GExp.Eq(vb, AExp.Times(vd, ve)) :: va, uv) => false
  case (GExp.Gt(vb, vc) :: va, uv) => false
  case (GExp.In(vb, vc) :: va, uv) => false
  case (GExp.Nor(vb, vc) :: va, uv) => false
  case (v :: vb :: vc, uv) => false
  case (uu, Nil) => false
  case (uu, GExp.Bc(vb) :: va) => false
  case (uu, GExp.Eq(AExp.L(vd), vc) :: va) => false
  case (uu, GExp.Eq(AExp.V(VName.R(ve)), vc) :: va) => false
  case (uu, GExp.Eq(AExp.Plus(vd, ve), vc) :: va) => false
  case (uu, GExp.Eq(AExp.Minus(vd, ve), vc) :: va) => false
  case (uu, GExp.Eq(AExp.Times(vd, ve), vc) :: va) => false
  case (uu, GExp.Eq(vb, AExp.L(Value.Str(ve))) :: va) => false
  case (uu, GExp.Eq(vb, AExp.V(vd)) :: va) => false
  case (uu, GExp.Eq(vb, AExp.Plus(vd, ve)) :: va) => false
  case (uu, GExp.Eq(vb, AExp.Minus(vd, ve)) :: va) => false
  case (uu, GExp.Eq(vb, AExp.Times(vd, ve)) :: va) => false
  case (uu, GExp.Gt(vb, vc) :: va) => false
  case (uu, GExp.In(vb, vc) :: va) => false
  case (uu, GExp.Nor(vb, vc) :: va) => false
  case (uu, v :: vb :: vc) => false
}

def guardMatch[A, B](t1: Transition.transition_ext[Value.value, A],
                      t2: Transition.transition_ext[Value.value, B]):
      Boolean
  =
  guardMatch_code(Transition.Guards[Value.value, A](t1),
                   Transition.Guards[Value.value, B](t2))

def outputMatch_code(uu: List[AExp.aexp[VName.vname, Value.value]],
                      uv: List[AExp.aexp[VName.vname, Value.value]]):
      Boolean
  =
  (uu, uv) match {
  case (List(AExp.L(Value.Numa(na))), List(AExp.L(Value.Numa(n)))) => true
  case (Nil, uv) => false
  case (AExp.L(Value.Str(vc)) :: va, uv) => false
  case (AExp.V(vb) :: va, uv) => false
  case (AExp.Plus(vb, vc) :: va, uv) => false
  case (AExp.Minus(vb, vc) :: va, uv) => false
  case (AExp.Times(vb, vc) :: va, uv) => false
  case (v :: vb :: vc, uv) => false
  case (uu, Nil) => false
  case (uu, AExp.L(Value.Str(vc)) :: va) => false
  case (uu, AExp.V(vb) :: va) => false
  case (uu, AExp.Plus(vb, vc) :: va) => false
  case (uu, AExp.Minus(vb, vc) :: va) => false
  case (uu, AExp.Times(vb, vc) :: va) => false
  case (uu, v :: vb :: vc) => false
}

def outputMatch[A, B](t1: Transition.transition_ext[Value.value, A],
                       t2: Transition.transition_ext[Value.value, B]):
      Boolean
  =
  outputMatch_code(Transition.Outputs[Value.value, A](t1),
                    Transition.Outputs[Value.value, B](t2))

def initialiseReg(t: Transition.transition_ext[Value.value, Unit],
                   newReg: Nat.nat):
      Transition.transition_ext[Value.value, Unit]
  =
  Transition.transition_exta[Value.value,
                              Unit](Transition.Label[Value.value, Unit](t),
                                     Transition.Arity[Value.value, Unit](t),
                                     Transition.Guards[Value.value, Unit](t),
                                     Transition.Outputs[Value.value, Unit](t),
                                     (newReg,
                                       AExp.L[Value.value,
       VName.vname](Value.Numa(Int.zero_int))) ::
                                       Transition.Updates[Value.value, Unit](t),
                                     ())

def struct_replace_all(e: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Value.value, Unit]))],
                        old: Transition.transition_ext[Value.value, Unit],
                        newa: Transition.transition_ext[Value.value, Unit]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat),
                    Transition.transition_ext[Value.value, Unit]))]
  =
  {
    val to_replace:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Value.value, Unit]))]
      = FSet.ffilter[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Value.value,
            Unit]))](((a: (List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Value.value, Unit])))
                        =>
                       {
                         val (_, aa):
                               (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Value.value,
                      Unit]))
                           = a
                         val (ab, b):
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Value.value, Unit])
                           = aa;
                         ({
                            val (_, _): (Nat.nat, Nat.nat) = ab;
                            ((t: Transition.transition_ext[Value.value, Unit])
                               =>
                              Transition.same_structure[Value.value](t, old))
                          })(b)
                       }),
                      e)
    val replacements:
          FSet.fset[(List[Nat.nat],
                      Transition.transition_ext[Value.value, Unit])]
      = FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Value.value, Unit])),
                     (List[Nat.nat],
                       Transition.transition_ext[Value.value,
          Unit])](((a: (List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Value.value, Unit])))
                     =>
                    {
                      val (uid, aa):
                            (List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Value.value, Unit]))
                        = a
                      val (ab, b):
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Value.value, Unit])
                        = aa;
                      ({
                         val (_, _): (Nat.nat, Nat.nat) = ab;
                         ((_: Transition.transition_ext[Value.value, Unit]) =>
                           (uid, newa))
                       })(b)
                    }),
                   to_replace);
    Inference.replace_transitions[Value.value](e,
        FSet.sorted_list_of_fset[(List[Nat.nat],
                                   Transition.transition_ext[Value.value,
                      Unit])](replacements))
  }

def insert_increment_2(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                        newa: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Value.value, Unit]))],
                        uu: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Value.value, Unit]))],
                        old: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Value.value, Unit]))],
                        check:
                          (FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Value.value,
                          Unit])]) =>
                            Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Value.value, Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Value.value, Unit] =
      Inference.get_by_ids[Value.value](newa, t1ID)
    val t2: Transition.transition_ext[Value.value, Unit] =
      Inference.get_by_ids[Value.value](newa, t2ID);
    (if ((guardMatch[Unit, Unit](t1, t2)) && (outputMatch[Unit, Unit](t1, t2)))
      {
        val r: Nat.nat = (Inference.max_reg[Value.value](newa) match {
                            case None => Nat.Nata((1))
                            case Some(r) => Nat.plus_nata(r, Nat.Nata((1)))
                          })
        val newReg: VName.vname = VName.R(r)
        val newT1: Transition.transition_ext[Value.value, Unit] =
          Transition.transition_exta[Value.value,
                                      Unit](Transition.Label[Value.value,
                      Unit](t1),
     Transition.Arity[Value.value, Unit](t1), Nil,
     List(AExp.Plus[VName.vname,
                     Value.value](AExp.V[VName.vname, Value.value](newReg),
                                   AExp.V[VName.vname,
   Value.value](VName.I(Nat.zero_nata)))),
     (r, AExp.Plus[VName.vname,
                    Value.value](AExp.V[VName.vname, Value.value](newReg),
                                  AExp.V[VName.vname,
  Value.value](VName.I(Nat.zero_nata)))) ::
       Transition.Updates[Value.value, Unit](t1),
     ())
        val newT2: Transition.transition_ext[Value.value, Unit] =
          Transition.transition_exta[Value.value,
                                      Unit](Transition.Label[Value.value,
                      Unit](t2),
     Transition.Arity[Value.value, Unit](t2), Nil,
     List(AExp.Plus[VName.vname,
                     Value.value](AExp.V[VName.vname, Value.value](newReg),
                                   AExp.V[VName.vname,
   Value.value](VName.I(Nat.zero_nata)))),
     (r, AExp.Plus[VName.vname,
                    Value.value](AExp.V[VName.vname, Value.value](newReg),
                                  AExp.V[VName.vname,
  Value.value](VName.I(Nat.zero_nata)))) ::
       Transition.Updates[Value.value, Unit](t2),
     ())
        val to_initialise:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Value.value, Unit]))]
          = FSet.ffilter[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Value.value,
                Unit]))](((a: (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Value.value,
                     Unit])))
                            =>
                           {
                             val (_, aa):
                                   (List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Value.value,
                          Unit]))
                               = a
                             val (ab, b):
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Value.value,
                        Unit])
                               = aa;
                             ({
                                val (_, to): (Nat.nat, Nat.nat) = ab;
                                ((t: Transition.transition_ext[Value.value,
                        Unit])
                                   =>
                                  ((Nat.equal_nata(to,
            Inference.dest[Value.value](t1ID,
 newa))) || (Nat.equal_nata(to, Inference.dest[Value.value](t2ID,
                     newa)))) && ((! (Transition.equal_transition_exta[Value.value,
                                Unit](t, t1))) && (! (Transition.equal_transition_exta[Value.value,
        Unit](t, t2)))))
                              })(b)
                           }),
                          newa)
        val initialisedTrans:
              FSet.fset[(List[Nat.nat],
                          Transition.transition_ext[Value.value, Unit])]
          = FSet.fimage[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Value.value, Unit])),
                         (List[Nat.nat],
                           Transition.transition_ext[Value.value,
              Unit])](((a: (List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Value.value, Unit])))
                         =>
                        {
                          val (uid, aa):
                                (List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Value.value,
                       Unit]))
                            = a
                          val (ab, b):
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Value.value, Unit])
                            = aa;
                          ({
                             val (_, _): (Nat.nat, Nat.nat) = ab;
                             ((t: Transition.transition_ext[Value.value, Unit])
                                =>
                               (uid, initialiseReg(t, r)))
                           })(b)
                        }),
                       to_initialise)
        val initialised:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Value.value, Unit]))]
          = Inference.replace_transitions[Value.value](newa,
                FSet.sorted_list_of_fset[(List[Nat.nat],
   Transition.transition_ext[Value.value, Unit])](initialisedTrans))
        val rep: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Value.value, Unit]))]
          = struct_replace_all(struct_replace_all(initialised, t2, newT2), t1,
                                newT1);
        (if (check(Inference.tm[Value.value](rep)))
          Some[FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Value.value,
                Unit]))]](rep)
          else None)
      }
      else None)
  }

} /* object Increment_Reset */

object Weak_Subsumption {

def maxBy[A, B : Orderings.linorder](f: A => B, a: A, b: A): A =
  (if (Orderings.less[B](f(b), f(a))) a else b)

def weak_subsumption[A : HOL.equal : Orderings.linorder](t1ID: List[Nat.nat],
                  t2ID: List[Nat.nat], s: Nat.nat,
                  newa: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit]))],
                  uu: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit]))],
                  old: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit]))],
                  check:
                    (FSet.fset[((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit])]) =>
                      Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](newa, t1ID)
    val t2: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](newa, t2ID);
    (if (Transition.same_structure[A](t1, t2))
      {
        val maxT: Transition.transition_ext[A, Unit] =
          maxBy[Transition.transition_ext[A, Unit],
                 (Nat.nat,
                   List[AExp.aexp[VName.vname,
                                   A]])](((x:
     Transition.transition_ext[A, Unit])
    =>
   ((Fun.comp[List[(Nat.nat, AExp.aexp[VName.vname, A])], Nat.nat,
               Transition.transition_ext[A,
  Unit]](((a: List[(Nat.nat, AExp.aexp[VName.vname, A])]) =>
           Nat.Nata(a.par.length)),
          ((a: Transition.transition_ext[A, Unit]) =>
            Transition.Updates[A, Unit](a)))).apply(x),
     Lista.map[(Nat.nat, AExp.aexp[VName.vname, A]),
                AExp.aexp[VName.vname,
                           A]](((a: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                                 a._2),
                                Transition.Updates[A, Unit](x)))),
  t1, t2)
        val minT: Transition.transition_ext[A, Unit] =
          (if (Transition.equal_transition_exta[A, Unit](maxT, t1)) t2 else t1)
        val newEFSMmax:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]
          = Inference.replace_all[A](newa, List(t1ID, t2ID), maxT);
        (if (check(Inference.tm[A](newEFSMmax)))
          Some[FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))]](newEFSMmax)
          else {
                 val newEFSMmin:
                       FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit]))]
                   = Inference.replace_all[A](newa, List(t1ID, t2ID), minT);
                 (if (check(Inference.tm[A](newEFSMmin)))
                   Some[FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A,
                         Unit]))]](newEFSMmin)
                   else None)
               })
      }
      else None)
  }

} /* object Weak_Subsumption */

object Least_Upper_Bound {

def literal_args[A, B](x0: GExp.gexp[A, B]): Boolean = x0 match {
  case GExp.Bc(v) => false
  case GExp.Eq(AExp.V(uu), AExp.L(uv)) => true
  case GExp.In(uw, ux) => true
  case GExp.Eq(AExp.L(v), uz) => false
  case GExp.Eq(AExp.Plus(v, va), uz) => false
  case GExp.Eq(AExp.Minus(v, va), uz) => false
  case GExp.Eq(AExp.Times(v, va), uz) => false
  case GExp.Eq(uy, AExp.V(v)) => false
  case GExp.Eq(uy, AExp.Plus(v, va)) => false
  case GExp.Eq(uy, AExp.Minus(v, va)) => false
  case GExp.Eq(uy, AExp.Times(v, va)) => false
  case GExp.Gt(va, v) => false
  case GExp.Nor(v, va) => (literal_args[A, B](v)) && (literal_args[A, B](va))
}

def all_literal_args[A, B](t: Transition.transition_ext[A, B]): Boolean =
  Lista.list_all[GExp.gexp[VName.vname,
                            A]](((a: GExp.gexp[VName.vname, A]) =>
                                  literal_args[VName.vname, A](a)),
                                 Transition.Guards[A, B](t))

def merge_in_in[A : HOL.equal, B](v: A, l: List[B], x2: List[GExp.gexp[A, B]]):
      List[GExp.gexp[A, B]]
  =
  (v, l, x2) match {
  case (v, l, Nil) => List(GExp.In[A, B](v, l))
  case (va, la, GExp.Eq(AExp.V(v), AExp.L(l)) :: t) =>
    (if (HOL.eq[A](va, v)) GExp.In[A, B](va, Lista.insert[B](l, la)) :: t
      else GExp.Eq[A, B](AExp.V[A, B](v), AExp.L[B, A](l)) ::
             merge_in_in[A, B](va, la, t))
  case (va, la, GExp.In(v, l) :: t) =>
    (if (HOL.eq[A](va, v))
      GExp.In[A, B](va, Lista.union[B].apply(la).apply(l)) :: t
      else GExp.In[A, B](v, l) :: merge_in_in[A, B](va, la, t))
  case (v, l, GExp.Bc(va) :: t) =>
    GExp.Bc[A, B](va) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Eq(AExp.L(vc), vb) :: t) =>
    GExp.Eq[A, B](AExp.L[B, A](vc), vb) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Eq(AExp.Plus(vc, vd), vb) :: t) =>
    GExp.Eq[A, B](AExp.Plus[A, B](vc, vd), vb) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Eq(AExp.Minus(vc, vd), vb) :: t) =>
    GExp.Eq[A, B](AExp.Minus[A, B](vc, vd), vb) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Eq(AExp.Times(vc, vd), vb) :: t) =>
    GExp.Eq[A, B](AExp.Times[A, B](vc, vd), vb) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Eq(va, AExp.V(vc)) :: t) =>
    GExp.Eq[A, B](va, AExp.V[A, B](vc)) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Eq(va, AExp.Plus(vc, vd)) :: t) =>
    GExp.Eq[A, B](va, AExp.Plus[A, B](vc, vd)) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Eq(va, AExp.Minus(vc, vd)) :: t) =>
    GExp.Eq[A, B](va, AExp.Minus[A, B](vc, vd)) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Eq(va, AExp.Times(vc, vd)) :: t) =>
    GExp.Eq[A, B](va, AExp.Times[A, B](vc, vd)) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Gt(va, vb) :: t) =>
    GExp.Gt[A, B](va, vb) :: merge_in_in[A, B](v, l, t)
  case (v, l, GExp.Nor(va, vb) :: t) =>
    GExp.Nor[A, B](va, vb) :: merge_in_in[A, B](v, l, t)
}

def merge_in_eq[A : HOL.equal,
                 B : HOL.equal](v: A, l: B, x2: List[GExp.gexp[A, B]]):
      List[GExp.gexp[A, B]]
  =
  (v, l, x2) match {
  case (v, l, Nil) => List(GExp.Eq[A, B](AExp.V[A, B](v), AExp.L[B, A](l)))
  case (va, la, GExp.Eq(AExp.V(v), AExp.L(l)) :: t) =>
    (if ((HOL.eq[A](va, v)) && (! (HOL.eq[B](la, l))))
      GExp.In[A, B](va, List(la, l)) :: t
      else GExp.Eq[A, B](AExp.V[A, B](v), AExp.L[B, A](l)) ::
             merge_in_eq[A, B](va, la, t))
  case (va, la, GExp.In(v, l) :: t) =>
    (if (HOL.eq[A](va, v)) GExp.In[A, B](va, (la :: l).par.distinct.toList) :: t
      else GExp.In[A, B](v, l) :: merge_in_eq[A, B](va, la, t))
  case (v, l, GExp.Bc(va) :: t) =>
    GExp.Bc[A, B](va) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Eq(AExp.L(vc), vb) :: t) =>
    GExp.Eq[A, B](AExp.L[B, A](vc), vb) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Eq(AExp.Plus(vc, vd), vb) :: t) =>
    GExp.Eq[A, B](AExp.Plus[A, B](vc, vd), vb) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Eq(AExp.Minus(vc, vd), vb) :: t) =>
    GExp.Eq[A, B](AExp.Minus[A, B](vc, vd), vb) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Eq(AExp.Times(vc, vd), vb) :: t) =>
    GExp.Eq[A, B](AExp.Times[A, B](vc, vd), vb) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Eq(va, AExp.V(vc)) :: t) =>
    GExp.Eq[A, B](va, AExp.V[A, B](vc)) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Eq(va, AExp.Plus(vc, vd)) :: t) =>
    GExp.Eq[A, B](va, AExp.Plus[A, B](vc, vd)) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Eq(va, AExp.Minus(vc, vd)) :: t) =>
    GExp.Eq[A, B](va, AExp.Minus[A, B](vc, vd)) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Eq(va, AExp.Times(vc, vd)) :: t) =>
    GExp.Eq[A, B](va, AExp.Times[A, B](vc, vd)) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Gt(va, vb) :: t) =>
    GExp.Gt[A, B](va, vb) :: merge_in_eq[A, B](v, l, t)
  case (v, l, GExp.Nor(va, vb) :: t) =>
    GExp.Nor[A, B](va, vb) :: merge_in_eq[A, B](v, l, t)
}

def merge_guards[A : HOL.equal,
                  B : HOL.equal](x0: List[GExp.gexp[A, B]],
                                  g2: List[GExp.gexp[A, B]]):
      List[GExp.gexp[A, B]]
  =
  (x0, g2) match {
  case (Nil, g2) => g2
  case (GExp.Eq(AExp.V(v), AExp.L(l)) :: t, g2) =>
    merge_guards[A, B](t, merge_in_eq[A, B](v, l, g2))
  case (GExp.In(v, l) :: t, g2) =>
    merge_guards[A, B](t, merge_in_in[A, B](v, l, g2))
  case (GExp.Bc(v) :: t, g2) => GExp.Bc[A, B](v) :: merge_guards[A, B](t, g2)
  case (GExp.Eq(AExp.L(vb), va) :: t, g2) =>
    GExp.Eq[A, B](AExp.L[B, A](vb), va) :: merge_guards[A, B](t, g2)
  case (GExp.Eq(AExp.Plus(vb, vc), va) :: t, g2) =>
    GExp.Eq[A, B](AExp.Plus[A, B](vb, vc), va) :: merge_guards[A, B](t, g2)
  case (GExp.Eq(AExp.Minus(vb, vc), va) :: t, g2) =>
    GExp.Eq[A, B](AExp.Minus[A, B](vb, vc), va) :: merge_guards[A, B](t, g2)
  case (GExp.Eq(AExp.Times(vb, vc), va) :: t, g2) =>
    GExp.Eq[A, B](AExp.Times[A, B](vb, vc), va) :: merge_guards[A, B](t, g2)
  case (GExp.Eq(v, AExp.V(vb)) :: t, g2) =>
    GExp.Eq[A, B](v, AExp.V[A, B](vb)) :: merge_guards[A, B](t, g2)
  case (GExp.Eq(v, AExp.Plus(vb, vc)) :: t, g2) =>
    GExp.Eq[A, B](v, AExp.Plus[A, B](vb, vc)) :: merge_guards[A, B](t, g2)
  case (GExp.Eq(v, AExp.Minus(vb, vc)) :: t, g2) =>
    GExp.Eq[A, B](v, AExp.Minus[A, B](vb, vc)) :: merge_guards[A, B](t, g2)
  case (GExp.Eq(v, AExp.Times(vb, vc)) :: t, g2) =>
    GExp.Eq[A, B](v, AExp.Times[A, B](vb, vc)) :: merge_guards[A, B](t, g2)
  case (GExp.Gt(v, va) :: t, g2) =>
    GExp.Gt[A, B](v, va) :: merge_guards[A, B](t, g2)
  case (GExp.Nor(v, va) :: t, g2) =>
    GExp.Nor[A, B](v, va) :: merge_guards[A, B](t, g2)
}

def lob_aux[A : HOL.equal](t1: Transition.transition_ext[A, Unit],
                            t2: Transition.transition_ext[A, Unit]):
      Option[Transition.transition_ext[A, Unit]]
  =
  (if ((Lista.equal_lista[AExp.aexp[VName.vname,
                                     A]](Transition.Outputs[A, Unit](t1),
  Transition.Outputs[A, Unit](t2))) && ((Lista.equal_lista[(Nat.nat,
                     AExp.aexp[VName.vname,
                                A])](Transition.Updates[A, Unit](t1),
                                      Transition.Updates[A,
                  Unit](t2))) && ((all_literal_args[A,
             Unit](t1)) && (all_literal_args[A, Unit](t2)))))
    Some[Transition.transition_ext[A, Unit]](Transition.transition_exta[A,
                                 Unit](Transition.Label[A, Unit](t1),
Transition.Arity[A, Unit](t1),
(merge_guards[VName.vname,
               A](Transition.Guards[A, Unit](t1),
                   Transition.Guards[A, Unit](t2))).par.distinct.toList,
Transition.Outputs[A, Unit](t1), Transition.Updates[A, Unit](t1), ()))
    else None)

def lob[A : HOL.equal](t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                        newa: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                        uu: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                        old: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                        uv: (FSet.fset[((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit])]) =>
                              Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](newa, t1ID)
    val t2: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](newa, t2ID);
    (lob_aux[A](t1, t2) match {
       case None => None
       case Some(lob_t) =>
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit]))]](Inference.replace_transitions[A](newa,
                   List((t1ID, lob_t), (t2ID, lob_t))))
     })
  }

} /* object Least_Upper_Bound */

object PTA_Generalisation {

abstract sealed class value_type
final case class N() extends value_type
final case class S() extends value_type

def equal_value_typea(x0: value_type, x1: value_type): Boolean = (x0, x1) match
  {
  case (N(), S()) => false
  case (S(), N()) => false
  case (S(), S()) => true
  case (N(), N()) => true
}

def less_value_type(uu: value_type, uv: value_type): Boolean = (uu, uv) match {
  case (N(), S()) => true
  case (S(), uv) => false
  case (uu, N()) => false
}

def less_eq_value_type(v1: value_type, v2: value_type): Boolean =
  (less_value_type(v1, v2)) || (equal_value_typea(v1, v2))

def typeSig[A : Value.aexp_value](v: AExp.aexp[VName.vname, A]): value_type =
  (v match {
     case AExp.L(va) => (if (Value.is_num[A](va)) N() else S())
     case AExp.V(_) => N()
     case AExp.Plus(_, _) => N()
     case AExp.Minus(_, _) => N()
     case AExp.Times(_, _) => N()
   })

def tag[A : Value.aexp_value](uu: Option[(String, (Nat.nat, List[value_type]))],
                               x1: List[List[(Nat.nat,
       (List[Nat.nat], Transition.transition_ext[A, Unit]))]]):
      List[(Option[(String, (Nat.nat, List[value_type]))],
             ((String, (Nat.nat, List[value_type])),
               List[(Nat.nat,
                      (List[Nat.nat], Transition.transition_ext[A, Unit]))]))]
  =
  (uu, x1) match {
  case (uu, Nil) => Nil
  case (t, g :: gs) =>
    {
      val (_, (_, head)):
            (Nat.nat, (List[Nat.nat], Transition.transition_ext[A, Unit]))
        = g.head
      val struct: (String, (Nat.nat, List[value_type])) =
        (Transition.Label[A, Unit](head),
          (Transition.Arity[A, Unit](head),
            Lista.map[AExp.aexp[VName.vname, A],
                       value_type](((a: AExp.aexp[VName.vname, A]) =>
                                     typeSig[A](a)),
                                    Transition.Outputs[A, Unit](head))));
      (t, (struct, g)) ::
        tag[A](Some[(String, (Nat.nat, List[value_type]))](struct), gs)
    }
}

def target_fold[A : Orderings.linorder, B, C, D, E, F,
                 G](tRegs: Map[A, B],
                     ts: List[(C, (D, (Map[A, B], (E, (F, G)))))],
                     b: List[(Map[A, B], (C, (D, (Map[A, B], (E, (F, G))))))]):
      List[(Map[A, B], (C, (D, (Map[A, B], (E, (F, G))))))]
  =
  (Lista.fold[(C, (D, (Map[A, B], (E, (F, G))))),
               (List[(Map[A, B], (C, (D, (Map[A, B], (E, (F, G))))))],
                 Map[A, B])](((a: (C, (D, (Map[A, B], (E, (F, G)))))) =>
                               {
                                 val (s, (oldregs,
   (regs, (inputs, (tid, ta))))):
                                       (C, (D, (Map[A, B], (E, (F, G)))))
                                   = a;
                                 ((aa: (List[(Map[A, B],
       (C, (D, (Map[A, B], (E, (F, G))))))],
 Map[A, B]))
                                    =>
                                   {
                                     val (acc, tRegsa):
   (List[(Map[A, B], (C, (D, (Map[A, B], (E, (F, G))))))], Map[A, B])
                                       = aa
                                     val ab: Map[A, B] =
                                       (if ((regs.keySet.toList).isEmpty) tRegsa
 else regs);
                                     (acc ++
List((tRegsa, (s, (oldregs, (regs, (inputs, (tid, ta))))))),
                                       ab)
                                   })
                               }),
                              ts, (b.par.reverse.toList, tRegs)))._1

def target[A](tRegs: Map[Nat.nat, Option[A]],
               ts: List[(Nat.nat,
                          (Map[Nat.nat, Option[A]],
                            (Map[Nat.nat, Option[A]],
                              (List[A],
                                (List[Nat.nat],
                                  Transition.transition_ext[A, Unit])))))]):
      List[(Map[Nat.nat, Option[A]],
             (Nat.nat,
               (Map[Nat.nat, Option[A]],
                 (Map[Nat.nat, Option[A]],
                   (List[A],
                     (List[Nat.nat], Transition.transition_ext[A, Unit]))))))]
  =
  target_fold[Nat.nat, Option[A], Nat.nat, Map[Nat.nat, Option[A]], List[A],
               List[Nat.nat],
               Transition.transition_ext[A, Unit]](tRegs, ts, Nil)

def unzip_3_tailrec_rev[A, B,
                         C](x0: List[(A, (B, C))],
                             x1: (List[A], (List[B], List[C]))):
      (List[A], (List[B], List[C]))
  =
  (x0, x1) match {
  case (Nil, (as, (bs, cs))) => (as, (bs, cs))
  case ((a, (b, c)) :: t, (as, (bs, cs))) =>
    unzip_3_tailrec_rev[A, B, C](t, (a :: as, (b :: bs, c :: cs)))
}

def unzip_3_tailrec[A, B, C](l: List[(A, (B, C))]):
      (List[A], (List[B], List[C]))
  =
  {
    val (as, (bs, cs)): (List[A], (List[B], List[C])) =
      unzip_3_tailrec_rev[A, B, C](l, (Nil, (Nil, Nil)));
    (as.par.reverse.toList, (bs.par.reverse.toList, cs.par.reverse.toList))
  }

def unzip_3[A, B, C](l: List[(A, (B, C))]): (List[A], (List[B], List[C])) =
  unzip_3_tailrec[A, B, C](l)

def find_outputs[A : HOL.equal : Orderings.order : Value.aexp_value](x0:
                               List[List[AExp.aexp[VName.vname, A]]],
                              uu: FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                              uv: List[List[(String, (List[A], List[A]))]],
                              uw: List[(List[Nat.nat],
 Transition.transition_ext[A, Unit])]):
      Option[List[AExp.aexp[VName.vname, A]]]
  =
  (x0, uu, uv, uw) match {
  case (Nil, uu, uv, uw) => None
  case (h :: t, e, l, g) =>
    {
      val outputs:
            FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))]
        = Lista.fold[(List[Nat.nat], Transition.transition_ext[A, Unit]),
                      FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A,
                       Unit]))]](((a: (List[Nat.nat],
Transition.transition_ext[A, Unit]))
                                    =>
                                   {
                                     val (tids, ta):
   (List[Nat.nat], Transition.transition_ext[A, Unit])
                                       = a;
                                     ((acc:
 FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
=>
                                       Inference.replace_transition[A](acc,
                                tids,
                                Transition.Outputs_update[A,
                   Unit](((_: List[AExp.aexp[VName.vname, A]]) => h), ta)))
                                   }),
                                  g, e);
      (if (EFSM.accepts_log[A](Set.seta[List[(String, (List[A], List[A]))]](l),
                                Inference.tm[A](outputs)))
        Some[List[AExp.aexp[VName.vname, A]]](h)
        else find_outputs[A](t, e, l, g))
    }
}

def find_updates_outputs[A : HOL.equal : Orderings.order : Value.aexp_value](x0:
                                       List[List[(Nat.nat,
           AExp.aexp[VName.vname, A])]],
                                      uu: List[List[AExp.aexp[VName.vname, A]]],
                                      uv:
FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                      uw:
List[List[(String, (List[A], List[A]))]],
                                      ux:
List[(List[Nat.nat], Transition.transition_ext[A, Unit])]):
      Option[(List[AExp.aexp[VName.vname, A]],
               List[(Nat.nat, AExp.aexp[VName.vname, A])])]
  =
  (x0, uu, uv, uw, ux) match {
  case (Nil, uu, uv, uw, ux) => None
  case (h :: t, p, e, l, g) =>
    {
      val updates:
            FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))]
        = Lista.fold[(List[Nat.nat], Transition.transition_ext[A, Unit]),
                      FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A,
                       Unit]))]](((a: (List[Nat.nat],
Transition.transition_ext[A, Unit]))
                                    =>
                                   {
                                     val (tids, ta):
   (List[Nat.nat], Transition.transition_ext[A, Unit])
                                       = a;
                                     ((acc:
 FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
=>
                                       Inference.replace_transition[A](acc,
                                tids,
                                Transition.Updates_update[A,
                   Unit](((_: List[(Nat.nat, AExp.aexp[VName.vname, A])]) => h),
                          ta)))
                                   }),
                                  g, e);
      (find_outputs[A](p, updates, l,
                        Lista.map[(List[Nat.nat],
                                    Transition.transition_ext[A, Unit]),
                                   (List[Nat.nat],
                                     Transition.transition_ext[A,
                        Unit])](((a: (List[Nat.nat],
                                       Transition.transition_ext[A, Unit]))
                                   =>
                                  {
                                    val (id, ta):
  (List[Nat.nat], Transition.transition_ext[A, Unit])
                                      = a;
                                    (id, Transition.Updates_update[A,
                            Unit](((_: List[(Nat.nat,
      AExp.aexp[VName.vname, A])])
                                     =>
                                    h),
                                   ta))
                                  }),
                                 g))
         match {
         case None => find_updates_outputs[A](t, p, e, l, g)
         case Some(pp) =>
           Some[(List[AExp.aexp[VName.vname, A]],
                  List[(Nat.nat, AExp.aexp[VName.vname, A])])]((pp, h))
       })
    }
}

def updates_for[A : HOL.equal](u: List[(Nat.nat, AExp.aexp[VName.vname, A])]):
      List[List[(Nat.nat, AExp.aexp[VName.vname, A])]]
  =
  {
    val uf: Map[Nat.nat, (List[AExp.aexp[VName.vname, A]])] =
      Lista.fold[(Nat.nat, AExp.aexp[VName.vname, A]),
                  Map[Nat.nat, (List[AExp.aexp[VName.vname,
        A]])]](((a: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                 {
                   val (r, ua): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
                   ((f: Map[Nat.nat, (List[AExp.aexp[VName.vname, A]])]) =>
                     f + (r -> (ua :: f(r))))
                 }),
                u, scala.collection.immutable.Map().withDefaultValue(Nil));
    Lista.map[Nat.nat,
               List[(Nat.nat,
                      AExp.aexp[VName.vname,
                                 A])]](((r: Nat.nat) =>
 Lista.map[AExp.aexp[VName.vname, A],
            (Nat.nat,
              AExp.aexp[VName.vname,
                         A])](((a: AExp.aexp[VName.vname, A]) => (r, a)),
                               uf(r))),
uf.keySet.toList)
  }

def standardise_group_outputs_updates[A : HOL.equal : Orderings.order : Value.aexp_value](e:
            FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))],
           l: List[List[(String, (List[A], List[A]))]],
           g: List[(List[Nat.nat], Transition.transition_ext[A, Unit])]):
      List[(List[Nat.nat], Transition.transition_ext[A, Unit])]
  =
  {
    val update_groups: List[List[(Nat.nat, AExp.aexp[VName.vname, A])]] =
      Lista.product_lists[(Nat.nat,
                            AExp.aexp[VName.vname,
                                       A])](updates_for[A]((Lista.maps[(List[Nat.nat],
                                 Transition.transition_ext[A, Unit]),
                                (Nat.nat,
                                  AExp.aexp[VName.vname,
     A])](Fun.comp[Transition.transition_ext[A, Unit],
                    List[(Nat.nat, AExp.aexp[VName.vname, A])],
                    (List[Nat.nat],
                      Transition.transition_ext[A,
         Unit])](((a: Transition.transition_ext[A, Unit]) =>
                   Transition.Updates[A, Unit](a)),
                  ((a: (List[Nat.nat], Transition.transition_ext[A, Unit])) =>
                    a._2)),
           g)).par.distinct.toList))
    val update_groups_subs: List[List[(Nat.nat, AExp.aexp[VName.vname, A])]] =
      Lista.fold[List[(Nat.nat, AExp.aexp[VName.vname, A])],
                  List[List[(Nat.nat,
                              AExp.aexp[VName.vname,
 A])]]](Fun.comp[List[List[(Nat.nat, AExp.aexp[VName.vname, A])]],
                  (List[List[(Nat.nat, AExp.aexp[VName.vname, A])]]) =>
                    List[List[(Nat.nat, AExp.aexp[VName.vname, A])]],
                  List[(Nat.nat,
                         AExp.aexp[VName.vname,
                                    A])]](Lista.union[List[(Nat.nat,
                     AExp.aexp[VName.vname, A])]],
   ((a: List[(Nat.nat, AExp.aexp[VName.vname, A])]) =>
     Lista.subseqs[(Nat.nat, AExp.aexp[VName.vname, A])](a))),
         update_groups, Nil)
    val output_groups: List[List[AExp.aexp[VName.vname, A]]] =
      Lista.product_lists[AExp.aexp[VName.vname,
                                     A]](Lista.transpose[AExp.aexp[VName.vname,
                            A]]((Lista.map[(List[Nat.nat],
     Transition.transition_ext[A, Unit]),
    List[AExp.aexp[VName.vname,
                    A]]](Fun.comp[Transition.transition_ext[A, Unit],
                                   List[AExp.aexp[VName.vname, A]],
                                   (List[Nat.nat],
                                     Transition.transition_ext[A,
                        Unit])](((a: Transition.transition_ext[A, Unit]) =>
                                  Transition.Outputs[A, Unit](a)),
                                 ((a: (List[Nat.nat],
Transition.transition_ext[A, Unit]))
                                    =>
                                   a._2)),
                          g)).par.distinct.toList));
    (find_updates_outputs[A](update_groups_subs, output_groups, e, l, g) match {
       case None => g
       case Some((p, u)) =>
         Lista.map[(List[Nat.nat], Transition.transition_ext[A, Unit]),
                    (List[Nat.nat],
                      Transition.transition_ext[A,
         Unit])](((a: (List[Nat.nat], Transition.transition_ext[A, Unit])) =>
                   {
                     val (id, t):
                           (List[Nat.nat], Transition.transition_ext[A, Unit])
                       = a;
                     (id, Transition.Updates_update[A,
             Unit](((_: List[(Nat.nat, AExp.aexp[VName.vname, A])]) => u),
                    Transition.Outputs_update[A,
       Unit](((_: List[AExp.aexp[VName.vname, A]]) => p), t)))
                   }),
                  g)
     })
  }

def find_initialisation_of_trace[A : HOL.equal : Value.aexp_value](uu: Nat.nat,
                            x1: List[(String, (List[A], List[A]))],
                            uv: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                            uw: Nat.nat, ux: Map[Nat.nat, Option[A]]):
      Option[(List[Nat.nat], Transition.transition_ext[A, Unit])]
  =
  (uu, x1, uv, uw, ux) match {
  case (uu, Nil, uv, uw, ux) => None
  case (ra, (l, (i, uy)) :: es, e, s, r) =>
    {
      val (tids, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[A,
                Unit]))](Inference.i_possible_steps[A](e, s, r, l, i));
      (if (Lista.list_ex[(Nat.nat,
                           AExp.aexp[VName.vname,
                                      A])](((a:
       (Nat.nat, AExp.aexp[VName.vname, A]))
      =>
     {
       val (rr, u): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
       (Nat.equal_nata(rr, ra)) && (AExp.is_lit[VName.vname, A](u))
     }),
    Transition.Updates[A, Unit](t)))
        Some[(List[Nat.nat], Transition.transition_ext[A, Unit])]((tids, t))
        else find_initialisation_of_trace[A](ra, es, e, sa,
      (Transition.apply_updates[A](Transition.Updates[A, Unit](t),
                                    AExp.join_ir[A](i, r))).apply(r)))
    }
}

def find_initialisation_of[A : HOL.equal : Orderings.order : Value.aexp_value](uu:
 Nat.nat,
uv: FSet.fset[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
x2: List[List[(String, (List[A], List[A]))]]):
      List[Option[(List[Nat.nat], Transition.transition_ext[A, Unit])]]
  =
  (uu, uv, x2) match {
  case (uu, uv, Nil) => Nil
  case (r, e, h :: t) =>
    (find_initialisation_of_trace[A](r, h, e, Nat.zero_nata,
                                      AExp.null_state[Nat.nat, Option[A]])
       match {
       case None => find_initialisation_of[A](r, e, t)
       case Some(thing) =>
         Some[(List[Nat.nat], Transition.transition_ext[A, Unit])](thing) ::
           find_initialisation_of[A](r, e, t)
     })
}

def delay_initialisation_of[A : HOL.equal : Orderings.order : Value.aexp_value](r:
  Nat.nat,
 l: List[List[(String, (List[A], List[A]))]],
 e: FSet.fset[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
 tids: List[List[Nat.nat]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  Lista.fold[Option[(List[Nat.nat], Transition.transition_ext[A, Unit])],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit]))]](((x: Option[(List[Nat.nat],
                                       Transition.transition_ext[A, Unit])])
                            =>
                           (ea: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
                             =>
                           (x match {
                              case None => ea
                              case Some((i_tids, t)) =>
                                {
                                  val origins: List[Nat.nat] =
                                    Lista.map[List[Nat.nat],
       Nat.nat](((id: List[Nat.nat]) => Inference.origin[A](id, ea)), tids)
                                  val init_val: AExp.aexp[VName.vname, A] =
                                    ((Lista.filter[(Nat.nat,
             AExp.aexp[VName.vname,
                        A])](((a: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                               {
                                 val (ra, _):
                                       (Nat.nat, AExp.aexp[VName.vname, A])
                                   = a;
                                 Nat.equal_nata(r, ra)
                               }),
                              Transition.Updates[A, Unit](t))).head)._2
                                  val eaa:
FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
                                    = FSet.fimage[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
           (List[Nat.nat],
             ((Nat.nat, Nat.nat),
               Transition.transition_ext[A,
  Unit]))](((a: (List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
              =>
             {
               val (id, aa):
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
                 = a
               val (ab, b):
                     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])
                 = aa;
               ({
                  val (origin, dest): (Nat.nat, Nat.nat) = ab;
                  ((tr: Transition.transition_ext[A, Unit]) =>
                    (if (origins.contains(dest))
                      (id, ((origin, dest),
                             Transition.Updates_update[A,
                Unit](((_: List[(Nat.nat, AExp.aexp[VName.vname, A])]) =>
                        Lista.insert[(Nat.nat,
                                       AExp.aexp[VName.vname,
          A])]((r, init_val), Transition.Updates[A, Unit](tr))),
                       tr)))
                      else (if (Lista.equal_lista[Nat.nat](id, i_tids))
                             (id, ((origin, dest),
                                    Transition.Updates_update[A,
                       Unit](((_: List[(Nat.nat, AExp.aexp[VName.vname, A])]) =>
                               Lista.filter[(Nat.nat,
      AExp.aexp[VName.vname,
                 A])](((ac: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                        {
                          val (ra, _): (Nat.nat, AExp.aexp[VName.vname, A]) =
                            ac;
                          ! (Nat.equal_nata(r, ra))
                        }),
                       Transition.Updates[A, Unit](tr))),
                              tr)))
                             else (id, ((origin, dest), tr)))))
                })(b)
             }),
            ea);
                                  (if (EFSM.accepts_log[A](Set.seta[List[(String,
                                   (List[A], List[A]))]](l),
                    Inference.tm[A](eaa)))
                                    eaa else ea)
                                }
                            })),
                          find_initialisation_of[A](r, e, l), e)

def enumerate_exec_values[A](vs: List[(String, (List[A], List[A]))]): List[A] =
  Lista.fold[(String, (List[A], List[A])),
              List[A]](((a: (String, (List[A], List[A]))) =>
                         {
                           val (_, (i, p)): (String, (List[A], List[A])) = a;
                           Lista.union[A].apply(Lista.union[A].apply(i).apply(p))
                         }),
                        vs, Nil)

def enumerate_log_values[A](l: List[List[(String, (List[A], List[A]))]]):
      List[A]
  =
  Lista.fold[List[(String, (List[A], List[A]))],
              List[A]](((e: List[(String, (List[A], List[A]))]) =>
                         Lista.union[A].apply(enumerate_exec_values[A](e))),
                        l, Nil)

def trace_group_training_set[A : HOL.equal : Value.aexp_value](uu:
                         List[(List[Nat.nat],
                                Transition.transition_ext[A, Unit])],
                        uv: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                        uw: Nat.nat, ux: Map[Nat.nat, Option[A]],
                        x4: List[(String, (List[A], List[A]))],
                        train:
                          List[(List[A], (Map[Nat.nat, Option[A]], List[A]))]):
      List[(List[A], (Map[Nat.nat, Option[A]], List[A]))]
  =
  (uu, uv, uw, ux, x4, train) match {
  case (uu, uv, uw, ux, Nil, train) => train
  case (gp, e, s, r, (l, (i, p)) :: t, train) =>
    {
      val (id, (sa, transition)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[A,
                Unit]))](Inference.i_possible_steps[A](e, s, r, l, i));
      (if (Lista.list_ex[(List[Nat.nat],
                           Transition.transition_ext[A,
              Unit])](((a: (List[Nat.nat], Transition.transition_ext[A, Unit]))
                         =>
                        {
                          val (ida, _):
                                (List[Nat.nat],
                                  Transition.transition_ext[A, Unit])
                            = a;
                          Lista.equal_lista[Nat.nat](ida, id)
                        }),
                       gp))
        trace_group_training_set[A](gp, e, sa,
                                     (Transition.apply_updates[A](Transition.Updates[A,
      Unit](transition),
                           AExp.join_ir[A](i, r))).apply(r),
                                     t, (i, (r, p)) :: train)
        else trace_group_training_set[A](gp, e, sa,
  (Transition.apply_updates[A](Transition.Updates[A, Unit](transition),
                                AExp.join_ir[A](i, r))).apply(r),
  t, train))
    }
}

def make_training_set[A : HOL.equal : Orderings.order : Value.aexp_value](e:
                                    FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                   l: List[List[(String, (List[A], List[A]))]],
                                   gp: List[(List[Nat.nat],
      Transition.transition_ext[A, Unit])]):
      List[(List[A], (Map[Nat.nat, Option[A]], List[A]))]
  =
  Lista.fold[List[(String, (List[A], List[A]))],
              List[(List[A],
                     (Map[Nat.nat, Option[A]],
                       List[A]))]](((a: List[(String, (List[A], List[A]))]) =>
                                     (b:
List[(List[A], (Map[Nat.nat, Option[A]], List[A]))])
                                       =>
                                     trace_group_training_set[A](gp, e,
                          Nat.zero_nata, AExp.null_state[Nat.nat, Option[A]], a,
                          b)),
                                    l, Nil)

def insert_updates[A : HOL.equal](t: Transition.transition_ext[A, Unit],
                                   u: List[(Nat.nat,
     AExp.aexp[VName.vname, A])]):
      Transition.transition_ext[A, Unit]
  =
  {
    val necessary_updates: List[(Nat.nat, AExp.aexp[VName.vname, A])] =
      Lista.filter[(Nat.nat,
                     AExp.aexp[VName.vname,
                                A])](((a: (Nat.nat, AExp.aexp[VName.vname, A]))
=>
                                       {
 val (r, ua): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
 ! (AExp.equal_aexpa[VName.vname, A](ua, AExp.V[VName.vname, A](VName.R(r))))
                                       }),
                                      u);
    Transition.Updates_update[A, Unit](((_:
   List[(Nat.nat, AExp.aexp[VName.vname, A])])
  =>
 Lista.filter[(Nat.nat,
                AExp.aexp[VName.vname,
                           A])](((a: (Nat.nat, AExp.aexp[VName.vname, A])) =>
                                  {
                                    val (r, _):
  (Nat.nat, AExp.aexp[VName.vname, A])
                                      = a;
                                    ! ((Lista.map[(Nat.nat,
            AExp.aexp[VName.vname, A]),
           Nat.nat](((aa: (Nat.nat, AExp.aexp[VName.vname, A])) => aa._1),
                     u)).contains(r))
                                  }),
                                 Transition.Updates[A, Unit](t)) ++
   necessary_updates),
t)
  }

def add_groupwise_updates_trace[A : HOL.equal : Value.aexp_value](x0:
                            List[(String, (List[A], List[A]))],
                           uu: List[(List[Nat.nat],
                                      List[(Nat.nat,
     AExp.aexp[VName.vname, A])])],
                           e: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                           uv: Nat.nat, uw: Map[Nat.nat, Option[A]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (x0, uu, e, uv, uw) match {
  case (Nil, uu, e, uv, uw) => e
  case ((l, (i, ux)) :: trace, funs, e, s, r) =>
    {
      val (id, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[A,
                Unit]))](Inference.i_possible_steps[A](e, s, r, l, i))
      val updated: Map[Nat.nat, Option[A]] =
        (Transition.apply_updates[A](Transition.Updates[A, Unit](t),
                                      AExp.join_ir[A](i, r))).apply(r)
      val newUpdates: List[(Nat.nat, AExp.aexp[VName.vname, A])] =
        Lista.maps[(List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname, A])]),
                    (Nat.nat,
                      AExp.aexp[VName.vname,
                                 A])](((a:
  (List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname, A])]))
 =>
a._2),
                                       Lista.filter[(List[Nat.nat],
              List[(Nat.nat,
                     AExp.aexp[VName.vname,
                                A])])](((a:
   (List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname, A])]))
  =>
 {
   val (tids, _): (List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname, A])]) =
     a;
   Cardinality.subset[Nat.nat](Set.seta[Nat.nat](id), Set.seta[Nat.nat](tids))
 }),
funs))
      val ta: Transition.transition_ext[A, Unit] =
        insert_updates[A](t, newUpdates)
      val updateda: Map[Nat.nat, Option[A]] =
        (Transition.apply_updates[A](Transition.Updates[A, Unit](ta),
                                      AExp.join_ir[A](i, r))).apply(r)
      val necessaryUpdates: List[(Nat.nat, AExp.aexp[VName.vname, A])] =
        Lista.filter[(Nat.nat,
                       AExp.aexp[VName.vname,
                                  A])](((a:
   (Nat.nat, AExp.aexp[VName.vname, A]))
  =>
 {
   val (ra, _): (Nat.nat, AExp.aexp[VName.vname, A]) = a;
   ! (Optiona.equal_optiona[A](updated(ra), updateda(ra)))
 }),
newUpdates)
      val tb: Transition.transition_ext[A, Unit] =
        insert_updates[A](t, necessaryUpdates)
      val ea: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]
        = Inference.replace_transition[A](e, id, tb);
      add_groupwise_updates_trace[A](trace, funs, ea, sa, updateda)
    }
}

def add_groupwise_updates[A : HOL.equal : Orderings.order : Value.aexp_value](log:
List[List[(String, (List[A], List[A]))]],
                                       funs:
 List[(List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname, A])])],
                                       e:
 FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  Lista.fold[List[(String, (List[A], List[A]))],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit]))]](((trace: List[(String, (List[A], List[A]))]) =>
                           (acc: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
                             =>
                           add_groupwise_updates_trace[A](trace, funs, acc,
                   Nat.zero_nata, AExp.null_state[Nat.nat, Option[A]])),
                          log, e)

def get_updates_opt[A : HOL.equal : Value.aexp_value](l: String,
               values: List[A],
               train:
                 List[(List[A],
                        (Map[Nat.nat, Option[A]], Map[Nat.nat, Option[A]]))]):
      List[(Nat.nat, Option[AExp.aexp[VName.vname, A]])]
  =
  {
    val a: List[Nat.nat] =
      Lista.fold[(List[A], (Map[Nat.nat, Option[A]], Map[Nat.nat, Option[A]])),
                  List[Nat.nat]](Fun.comp[List[Nat.nat],
   (List[Nat.nat]) => List[Nat.nat],
   (List[A],
     (Map[Nat.nat, Option[A]],
       Map[Nat.nat, Option[A]]))](Lista.union[Nat.nat],
                                   Fun.comp[(Map[Nat.nat, Option[A]],
      Map[Nat.nat, Option[A]]),
     List[Nat.nat],
     (List[A],
       (Map[Nat.nat, Option[A]],
         Map[Nat.nat, Option[A]]))](Fun.comp[Map[Nat.nat, Option[A]],
      List[Nat.nat],
      (Map[Nat.nat, Option[A]],
        Map[Nat.nat, Option[A]])](((a: Map[Nat.nat, Option[A]]) =>
                                    a.keySet.toList),
                                   ((a: (Map[Nat.nat, Option[A]],
  Map[Nat.nat, Option[A]]))
                                      =>
                                     a._2)),
                                     ((a:
 (List[A], (Map[Nat.nat, Option[A]], Map[Nat.nat, Option[A]])))
=>
                                       a._2))),
                                  train, Nil);
    Lista.map[Nat.nat,
               (Nat.nat,
                 Option[AExp.aexp[VName.vname,
                                   A]])](((r: Nat.nat) =>
   {
     val targetValues: List[Option[A]] =
       (Lista.map[(List[A], (Map[Nat.nat, Option[A]], Map[Nat.nat, Option[A]])),
                   Option[A]](((aa: (List[A],
                                      (Map[Nat.nat, Option[A]],
Map[Nat.nat, Option[A]])))
                                 =>
                                {
                                  val (_, (_, regs)):
(List[A], (Map[Nat.nat, Option[A]], Map[Nat.nat, Option[A]]))
                                    = aa;
                                  regs(r)
                                }),
                               train)).par.distinct.toList;
     (if (Lista.list_all[(List[A],
                           (Map[Nat.nat, Option[A]],
                             Map[Nat.nat, Option[A]]))](((aa:
                    (List[A],
                      (Map[Nat.nat, Option[A]], Map[Nat.nat, Option[A]])))
                   =>
                  {
                    val (_, (anteriorRegs, posteriorRegs)):
                          (List[A],
                            (Map[Nat.nat, Option[A]], Map[Nat.nat, Option[A]]))
                      = aa;
                    Optiona.equal_optiona[A](anteriorRegs(r), posteriorRegs(r))
                  }),
                 train))
       (r, Some[AExp.aexp[VName.vname, A]](AExp.V[VName.vname, A](VName.R(r))))
       else (if ((Nat.equal_nata(Nat.Nata(targetValues.par.length),
                                  Nat.Nata((1)))) && (Lista.list_all[(List[A],
                               (Map[Nat.nat, Option[A]],
                                 Map[Nat.nat, Option[A]]))](((aa:
                        (List[A],
                          (Map[Nat.nat, Option[A]], Map[Nat.nat, Option[A]])))
                       =>
                      {
                        val (_, (anteriorRegs, _)):
                              (List[A],
                                (Map[Nat.nat, Option[A]],
                                  Map[Nat.nat, Option[A]]))
                          = aa;
                        (anteriorRegs.keySet.toList).isEmpty
                      }),
                     train)))
              {
                val (Some(v)): Option[A] = targetValues.head;
                (r, Some[AExp.aexp[VName.vname, A]](AExp.L[A, VName.vname](v)))
              }
              else (r, Dirties.getUpdate[A](l, r, values, train))))
   }),
  a)
  }

def finfun_add[A : HOL.equal : Orderings.linorder,
                B : HOL.equal](a: Map[A, B], b: Map[A, B]):
      Map[A, B]
  =
  Lista.fold[A, Map[A, B]](((k: A) => (f: Map[A, B]) => f + (k -> (b(k)))),
                            b.keySet.toList, a)

def group_update[A : HOL.equal : Value.aexp_value](values: List[A],
            l: List[(Map[Nat.nat, Option[A]],
                      (Nat.nat,
                        (Map[Nat.nat, Option[A]],
                          (Map[Nat.nat, Option[A]],
                            (List[A],
                              (List[Nat.nat],
                                Transition.transition_ext[A, Unit]))))))]):
      Option[(List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname, A])])]
  =
  {
    val (_, (_, (_, (_, (_, (_, t)))))):
          (Map[Nat.nat, Option[A]],
            (Nat.nat,
              (Map[Nat.nat, Option[A]],
                (Map[Nat.nat, Option[A]],
                  (List[A],
                    (List[Nat.nat], Transition.transition_ext[A, Unit]))))))
      = l.head
    val targeted:
          List[(Map[Nat.nat, Option[A]],
                 (Nat.nat,
                   (Map[Nat.nat, Option[A]],
                     (Map[Nat.nat, Option[A]],
                       (List[A],
                         (List[Nat.nat],
                           Transition.transition_ext[A, Unit]))))))]
      = Lista.filter[(Map[Nat.nat, Option[A]],
                       (Nat.nat,
                         (Map[Nat.nat, Option[A]],
                           (Map[Nat.nat, Option[A]],
                             (List[A],
                               (List[Nat.nat],
                                 Transition.transition_ext[A,
                    Unit]))))))](((a: (Map[Nat.nat, Option[A]],
(Nat.nat,
  (Map[Nat.nat, Option[A]],
    (Map[Nat.nat, Option[A]],
      (List[A], (List[Nat.nat], Transition.transition_ext[A, Unit])))))))
                                    =>
                                   {
                                     val (regs, _):
   (Map[Nat.nat, Option[A]],
     (Nat.nat,
       (Map[Nat.nat, Option[A]],
         (Map[Nat.nat, Option[A]],
           (List[A], (List[Nat.nat], Transition.transition_ext[A, Unit]))))))
                                       = a;
                                     ! ((regs.keySet.toList).isEmpty)
                                   }),
                                  l)
    val maybe_updates: List[(Nat.nat, Option[AExp.aexp[VName.vname, A]])] =
      get_updates_opt[A](Transition.Label[A, Unit](t), values,
                          Lista.map[(Map[Nat.nat, Option[A]],
                                      (Nat.nat,
(Map[Nat.nat, Option[A]],
  (Map[Nat.nat, Option[A]],
    (List[A], (List[Nat.nat], Transition.transition_ext[A, Unit])))))),
                                     (List[A],
                                       (Map[Nat.nat, Option[A]],
 Map[Nat.nat, Option[A]]))](((a: (Map[Nat.nat, Option[A]],
                                   (Nat.nat,
                                     (Map[Nat.nat, Option[A]],
                                       (Map[Nat.nat, Option[A]],
 (List[A], (List[Nat.nat], Transition.transition_ext[A, Unit])))))))
                               =>
                              {
                                val (tRegs,
                                      (_, (oldRegs, (regs, (inputs, (_, _)))))):
                                      (Map[Nat.nat, Option[A]],
(Nat.nat,
  (Map[Nat.nat, Option[A]],
    (Map[Nat.nat, Option[A]],
      (List[A], (List[Nat.nat], Transition.transition_ext[A, Unit]))))))
                                  = a;
                                (inputs,
                                  (finfun_add[Nat.nat,
       Option[A]](oldRegs, regs),
                                    tRegs))
                              }),
                             targeted));
    (if (Lista.list_ex[(Nat.nat,
                         Option[AExp.aexp[VName.vname,
   A]])](((a: (Nat.nat, Option[AExp.aexp[VName.vname, A]])) =>
           {
             val (_, aa): (Nat.nat, Option[AExp.aexp[VName.vname, A]]) = a;
             Optiona.is_none[AExp.aexp[VName.vname, A]](aa)
           }),
          maybe_updates))
      None
      else Some[(List[Nat.nat],
                  List[(Nat.nat,
                         AExp.aexp[VName.vname,
                                    A])])]((Lista.fold[(Map[Nat.nat, Option[A]],
                 (Nat.nat,
                   (Map[Nat.nat, Option[A]],
                     (Map[Nat.nat, Option[A]],
                       (List[A],
                         (List[Nat.nat],
                           Transition.transition_ext[A, Unit])))))),
                List[Nat.nat]](Fun.comp[List[Nat.nat],
 (List[Nat.nat]) => List[Nat.nat],
 (Map[Nat.nat, Option[A]],
   (Nat.nat,
     (Map[Nat.nat, Option[A]],
       (Map[Nat.nat, Option[A]],
         (List[A],
           (List[Nat.nat],
             Transition.transition_ext[A,
Unit]))))))](Lista.union[Nat.nat],
              ((a: (Map[Nat.nat, Option[A]],
                     (Nat.nat,
                       (Map[Nat.nat, Option[A]],
                         (Map[Nat.nat, Option[A]],
                           (List[A],
                             (List[Nat.nat],
                               Transition.transition_ext[A, Unit])))))))
                 =>
                {
                  val (_, (_, (_, (_, (_, (tid, _)))))):
                        (Map[Nat.nat, Option[A]],
                          (Nat.nat,
                            (Map[Nat.nat, Option[A]],
                              (Map[Nat.nat, Option[A]],
                                (List[A],
                                  (List[Nat.nat],
                                    Transition.transition_ext[A, Unit]))))))
                    = a;
                  tid
                })),
                                l, Nil),
     Lista.map[(Nat.nat, Option[AExp.aexp[VName.vname, A]]),
                (Nat.nat,
                  AExp.aexp[VName.vname,
                             A])](((a: (Nat.nat,
 Option[AExp.aexp[VName.vname, A]]))
                                     =>
                                    {
                                      val
(r, f_o): (Nat.nat, Option[AExp.aexp[VName.vname, A]]) = a;
                                      (r,
Optiona.the[AExp.aexp[VName.vname, A]](f_o))
                                    }),
                                   maybe_updates))))
  }

def groupwise_put_updates[A : HOL.equal : Orderings.linorder : Value.aexp_value](x0:
   List[List[(List[Nat.nat], Transition.transition_ext[A, Unit])]],
  uu: List[List[(String, (List[A], List[A]))]], uv: List[A],
  uw: List[List[(Nat.nat,
                  (Map[Nat.nat, Option[A]],
                    (Map[Nat.nat, Option[A]],
                      (List[A],
                        (List[Nat.nat],
                          Transition.transition_ext[A, Unit])))))]],
  ux: (Nat.nat, (AExp.aexp[VName.vname, A], Map[VName.vname, String])),
  e: FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (x0, uu, uv, uw, ux, e) match {
  case (Nil, uu, uv, uw, ux, e) => e
  case (gp :: gps, log, values, walked, (o_inx, (op, types)), e) =>
    {
      val targeted:
            List[List[(Map[Nat.nat, Option[A]],
                        (Nat.nat,
                          (Map[Nat.nat, Option[A]],
                            (Map[Nat.nat, Option[A]],
                              (List[A],
                                (List[Nat.nat],
                                  Transition.transition_ext[A, Unit]))))))]]
        = Lista.map[List[(Map[Nat.nat, Option[A]],
                           (Nat.nat,
                             (Map[Nat.nat, Option[A]],
                               (Map[Nat.nat, Option[A]],
                                 (List[A],
                                   (List[Nat.nat],
                                     Transition.transition_ext[A, Unit]))))))],
                     List[(Map[Nat.nat, Option[A]],
                            (Nat.nat,
                              (Map[Nat.nat, Option[A]],
                                (Map[Nat.nat, Option[A]],
                                  (List[A],
                                    (List[Nat.nat],
                                      Transition.transition_ext[A,
                         Unit]))))))]](((a:
   List[(Map[Nat.nat, Option[A]],
          (Nat.nat,
            (Map[Nat.nat, Option[A]],
              (Map[Nat.nat, Option[A]],
                (List[A],
                  (List[Nat.nat], Transition.transition_ext[A, Unit]))))))])
  =>
 Lista.filter[(Map[Nat.nat, Option[A]],
                (Nat.nat,
                  (Map[Nat.nat, Option[A]],
                    (Map[Nat.nat, Option[A]],
                      (List[A],
                        (List[Nat.nat],
                          Transition.transition_ext[A,
             Unit]))))))](((aa: (Map[Nat.nat, Option[A]],
                                  (Nat.nat,
                                    (Map[Nat.nat, Option[A]],
                                      (Map[Nat.nat, Option[A]],
(List[A], (List[Nat.nat], Transition.transition_ext[A, Unit])))))))
                             =>
                            {
                              val (_, (_, (_, (_, (_, (id, tran)))))):
                                    (Map[Nat.nat, Option[A]],
                                      (Nat.nat,
(Map[Nat.nat, Option[A]],
  (Map[Nat.nat, Option[A]],
    (List[A], (List[Nat.nat], Transition.transition_ext[A, Unit]))))))
                                = aa;
                              gp.contains((id, tran))
                            }),
                           a)),
Lista.map[List[(Nat.nat,
                 (Map[Nat.nat, Option[A]],
                   (Map[Nat.nat, Option[A]],
                     (List[A],
                       (List[Nat.nat], Transition.transition_ext[A, Unit])))))],
           List[(Map[Nat.nat, Option[A]],
                  (Nat.nat,
                    (Map[Nat.nat, Option[A]],
                      (Map[Nat.nat, Option[A]],
                        (List[A],
                          (List[Nat.nat],
                            Transition.transition_ext[A,
               Unit]))))))]](((w: List[(Nat.nat,
 (Map[Nat.nat, Option[A]],
   (Map[Nat.nat, Option[A]],
     (List[A], (List[Nat.nat], Transition.transition_ext[A, Unit])))))])
                                =>
                               (target[A](AExp.null_state[Nat.nat, Option[A]],
   w.par.reverse.toList)).par.reverse.toList),
                              walked))
      val group:
            List[(Map[Nat.nat, Option[A]],
                   (Nat.nat,
                     (Map[Nat.nat, Option[A]],
                       (Map[Nat.nat, Option[A]],
                         (List[A],
                           (List[Nat.nat],
                             Transition.transition_ext[A, Unit]))))))]
        = Lista.fold[List[(Map[Nat.nat, Option[A]],
                            (Nat.nat,
                              (Map[Nat.nat, Option[A]],
                                (Map[Nat.nat, Option[A]],
                                  (List[A],
                                    (List[Nat.nat],
                                      Transition.transition_ext[A, Unit]))))))],
                      List[(Map[Nat.nat, Option[A]],
                             (Nat.nat,
                               (Map[Nat.nat, Option[A]],
                                 (Map[Nat.nat, Option[A]],
                                   (List[A],
                                     (List[Nat.nat],
                                       Transition.transition_ext[A,
                          Unit]))))))]](Lista.union[(Map[Nat.nat, Option[A]],
              (Nat.nat,
                (Map[Nat.nat, Option[A]],
                  (Map[Nat.nat, Option[A]],
                    (List[A],
                      (List[Nat.nat], Transition.transition_ext[A, Unit]))))))],
 targeted, Nil);
      (group_update[A](values, group) match {
         case None =>
           groupwise_put_updates[A](gps, log, values, walked,
                                     (o_inx, (op, types)), e)
         case Some(u) =>
           groupwise_put_updates[A](gps, log, values, walked,
                                     (o_inx, (op, types)),
                                     Inference.make_distinct[A](add_groupwise_updates[A](log,
          List(u), e)))
       })
    }
}

def everything_walk[A : HOL.equal : Orderings.order : Value.aexp_value](uu:
                                  AExp.aexp[VName.vname, A],
                                 uv: Nat.nat, uw: Map[VName.vname, String],
                                 x3: List[(String, (List[A], List[A]))],
                                 ux: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                 uy: Nat.nat, uz: Map[Nat.nat, Option[A]],
                                 va: List[(List[Nat.nat],
    Transition.transition_ext[A, Unit])]):
      List[(Nat.nat,
             (Map[Nat.nat, Option[A]],
               (Map[Nat.nat, Option[A]],
                 (List[A],
                   (List[Nat.nat], Transition.transition_ext[A, Unit])))))]
  =
  (uu, uv, uw, x3, ux, uy, uz, va) match {
  case (uu, uv, uw, Nil, ux, uy, uz, va) => Nil
  case (f, fi, types, (label, (inputs, outputs)) :: t, oPTA, s, regs, gp) =>
    {
      val (tid, (sa, ta)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[A,
                Unit]))](Inference.i_possible_steps[A](oPTA, s, regs, label,
                inputs));
      (if (Lista.list_ex[(List[Nat.nat],
                           Transition.transition_ext[A,
              Unit])](((a: (List[Nat.nat], Transition.transition_ext[A, Unit]))
                         =>
                        {
                          val (tida, _):
                                (List[Nat.nat],
                                  Transition.transition_ext[A, Unit])
                            = a;
                          Lista.equal_lista[Nat.nat](tid, tida)
                        }),
                       gp))
        (s, (regs,
              (Dirties.getRegs[A](types, inputs, f,
                                   outputs(Code_Numeral.integer_of_nat(fi).toInt)),
                (inputs, (tid, ta))))) ::
          everything_walk[A](f, fi, types, t, oPTA, sa,
                              (Transition.apply_updates[A](Transition.Updates[A,
                                       Unit](ta),
                    AExp.join_ir[A](inputs, regs))).apply(regs),
                              gp)
        else {
               val empty: Map[Nat.nat, Option[A]] =
                 AExp.null_state[Nat.nat, Option[A]];
               (s, (regs, (empty, (inputs, (tid, ta))))) ::
                 everything_walk[A](f, fi, types, t, oPTA, sa,
                                     (Transition.apply_updates[A](Transition.Updates[A,
      Unit](ta),
                           AExp.join_ir[A](inputs, regs))).apply(regs),
                                     gp)
             })
    }
}

def everything_walk_log[A : HOL.equal : Orderings.order : Value.aexp_value](f:
                                      AExp.aexp[VName.vname, A],
                                     fi: Nat.nat,
                                     types: Map[VName.vname, String],
                                     log: List[List[(String,
              (List[A], List[A]))]],
                                     e: FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                     gp: List[(List[Nat.nat],
        Transition.transition_ext[A, Unit])]):
      List[List[(Nat.nat,
                  (Map[Nat.nat, Option[A]],
                    (Map[Nat.nat, Option[A]],
                      (List[A],
                        (List[Nat.nat],
                          Transition.transition_ext[A, Unit])))))]]
  =
  Lista.map[List[(String, (List[A], List[A]))],
             List[(Nat.nat,
                    (Map[Nat.nat, Option[A]],
                      (Map[Nat.nat, Option[A]],
                        (List[A],
                          (List[Nat.nat],
                            Transition.transition_ext[A,
               Unit])))))]](((t: List[(String, (List[A], List[A]))]) =>
                              everything_walk[A](f, fi, types, t, e,
          Nat.zero_nata, AExp.null_state[Nat.nat, Option[A]], gp)),
                             log)

def same_structure[A : Value.aexp_value](t1: Transition.transition_ext[A, Unit],
  t2: Transition.transition_ext[A, Unit]):
      Boolean
  =
  (Transition.Label[A, Unit](t1) ==
    Transition.Label[A, Unit](t2)) && ((Nat.equal_nata(Transition.Arity[A,
                                 Unit](t1),
                Transition.Arity[A, Unit](t2))) && (Lista.equal_lista[value_type](Lista.map[AExp.aexp[VName.vname,
                       A],
             value_type](((a: AExp.aexp[VName.vname, A]) => typeSig[A](a)),
                          Transition.Outputs[A, Unit](t1)),
   Lista.map[AExp.aexp[VName.vname, A],
              value_type](((a: AExp.aexp[VName.vname, A]) => typeSig[A](a)),
                           Transition.Outputs[A, Unit](t2)))))

def observe_all[A : HOL.equal : Value.aexp_value](uu:
            FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))],
           uv: Nat.nat, uw: Map[Nat.nat, Option[A]],
           x3: List[(String, (List[A], List[A]))]):
      List[(List[Nat.nat], Transition.transition_ext[A, Unit])]
  =
  (uu, uv, uw, x3) match {
  case (uu, uv, uw, Nil) => Nil
  case (e, s, r, (l, (i, ux)) :: es) =>
    (Dirties.randomMember[(List[Nat.nat],
                            (Nat.nat,
                              Transition.transition_ext[A,
                 Unit]))](Inference.i_possible_steps[A](e, s, r, l, i))
       match {
       case None => Nil
       case Some((ids, (sa, t))) =>
         (ids, t) ::
           observe_all[A](e, sa,
                           (Transition.apply_updates[A](Transition.Updates[A,
                                    Unit](t),
                 AExp.join_ir[A](i, r))).apply(r),
                           es)
     })
}

def transition_group_exec[A : HOL.equal : Orderings.order : Value.aexp_value](e:
FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                       t: List[(String, (List[A], List[A]))]):
      List[List[(Nat.nat, (List[Nat.nat], Transition.transition_ext[A, Unit]))]]
  =
  Group_By.group_by[(Nat.nat,
                      (List[Nat.nat],
                        Transition.transition_ext[A,
           Unit]))](((a: (Nat.nat,
                           (List[Nat.nat], Transition.transition_ext[A, Unit])))
                       =>
                      {
                        val (_, (_, t1)):
                              (Nat.nat,
                                (List[Nat.nat],
                                  Transition.transition_ext[A, Unit]))
                          = a;
                        ((aa: (Nat.nat,
                                (List[Nat.nat],
                                  Transition.transition_ext[A, Unit])))
                           =>
                          {
                            val (_, ab):
                                  (Nat.nat,
                                    (List[Nat.nat],
                                      Transition.transition_ext[A, Unit]))
                              = aa
                            val (_, ac):
                                  (List[Nat.nat],
                                    Transition.transition_ext[A, Unit])
                              = ab;
                            same_structure[A](t1, ac)
                          })
                      }),
                     Lista.enumerate[(List[Nat.nat],
                                       Transition.transition_ext[A,
                          Unit])](Nat.zero_nata,
                                   observe_all[A](e, Nat.zero_nata,
           AExp.null_state[Nat.nat, Option[A]], t)))

def transition_group[A : HOL.equal : Orderings.linorder : Value.aexp_value](e:
                                      FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                     l: List[List[(String,
            (List[A], List[A]))]]):
      List[List[(List[Nat.nat], Transition.transition_ext[A, Unit])]]
  =
  {
    val trace_groups:
          List[List[List[(Nat.nat,
                           (List[Nat.nat],
                             Transition.transition_ext[A, Unit]))]]]
      = Lista.map[List[(String, (List[A], List[A]))],
                   List[List[(Nat.nat,
                               (List[Nat.nat],
                                 Transition.transition_ext[A,
                    Unit]))]]](((a: List[(String, (List[A], List[A]))]) =>
                                 transition_group_exec[A](e, a)),
                                l)
    val tagged:
          List[List[(Option[(String, (Nat.nat, List[value_type]))],
                      ((String, (Nat.nat, List[value_type])),
                        List[(Nat.nat,
                               (List[Nat.nat],
                                 Transition.transition_ext[A, Unit]))]))]]
      = Lista.map[List[List[(Nat.nat,
                              (List[Nat.nat],
                                Transition.transition_ext[A, Unit]))]],
                   List[(Option[(String, (Nat.nat, List[value_type]))],
                          ((String, (Nat.nat, List[value_type])),
                            List[(Nat.nat,
                                   (List[Nat.nat],
                                     Transition.transition_ext[A,
                        Unit]))]))]](((a:
 List[List[(Nat.nat, (List[Nat.nat], Transition.transition_ext[A, Unit]))]])
=>
                                       tag[A](None, a)),
                                      trace_groups)
    val flat: List[(Option[(String, (Nat.nat, List[value_type]))],
                     ((String, (Nat.nat, List[value_type])),
                       List[(Nat.nat,
                              (List[Nat.nat],
                                Transition.transition_ext[A, Unit]))]))]
      = Lista.sort_key[(Option[(String, (Nat.nat, List[value_type]))],
                         ((String, (Nat.nat, List[value_type])),
                           List[(Nat.nat,
                                  (List[Nat.nat],
                                    Transition.transition_ext[A, Unit]))])),
                        (Option[(String, (Nat.nat, List[value_type]))],
                          ((String, (Nat.nat, List[value_type])),
                            List[(Nat.nat,
                                   (List[Nat.nat],
                                     Transition.transition_ext[A,
                        Unit]))]))](((x:
(Option[(String, (Nat.nat, List[value_type]))],
  ((String, (Nat.nat, List[value_type])),
    List[(Nat.nat, (List[Nat.nat], Transition.transition_ext[A, Unit]))])))
                                       =>
                                      x),
                                     Lista.fold[List[(Option[(String,
                       (Nat.nat, List[value_type]))],
               ((String, (Nat.nat, List[value_type])),
                 List[(Nat.nat,
                        (List[Nat.nat],
                          Transition.transition_ext[A, Unit]))]))],
         List[(Option[(String, (Nat.nat, List[value_type]))],
                ((String, (Nat.nat, List[value_type])),
                  List[(Nat.nat,
                         (List[Nat.nat],
                           Transition.transition_ext[A,
              Unit]))]))]](((a: List[(Option[(String,
       (Nat.nat, List[value_type]))],
                                       ((String, (Nat.nat, List[value_type])),
 List[(Nat.nat, (List[Nat.nat], Transition.transition_ext[A, Unit]))]))])
                              =>
                             (b: List[(Option[(String,
        (Nat.nat, List[value_type]))],
((String, (Nat.nat, List[value_type])),
  List[(Nat.nat, (List[Nat.nat], Transition.transition_ext[A, Unit]))]))])
                               =>
                             a ++ b),
                            tagged, Nil))
    val group_fun:
          Map[((Option[(String, (Nat.nat, List[value_type]))],
                (String,
                  (Nat.nat,
                    List[value_type])))), (List[(Nat.nat,
          (List[Nat.nat], Transition.transition_ext[A, Unit]))])]
      = Lista.fold[(Option[(String, (Nat.nat, List[value_type]))],
                     ((String, (Nat.nat, List[value_type])),
                       List[(Nat.nat,
                              (List[Nat.nat],
                                Transition.transition_ext[A, Unit]))])),
                    Map[((Option[(String, (Nat.nat, List[value_type]))],
                          (String,
                            (Nat.nat,
                              List[value_type])))), (List[(Nat.nat,
                    (List[Nat.nat],
                      Transition.transition_ext[A,
         Unit]))])]](((a: (Option[(String, (Nat.nat, List[value_type]))],
                            ((String, (Nat.nat, List[value_type])),
                              List[(Nat.nat,
                                     (List[Nat.nat],
                                       Transition.transition_ext[A, Unit]))])))
                        =>
                       {
                         val (taga, (s, gp)):
                               (Option[(String, (Nat.nat, List[value_type]))],
                                 ((String, (Nat.nat, List[value_type])),
                                   List[(Nat.nat,
  (List[Nat.nat], Transition.transition_ext[A, Unit]))]))
                           = a;
                         ((f: Map[((Option[(String,
     (Nat.nat, List[value_type]))],
                                    (String,
                                      (Nat.nat,
List[value_type])))), (List[(Nat.nat,
                              (List[Nat.nat],
                                Transition.transition_ext[A, Unit]))])])
                            =>
                           f + ((taga, s) -> (gp ++ f((taga, s)))))
                       }),
                      flat,
                      scala.collection.immutable.Map().withDefaultValue(Nil))
    val grouped:
          List[List[(Nat.nat,
                      (List[Nat.nat], Transition.transition_ext[A, Unit]))]]
      = Lista.map[(Option[(String, (Nat.nat, List[value_type]))],
                    (String, (Nat.nat, List[value_type]))),
                   List[(Nat.nat,
                          (List[Nat.nat],
                            Transition.transition_ext[A,
               Unit]))]](((a: (Option[(String, (Nat.nat, List[value_type]))],
                                (String, (Nat.nat, List[value_type]))))
                            =>
                           group_fun(a)),
                          group_fun.keySet.toList)
    val inx_groups:
          List[(Nat.nat,
                 List[(List[Nat.nat], Transition.transition_ext[A, Unit])])]
      = Lista.map[List[(Nat.nat,
                         (List[Nat.nat], Transition.transition_ext[A, Unit]))],
                   (Nat.nat,
                     List[(List[Nat.nat],
                            Transition.transition_ext[A,
               Unit])])](((gp: List[(Nat.nat,
                                      (List[Nat.nat],
Transition.transition_ext[A, Unit]))])
                            =>
                           (Lattices_Big.Min[Nat.nat](Set.seta[Nat.nat](Lista.map[(Nat.nat,
    (List[Nat.nat], Transition.transition_ext[A, Unit])),
   Nat.nat](((a: (Nat.nat, (List[Nat.nat], Transition.transition_ext[A, Unit])))
               =>
              a._1),
             gp))),
                             Lista.map[(Nat.nat,
 (List[Nat.nat], Transition.transition_ext[A, Unit])),
(List[Nat.nat],
  Transition.transition_ext[A, Unit])](((a:
   (Nat.nat, (List[Nat.nat], Transition.transition_ext[A, Unit])))
  =>
 a._2),
gp))),
                          grouped);
    Lista.map[(Nat.nat,
                List[(List[Nat.nat], Transition.transition_ext[A, Unit])]),
               List[(List[Nat.nat],
                      Transition.transition_ext[A,
         Unit])]](((a: (Nat.nat,
                         List[(List[Nat.nat],
                                Transition.transition_ext[A, Unit])]))
                     =>
                    a._2),
                   Lista.sort_key[(Nat.nat,
                                    List[(List[Nat.nat],
   Transition.transition_ext[A, Unit])]),
                                   (Nat.nat,
                                     List[(List[Nat.nat],
    Transition.transition_ext[A, Unit])])](((x:
       (Nat.nat, List[(List[Nat.nat], Transition.transition_ext[A, Unit])]))
      =>
     x),
    inx_groups))
  }

def updates_for_output[A : HOL.equal : Orderings.linorder : Value.aexp_value](log:
List[List[(String, (List[A], List[A]))]],
                                       values: List[A],
                                       current:
 List[(List[Nat.nat], Transition.transition_ext[A, Unit])],
                                       o_inx: Nat.nat,
                                       op: AExp.aexp[VName.vname, A],
                                       types: Map[VName.vname, String],
                                       e:
 FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (if (Cardinality.eq_set[Nat.nat](AExp.enumerate_regs[A](op),
                                    Set.bot_set[Nat.nat]))
    e else {
             val walked:
                   List[List[(Nat.nat,
                               (Map[Nat.nat, Option[A]],
                                 (Map[Nat.nat, Option[A]],
                                   (List[A],
                                     (List[Nat.nat],
                                       Transition.transition_ext[A, Unit])))))]]
               = everything_walk_log[A](op, o_inx, types, log, e, current)
             val groups:
                   List[List[(List[Nat.nat],
                               Transition.transition_ext[A, Unit])]]
               = transition_group[A](e, log);
             groupwise_put_updates[A](groups, log, values, walked,
                                       (o_inx, (op, types)), e)
           })

def put_updates[A : HOL.equal : Orderings.linorder : Value.aexp_value](uu:
                                 List[List[(String, (List[A], List[A]))]],
                                uv: List[A],
                                uw: List[(List[Nat.nat],
   Transition.transition_ext[A, Unit])],
                                x3: List[(Nat.nat,
   Option[(AExp.aexp[VName.vname, A], Map[VName.vname, String])])],
                                e: FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (uu, uv, uw, x3, e) match {
  case (uu, uv, uw, Nil, e) => e
  case (log, values, gp, (ux, None) :: ops, e) =>
    put_updates[A](log, values, gp, ops, e)
  case (log, values, gp, (o_inx, Some((op, types))) :: ops, e) =>
    {
      val gpa: List[(List[Nat.nat], Transition.transition_ext[A, Unit])] =
        Lista.map[(List[Nat.nat], Transition.transition_ext[A, Unit]),
                   (List[Nat.nat],
                     Transition.transition_ext[A,
        Unit])](((a: (List[Nat.nat], Transition.transition_ext[A, Unit])) =>
                  {
                    val (id, t):
                          (List[Nat.nat], Transition.transition_ext[A, Unit])
                      = a;
                    (id, Transition.Outputs_update[A,
            Unit](((_: List[AExp.aexp[VName.vname, A]]) =>
                    Lista.list_update[AExp.aexp[VName.vname,
         A]](Transition.Outputs[A, Unit](t), o_inx, op)),
                   t))
                  }),
                 gp)
      val generalised_model:
            FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))]
        = Lista.fold[(List[Nat.nat], Transition.transition_ext[A, Unit]),
                      FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A,
                       Unit]))]](((a: (List[Nat.nat],
Transition.transition_ext[A, Unit]))
                                    =>
                                   {
                                     val (id, t):
   (List[Nat.nat], Transition.transition_ext[A, Unit])
                                       = a;
                                     ((acc:
 FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
=>
                                       Inference.replace_transition[A](acc, id,
                                t))
                                   }),
                                  gpa, e)
      val ea: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]
        = updates_for_output[A](log, values, gp, o_inx, op, types,
                                 generalised_model);
      (if (EFSM.accepts_log[A](Set.seta[List[(String,
       (List[A], List[A]))]](log),
                                Inference.tm[A](ea)))
        put_updates[A](log, values, gpa, ops, ea)
        else put_updates[A](log, values, gp, ops, e))
    }
}

def get_outputs[A : Value.aexp_value](l: String, maxReg: Nat.nat,
                                       values: List[A], i: List[List[A]],
                                       r: List[Map[Nat.nat, Option[A]]],
                                       outputs: List[List[A]]):
      List[Option[(AExp.aexp[VName.vname, A], Map[VName.vname, String])]]
  =
  Lista.map_tailrec[(Nat.nat, List[A]),
                     Option[(AExp.aexp[VName.vname, A],
                              Map[VName.vname, String])]](((a:
                      (Nat.nat, List[A]))
                     =>
                    {
                      val (maxRega, ps): (Nat.nat, List[A]) = a;
                      Dirties.getOutput[A](l, maxRega, values,
    i.par.zip(r.par.zip(ps).toList).toList)
                    }),
                   Lista.enumerate[List[A]](maxReg,
     Lista.transpose[A](outputs)))

def generalise_and_update[A : HOL.equal : Orderings.linorder : Value.aexp_value](log:
   List[List[(String, (List[A], List[A]))]],
  e: FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
  gp: List[(List[Nat.nat], Transition.transition_ext[A, Unit])]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  {
    val label: String = Transition.Label[A, Unit]((gp.head)._2)
    val values: List[A] = enumerate_log_values[A](log)
    val new_gp_ts: List[(List[A], (Map[Nat.nat, Option[A]], List[A]))] =
      make_training_set[A](e, log, gp)
    val (i, (r, p)):
          (List[List[A]], (List[Map[Nat.nat, Option[A]]], List[List[A]]))
      = unzip_3[List[A], Map[Nat.nat, Option[A]], List[A]](new_gp_ts)
    val max_reg: Nat.nat = Inference.max_reg_total[A](e)
    val outputs:
          List[Option[(AExp.aexp[VName.vname, A], Map[VName.vname, String])]]
      = get_outputs[A](label, max_reg, values, i, r, p);
    put_updates[A](log, values, gp,
                    Lista.enumerate[Option[(AExp.aexp[VName.vname, A],
     Map[VName.vname, String])]](Nat.zero_nata, outputs),
                    e)
  }

def find_first_use_of_trace[A : HOL.equal : Value.aexp_value](uu: Nat.nat,
                       x1: List[(String, (List[A], List[A]))],
                       uv: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[A, Unit]))],
                       uw: Nat.nat, ux: Map[Nat.nat, Option[A]]):
      Option[List[Nat.nat]]
  =
  (uu, x1, uv, uw, ux) match {
  case (uu, Nil, uv, uw, ux) => None
  case (rr, (l, (i, uy)) :: es, e, s, r) =>
    {
      val (id, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[A,
                Unit]))](Inference.i_possible_steps[A](e, s, r, l, i));
      (if (Lista.list_ex[AExp.aexp[VName.vname,
                                    A]](((p: AExp.aexp[VName.vname, A]) =>
  AExp.aexp_constrains[VName.vname, A](p, AExp.V[VName.vname, A](VName.R(rr)))),
 Transition.Outputs[A, Unit](t)))
        Some[List[Nat.nat]](id)
        else find_first_use_of_trace[A](rr, es, e, sa,
 (Transition.apply_updates[A](Transition.Updates[A, Unit](t),
                               AExp.join_ir[A](i, r))).apply(r)))
    }
}

def find_first_uses_of[A : HOL.equal : Orderings.order : Value.aexp_value](r:
                                     Nat.nat,
                                    l: List[List[(String, (List[A], List[A]))]],
                                    e: FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      List[List[Nat.nat]]
  =
  Lista.maps[Option[List[Nat.nat]],
              List[Nat.nat]](((a: Option[List[Nat.nat]]) =>
                               (a match {
                                  case None => Nil
                                  case Some(x) => List(x)
                                })),
                              Lista.map[List[(String, (List[A], List[A]))],
 Option[List[Nat.nat]]](((t: List[(String, (List[A], List[A]))]) =>
                          find_first_use_of_trace[A](r, t, e, Nat.zero_nata,
              AExp.null_state[Nat.nat, Option[A]])),
                         l))

def standardise_group[A : HOL.equal : Orderings.order : Value.aexp_value](e:
                                    FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                   l: List[List[(String, (List[A], List[A]))]],
                                   gp: List[(List[Nat.nat],
      Transition.transition_ext[A, Unit])],
                                   s: (FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
(List[List[(String, (List[A], List[A]))]]) =>
  (List[(List[Nat.nat], Transition.transition_ext[A, Unit])]) =>
    List[(List[Nat.nat], Transition.transition_ext[A, Unit])]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  {
    val standardised: List[(List[Nat.nat], Transition.transition_ext[A, Unit])]
      = ((s(e))(l))(gp)
    val ea: FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))]
      = Inference.replace_transitions[A](e, standardised);
    (if (FSet.equal_fseta[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit]))](ea, e))
      e else (if (EFSM.accepts_log[A](Set.seta[List[(String,
              (List[A], List[A]))]](l),
                                       Inference.tm[A](ea)))
               ea else e))
  }

def groupwise_generalise_and_update[A : HOL.equal : Orderings.linorder : Value.aexp_value](uu:
             List[List[(String, (List[A], List[A]))]],
            e: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))],
            x2: List[List[(List[Nat.nat],
                            Transition.transition_ext[A, Unit])]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  (uu, e, x2) match {
  case (uu, e, Nil) => e
  case (log, e, gp :: t) =>
    {
      val ea: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]
        = generalise_and_update[A](log, e, gp)
      val rep: Transition.transition_ext[A, Unit] = (gp.head)._2
      val structural_group:
            FSet.fset[(List[Nat.nat], Transition.transition_ext[A, Unit])]
        = FSet.fimage[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit])),
                       (List[Nat.nat],
                         Transition.transition_ext[A,
            Unit])](((a: (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit])))
                       =>
                      {
                        val (i, aa):
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit]))
                          = a
                        val (_, ab):
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit])
                          = aa;
                        (i, ab)
                      }),
                     FSet.ffilter[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A,
                         Unit]))](((a: (List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                                     =>
                                    {
                                      val
(_, aa):
  (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
= a
                                      val
(_, ab): ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]) = aa;
                                      same_structure[A](rep, ab)
                                    }),
                                   ea))
      val delayed:
            FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))]
        = Lista.fold[Nat.nat,
                      FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A,
                       Unit]))]](((r: Nat.nat) =>
                                   (acc: FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
                                     =>
                                   delay_initialisation_of[A](r, log, acc,
                       find_first_uses_of[A](r, log, acc))),
                                  Lista.sorted_list_of_set[Nat.nat](Inference.all_regs[A](ea)),
                                  ea)
      val standardised:
            FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit]))]
        = standardise_group[A](delayed, log,
                                FSet.sorted_list_of_fset[(List[Nat.nat],
                   Transition.transition_ext[A, Unit])](structural_group),
                                ((a: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
                                   =>
                                  (b: List[List[(String, (List[A], List[A]))]])
                                    =>
                                  (c: List[(List[Nat.nat],
     Transition.transition_ext[A, Unit])])
                                    =>
                                  standardise_group_outputs_updates[A](a, b,
                                c)))
      val structural_group2:
            FSet.fset[(List[AExp.aexp[VName.vname, A]],
                        List[(Nat.nat, AExp.aexp[VName.vname, A])])]
        = FSet.fimage[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[A, Unit])),
                       (List[AExp.aexp[VName.vname, A]],
                         List[(Nat.nat,
                                AExp.aexp[VName.vname,
   A])])](((a: (List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
             =>
            {
              val (_, (_, ta)):
                    (List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))
                = a;
              (Transition.Outputs[A, Unit](ta), Transition.Updates[A, Unit](ta))
            }),
           FSet.ffilter[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit]))](((a: (List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit])))
                           =>
                          {
                            val (_, (_, ta)):
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[A, Unit]))
                              = a;
                            (Transition.Label[A, Unit](rep) ==
                              Transition.Label[A,
        Unit](ta)) && ((Nat.equal_nata(Transition.Arity[A, Unit](rep),
Transition.Arity[A, Unit](ta))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[A,
 Unit](rep)).par.length),
            Nat.Nata((Transition.Outputs[A, Unit](ta)).par.length))))
                          }),
                         standardised));
      (if (FSet_Utils.fis_singleton[(List[AExp.aexp[VName.vname, A]],
                                      List[(Nat.nat,
     AExp.aexp[VName.vname, A])])](structural_group2))
        groupwise_generalise_and_update[A](log,
    Same_Register.merge_regs[A](standardised,
                                 ((a: FSet.fset[((Nat.nat, Nat.nat),
          Transition.transition_ext[A, Unit])])
                                    =>
                                   EFSM.accepts_log[A](Set.seta[List[(String,
                               (List[A], List[A]))]](log),
                a))),
    Lista.filter[List[(List[Nat.nat],
                        Transition.transition_ext[A,
           Unit])]](((g: List[(List[Nat.nat],
                                Transition.transition_ext[A, Unit])])
                       =>
                      Set.equal_set[(List[Nat.nat],
                                      Transition.transition_ext[A,
                         Unit])](Set.inf_set[(List[Nat.nat],
       Transition.transition_ext[A, Unit])](Set.seta[(List[Nat.nat],
               Transition.transition_ext[A, Unit])](g),
     FSet.fset[(List[Nat.nat],
                 Transition.transition_ext[A, Unit])](structural_group)),
                                  Set.bot_set[(List[Nat.nat],
        Transition.transition_ext[A, Unit])])),
                     t))
        else groupwise_generalise_and_update[A](log,
         Same_Register.merge_regs[A](standardised,
                                      ((a:
  FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])])
 =>
EFSM.accepts_log[A](Set.seta[List[(String, (List[A], List[A]))]](log), a))),
         t))
    }
}

def drop_all_guards[A : HOL.equal : Orderings.linorder : Value.aexp_value](e:
                                     FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                    pta: FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                    log: List[List[(String,
             (List[A], List[A]))]],
                                    m: (List[Nat.nat]) =>
 (List[Nat.nat]) =>
   Nat.nat =>
     (FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
       (FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat),
                      Transition.transition_ext[A, Unit]))]) =>
         (FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))]) =>
           ((FSet.fset[((Nat.nat, Nat.nat),
                         Transition.transition_ext[A, Unit])]) =>
             Boolean) =>
             Option[FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit]))]],
                                    np: (FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
  FSet.fset[(Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  {
    val derestricted:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
      = FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[A,
            Unit]))](((a: (List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[A, Unit])))
                        =>
                       {
                         val (id, (tf, tran)):
                               (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[A, Unit]))
                           = a;
                         (id, (tf, Transition.Guards_update[A,
                     Unit](((_: List[GExp.gexp[VName.vname, A]]) => Nil),
                            tran)))
                       }),
                      e)
    val nondeterministic_pairs:
          List[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                     (Transition.transition_ext[A, Unit], List[Nat.nat]))))]
      = FSet.sorted_list_of_fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     ((Transition.transition_ext[A, Unit],
List[Nat.nat]),
                                       (Transition.transition_ext[A, Unit],
 List[Nat.nat]))))](np(derestricted));
    (Inference.resolve_nondeterminism[A](Set.bot_set[(Nat.nat, Nat.nat)],
  nondeterministic_pairs, pta, derestricted, m,
  ((a: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]) =>
    EFSM.accepts_log[A](Set.seta[List[(String, (List[A], List[A]))]](log), a)),
  np)
       match {
       case (None, _) => pta
       case (Some(resolved), _) => resolved
     })
  }

def derestrict[A : HOL.equal : Orderings.linorder : Value.aexp_value](pta:
                                FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                               log: List[List[(String, (List[A], List[A]))]],
                               m: (List[Nat.nat]) =>
                                    (List[Nat.nat]) =>
                                      Nat.nat =>
(FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
  (FSet.fset[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
    (FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
      ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])]) =>
        Boolean) =>
        Option[FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))]],
                               np: (FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
                                     FSet.fset[(Nat.nat,
         ((Nat.nat, Nat.nat),
           ((Transition.transition_ext[A, Unit], List[Nat.nat]),
             (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  {
    val normalised:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
      = groupwise_generalise_and_update[A](log, pta,
    transition_group[A](pta, log));
    drop_all_guards[A](normalised, pta, log, m, np)
  }

def drop_pta_guards[A : HOL.equal : Orderings.linorder : Value.aexp_value](pta:
                                     FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                    log: List[List[(String,
             (List[A], List[A]))]],
                                    m: (List[Nat.nat]) =>
 (List[Nat.nat]) =>
   Nat.nat =>
     (FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
       (FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat),
                      Transition.transition_ext[A, Unit]))]) =>
         (FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[A, Unit]))]) =>
           ((FSet.fset[((Nat.nat, Nat.nat),
                         Transition.transition_ext[A, Unit])]) =>
             Boolean) =>
             Option[FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit]))]],
                                    np: (FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]) =>
  FSet.fset[(Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[A, Unit], List[Nat.nat]),
                  (Transition.transition_ext[A, Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  drop_all_guards[A](pta, pta, log, m, np)

} /* object PTA_Generalisation */

object SelectionStrategies {

def leaves[A](t1ID: List[Nat.nat], t2ID: List[Nat.nat],
               e: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t1ID)
    val t2: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t2ID);
    (if ((Transition.Label[A, Unit](t1) ==
           Transition.Label[A, Unit](t2)) && ((Nat.equal_nata(Transition.Arity[A,
Unit](t1),
                       Transition.Arity[A,
 Unit](t2))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[A,
                      Unit](t1)).par.length),
                                 Nat.Nata((Transition.Outputs[A,
                       Unit](t2)).par.length)))))
      Nat.plus_nata(Inference.origin[A](t1ID, e), Inference.origin[A](t2ID, e))
      else Nat.zero_nata)
  }

def naive_score[A](t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                    e: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t1ID)
    val t2: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t2ID);
    Inference.bool2nat((Transition.Label[A, Unit](t1) ==
                         Transition.Label[A,
   Unit](t2)) && ((Nat.equal_nata(Transition.Arity[A, Unit](t1),
                                   Transition.Arity[A,
             Unit](t2))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[A,
                                  Unit](t1)).par.length),
     Nat.Nata((Transition.Outputs[A, Unit](t2)).par.length)))))
  }

def exactly_equal[A : HOL.equal](t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                                  e: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  Inference.bool2nat(Transition.equal_transition_exta[A,
               Unit](Inference.get_by_ids[A](e, t1ID),
                      Inference.get_by_ids[A](e, t2ID)))

def naive_score_outputs[A : HOL.equal](t1ID: List[Nat.nat], t2ID: List[Nat.nat],
e: FSet.fset[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t1ID)
    val t2: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t2ID);
    Nat.plus_nata(Nat.plus_nata(Inference.bool2nat(Transition.Label[A,
                             Unit](t1) ==
             Transition.Label[A, Unit](t2)),
                                 Inference.bool2nat(Nat.equal_nata(Transition.Arity[A,
     Unit](t1),
                            Transition.Arity[A, Unit](t2)))),
                   Inference.bool2nat(Lista.equal_lista[AExp.aexp[VName.vname,
                           A]](Transition.Outputs[A, Unit](t1),
                                Transition.Outputs[A, Unit](t2))))
  }

def naive_score_eq_bonus[A : HOL.equal](t1ID: List[Nat.nat],
 t2ID: List[Nat.nat],
 e: FSet.fset[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t1ID)
    val a: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t2ID);
    Inference.score_transitions[A](t1, a)
  }

def naive_score_comprehensive[A : HOL.equal](t1ID: List[Nat.nat],
      t2ID: List[Nat.nat],
      e: FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t1ID)
    val t2: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t2ID);
    (if ((Transition.Label[A, Unit](t1) ==
           Transition.Label[A, Unit](t2)) && (Nat.equal_nata(Transition.Arity[A,
                                       Unit](t1),
                      Transition.Arity[A, Unit](t2))))
      (if (Nat.equal_nata(Nat.Nata((Transition.Outputs[A,
                Unit](t1)).par.length),
                           Nat.Nata((Transition.Outputs[A,
                 Unit](t2)).par.length)))
        Nat.plus_nata(Finite_Set.card[GExp.gexp[VName.vname,
         A]](Set.inf_set[GExp.gexp[VName.vname,
                                    A]](Set.seta[GExp.gexp[VName.vname,
                    A]](Transition.Guards[A, Unit](t1)),
 Set.seta[GExp.gexp[VName.vname, A]](Transition.Guards[A, Unit](t2)))),
                       Nat.Nata((Lista.filter[(AExp.aexp[VName.vname, A],
        AExp.aexp[VName.vname,
                   A])](((a: (AExp.aexp[VName.vname, A],
                               AExp.aexp[VName.vname, A]))
                           =>
                          {
                            val (aa, b):
                                  (AExp.aexp[VName.vname, A],
                                    AExp.aexp[VName.vname, A])
                              = a;
                            AExp.equal_aexpa[VName.vname, A](aa, b)
                          }),
                         (Transition.Outputs[A,
      Unit](t1)).par.zip(Transition.Outputs[A, Unit](t2)).toList)).par.length))
        else Nat.zero_nata)
      else Nat.zero_nata)
  }

def naive_score_comprehensive_eq_high[A : HOL.equal](t1ID: List[Nat.nat],
              t2ID: List[Nat.nat],
              e: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[A, Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t1ID)
    val t2: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](e, t2ID);
    (if (Transition.equal_transition_exta[A, Unit](t1, t2))
      Code_Numeral.nat_of_integer(BigInt(100))
      else (if ((Transition.Label[A, Unit](t1) ==
                  Transition.Label[A, Unit](t2)) && (Nat.equal_nata(Transition.Arity[A,
      Unit](t1),
                             Transition.Arity[A, Unit](t2))))
             (if (Nat.equal_nata(Nat.Nata((Transition.Outputs[A,
                       Unit](t1)).par.length),
                                  Nat.Nata((Transition.Outputs[A,
                        Unit](t2)).par.length)))
               Nat.plus_nata(Finite_Set.card[GExp.gexp[VName.vname,
                A]](Set.inf_set[GExp.gexp[VName.vname,
   A]](Set.seta[GExp.gexp[VName.vname, A]](Transition.Guards[A, Unit](t1)),
        Set.seta[GExp.gexp[VName.vname, A]](Transition.Guards[A, Unit](t2)))),
                              Nat.Nata((Lista.filter[(AExp.aexp[VName.vname, A],
               AExp.aexp[VName.vname,
                          A])](((a: (AExp.aexp[VName.vname, A],
                                      AExp.aexp[VName.vname, A]))
                                  =>
                                 {
                                   val (aa, b):
 (AExp.aexp[VName.vname, A], AExp.aexp[VName.vname, A])
                                     = a;
                                   AExp.equal_aexpa[VName.vname, A](aa, b)
                                 }),
                                (Transition.Outputs[A,
             Unit](t1)).par.zip(Transition.Outputs[A,
            Unit](t2)).toList)).par.length))
               else Nat.zero_nata)
             else Nat.zero_nata))
  }

} /* object SelectionStrategies */

object Distinguishing_Guards {

def add_guard[A](t: Transition.transition_ext[A, Unit],
                  g: GExp.gexp[VName.vname, A]):
      Transition.transition_ext[A, Unit]
  =
  Transition.Guards_update[A, Unit](((_: List[GExp.gexp[VName.vname, A]]) =>
                                      Lista.insert[GExp.gexp[VName.vname,
                      A]](g, Transition.Guards[A, Unit](t))),
                                     t)

def trace_collect_training_sets[A : HOL.equal : Value.aexp_value](x0:
                            List[(String, (List[A], List[A]))],
                           uPTA: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                           s: Nat.nat, registers: Map[Nat.nat, Option[A]],
                           t1: List[Nat.nat], t2: List[Nat.nat],
                           g1: List[(List[A], Map[Nat.nat, Option[A]])],
                           g2: List[(List[A], Map[Nat.nat, Option[A]])]):
      (List[(List[A], Map[Nat.nat, Option[A]])],
        List[(List[A], Map[Nat.nat, Option[A]])])
  =
  (x0, uPTA, s, registers, t1, t2, g1, g2) match {
  case (Nil, uPTA, s, registers, t1, t2, g1, g2) => (g1, g2)
  case ((label, (inputs, outputs)) :: t, uPTA, s, registers, t1, t2, g1, g2) =>
    {
      val (uids, (sa, tran)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[A,
                Unit]))](FSet.ffilter[(List[Nat.nat],
(Nat.nat,
  Transition.transition_ext[A, Unit]))](((a:
    (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit])))
   =>
  {
    val (_, (_, tran)):
          (List[Nat.nat], (Nat.nat, Transition.transition_ext[A, Unit]))
      = a;
    Lista.equal_lista[Option[A]](Transition.apply_outputs[A](Transition.Outputs[A,
 Unit](tran),
                      AExp.join_ir[A](inputs, registers)),
                                  Lista.map[A,
     Option[A]](((aa: A) => Some[A](aa)), outputs))
  }),
 Inference.i_possible_steps[A](uPTA, s, registers, label, inputs)))
      val updated: Map[Nat.nat, Option[A]] =
        (Transition.apply_updates[A](Transition.Updates[A, Unit](tran),
                                      AExp.join_ir[A](inputs,
               registers))).apply(registers);
      (if (t1.contains(uids.head))
        trace_collect_training_sets[A](t, uPTA, sa, updated, t1, t2,
(inputs, registers) :: g1, g2)
        else (if (t2.contains(uids.head))
               trace_collect_training_sets[A](t, uPTA, sa, updated, t1, t2, g1,
       (inputs, registers) :: g2)
               else trace_collect_training_sets[A](t, uPTA, sa, updated, t1, t2,
            g1, g2)))
    }
}

def collect_training_sets[A : HOL.equal : Orderings.order : Value.aexp_value](x0:
List[List[(String, (List[A], List[A]))]],
                                       uPTA:
 FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                       t1: List[Nat.nat], t2: List[Nat.nat],
                                       g1:
 List[(List[A], Map[Nat.nat, Option[A]])],
                                       g2:
 List[(List[A], Map[Nat.nat, Option[A]])]):
      (List[(List[A], Map[Nat.nat, Option[A]])],
        List[(List[A], Map[Nat.nat, Option[A]])])
  =
  (x0, uPTA, t1, t2, g1, g2) match {
  case (Nil, uPTA, t1, t2, g1, g2) => (g1, g2)
  case (h :: t, uPTA, t1, t2, g1, g2) =>
    {
      val (g1a, g2a):
            (List[(List[A], Map[Nat.nat, Option[A]])],
              List[(List[A], Map[Nat.nat, Option[A]])])
        = trace_collect_training_sets[A](h, uPTA, Nat.zero_nata,
  AExp.null_state[Nat.nat, Option[A]], t1, t2, Nil, Nil);
      collect_training_sets[A](t, uPTA, t1, t2,
                                Lista.union[(List[A],
      Map[Nat.nat, Option[A]])].apply(g1).apply(g1a),
                                Lista.union[(List[A],
      Map[Nat.nat, Option[A]])].apply(g2).apply(g2a))
    }
}

def put_updates[A](uids: List[Nat.nat],
                    updates: List[(Nat.nat, AExp.aexp[VName.vname, A])],
                    iefsm:
                      FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[A,
      Unit]))](((a: (List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])))
                  =>
                 {
                   val (uid, (fromTo, tran)):
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[A, Unit]))
                     = a
                   val List(u): List[Nat.nat] = uid;
                   (if (uids.contains(u))
                     (uid, (fromTo,
                             Transition.transition_exta[A,
                 Unit](Transition.Label[A, Unit](tran),
                        Transition.Arity[A, Unit](tran),
                        Transition.Guards[A, Unit](tran),
                        Transition.Outputs[A, Unit](tran),
                        Transition.Updates[A, Unit](tran) ++ updates, ())))
                     else (uid, (fromTo, tran)))
                 }),
                iefsm)

def transfer_updates[A : HOL.equal : Orderings.linorder](e:
                   FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[A, Unit]))],
                  pta: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))]
  =
  Lista.fold[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit])),
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A,
               Unit]))]](((a: (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit])))
                            =>
                           {
                             val (tids, aa):
                                   (List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[A, Unit]))
                               = a
                             val (ab, b):
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[A, Unit])
                               = aa;
                             ({
                                val (_, _): (Nat.nat, Nat.nat) = ab;
                                ((tran: Transition.transition_ext[A, Unit]) =>
                                  ((ac: FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))])
                                     =>
                                    put_updates[A](tids,
            Transition.Updates[A, Unit](tran), ac)))
                              })(b)
                           }),
                          FSet.sorted_list_of_fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))](e),
                          pta)

def distinguish[A : HOL.equal : Orderings.linorder : Value.aexp_value](log:
                                 List[List[(String, (List[A], List[A]))]],
                                t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                                s: Nat.nat,
                                destMerge:
                                  FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                preDestMerge:
                                  FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                old: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[A, Unit]))],
                                check:
                                  (FSet.fset[((Nat.nat, Nat.nat),
       Transition.transition_ext[A, Unit])]) =>
                                    Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[A, Unit]))]]
  =
  {
    val t1: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](destMerge, t1ID)
    val t2: Transition.transition_ext[A, Unit] =
      Inference.get_by_ids[A](destMerge, t2ID)
    val uPTA: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[A, Unit]))]
      = transfer_updates[A](destMerge, Inference.make_pta[A](log))
    val (g1, g2):
          (List[(List[A], Map[Nat.nat, Option[A]])],
            List[(List[A], Map[Nat.nat, Option[A]])])
      = collect_training_sets[A](log, uPTA, t1ID, t2ID, Nil, Nil);
    (Dirties.findDistinguishingGuards[A](g1, g2) match {
       case None => None
       case Some((g1a, g2a)) =>
         {
           val rep: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[A, Unit]))]
             = Inference.replace_transitions[A](preDestMerge,
         List((t1ID, add_guard[A](t1, g1a)), (t2ID, add_guard[A](t2, g2a))));
           (if (check(Inference.tm[A](rep)))
             Some[FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[A, Unit]))]](rep)
             else None)
         }
     })
  }

} /* object Distinguishing_Guards */
