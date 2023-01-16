object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal{
  implicit def
    `Transition.equal_transition_ext`[A : equal]:
      equal[Transition.transition_ext[A]]
    = new equal[Transition.transition_ext[A]] {
    val `HOL.equal` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition.equal_transition_exta[A](a, b)
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
  implicit def
    `Registers.equal_registers`: equal[Map[Nat.nat, Option[Value.value]]] = new
    equal[Map[Nat.nat, Option[Value.value]]] {
    val `HOL.equal` =
      (a: Map[Nat.nat, Option[Value.value]],
        b: Map[Nat.nat, Option[Value.value]])
      => a == b
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
  implicit def `GExp.equal_gexp`[A : equal]: equal[GExp.gexp[A]] = new
    equal[GExp.gexp[A]] {
    val `HOL.equal` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp.equal_gexpa[A](a, b)
  }
  implicit def `FSet.equal_fset`[A : equal]: equal[FSet.fset[A]] = new
    equal[FSet.fset[A]] {
    val `HOL.equal` = (a: FSet.fset[A], b: FSet.fset[A]) =>
      FSet.equal_fseta[A](a, b)
  }
  implicit def `AExp.equal_aexp`[A : equal]: equal[AExp.aexp[A]] = new
    equal[AExp.aexp[A]] {
    val `HOL.equal` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp.equal_aexpa[A](a, b)
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

def less_eq_bool(x0: Boolean, b: Boolean): Boolean = (x0, b) match {
  case (true, b) => b
  case (false, b) => true
}

def less_bool(x0: Boolean, b: Boolean): Boolean = (x0, b) match {
  case (true, b) => false
  case (false, b) => b
}

trait ord[A] {
  val `Orderings.less_eq`: (A, A) => Boolean
  val `Orderings.less`: (A, A) => Boolean
}
def less_eq[A](a: A, b: A)(implicit A: ord[A]): Boolean =
  A.`Orderings.less_eq`(a, b)
def less[A](a: A, b: A)(implicit A: ord[A]): Boolean = A.`Orderings.less`(a, b)
object ord{
  implicit def
    `Transition_Lexorder.ord_transition_ext`[A : HOL.equal : linorder]:
      ord[Transition.transition_ext[A]]
    = new ord[Transition.transition_ext[A]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Lexorder.less_eq_transition_ext[A](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Lexorder.less_transition_ext[A](a, b)
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
    `GExp_Lexorder.ord_gexp`[A : HOL.equal : linorder]: ord[GExp.gexp[A]] = new
    ord[GExp.gexp[A]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Lexorder.less_eq_gexp[A](a, b)
    val `Orderings.less` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Lexorder.less_gexp[A](a, b)
  }
  implicit def
    `AExp_Lexorder.ord_aexp`[A : HOL.equal : linorder]: ord[AExp.aexp[A]] = new
    ord[AExp.aexp[A]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp_Lexorder.less_eq_aexp[A](a, b)
    val `Orderings.less` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp_Lexorder.less_aexp[A](a, b)
  }
  implicit def `Orderings.ord_bool`: ord[Boolean] = new ord[Boolean] {
    val `Orderings.less_eq` = (a: Boolean, b: Boolean) => less_eq_bool(a, b)
    val `Orderings.less` = (a: Boolean, b: Boolean) => less_bool(a, b)
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
object preorder{
  implicit def
    `Transition_Lexorder.preorder_transition_ext`[A : HOL.equal : linorder]:
      preorder[Transition.transition_ext[A]]
    = new preorder[Transition.transition_ext[A]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Lexorder.less_eq_transition_ext[A](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Lexorder.less_transition_ext[A](a, b)
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
    `GExp_Lexorder.preorder_gexp`[A : HOL.equal : linorder]:
      preorder[GExp.gexp[A]]
    = new preorder[GExp.gexp[A]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Lexorder.less_eq_gexp[A](a, b)
    val `Orderings.less` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Lexorder.less_gexp[A](a, b)
  }
  implicit def
    `AExp_Lexorder.preorder_aexp`[A : HOL.equal : linorder]:
      preorder[AExp.aexp[A]]
    = new preorder[AExp.aexp[A]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp_Lexorder.less_eq_aexp[A](a, b)
    val `Orderings.less` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp_Lexorder.less_aexp[A](a, b)
  }
  implicit def `Orderings.preorder_bool`: preorder[Boolean] = new
    preorder[Boolean] {
    val `Orderings.less_eq` = (a: Boolean, b: Boolean) => less_eq_bool(a, b)
    val `Orderings.less` = (a: Boolean, b: Boolean) => less_bool(a, b)
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
object order{
  implicit def
    `Transition_Lexorder.order_transition_ext`[A : HOL.equal : linorder]:
      order[Transition.transition_ext[A]]
    = new order[Transition.transition_ext[A]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Lexorder.less_eq_transition_ext[A](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Lexorder.less_transition_ext[A](a, b)
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
    `GExp_Lexorder.order_gexp`[A : HOL.equal : linorder]: order[GExp.gexp[A]] =
    new order[GExp.gexp[A]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Lexorder.less_eq_gexp[A](a, b)
    val `Orderings.less` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Lexorder.less_gexp[A](a, b)
  }
  implicit def
    `AExp_Lexorder.order_aexp`[A : HOL.equal : linorder]: order[AExp.aexp[A]] =
    new order[AExp.aexp[A]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp_Lexorder.less_eq_aexp[A](a, b)
    val `Orderings.less` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp_Lexorder.less_aexp[A](a, b)
  }
  implicit def `Orderings.order_bool`: order[Boolean] = new order[Boolean] {
    val `Orderings.less_eq` = (a: Boolean, b: Boolean) => less_eq_bool(a, b)
    val `Orderings.less` = (a: Boolean, b: Boolean) => less_bool(a, b)
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
object linorder{
  implicit def
    `Transition_Lexorder.linorder_transition_ext`[A : HOL.equal : linorder]:
      linorder[Transition.transition_ext[A]]
    = new linorder[Transition.transition_ext[A]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Lexorder.less_eq_transition_ext[A](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Lexorder.less_transition_ext[A](a, b)
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
    `AExp_Lexorder.linorder_aexp`[A : HOL.equal : linorder]:
      linorder[AExp.aexp[A]]
    = new linorder[AExp.aexp[A]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp_Lexorder.less_eq_aexp[A](a, b)
    val `Orderings.less` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp_Lexorder.less_aexp[A](a, b)
  }
  implicit def `Orderings.linorder_bool`: linorder[Boolean] = new
    linorder[Boolean] {
    val `Orderings.less_eq` = (a: Boolean, b: Boolean) => less_eq_bool(a, b)
    val `Orderings.less` = (a: Boolean, b: Boolean) => less_bool(a, b)
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

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def min[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) a else b)

} /* object Orderings */

object Groups {

trait plus[A] {
  val `Groups.plus`: (A, A) => A
}
def plus[A](a: A, b: A)(implicit A: plus[A]): A = A.`Groups.plus`(a, b)
object plus{
  implicit def `Nat.plus_nat`: plus[Nat.nat] = new plus[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait semigroup_add[A] extends plus[A] {
}
object semigroup_add{
  implicit def `Nat.semigroup_add_nat`: semigroup_add[Nat.nat] = new
    semigroup_add[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait zero[A] {
  val `Groups.zero`: A
}
def zero[A](implicit A: zero[A]): A = A.`Groups.zero`
object zero{
  implicit def `Nat.zero_nat`: zero[Nat.nat] = new zero[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata
  }
}

trait monoid_add[A] extends semigroup_add[A] with zero[A] {
}
object monoid_add{
  implicit def `Nat.monoid_add_nat`: monoid_add[Nat.nat] = new
    monoid_add[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait ab_semigroup_add[A] extends semigroup_add[A] {
}
object ab_semigroup_add{
  implicit def `Nat.ab_semigroup_add_nat`: ab_semigroup_add[Nat.nat] = new
    ab_semigroup_add[Nat.nat] {
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

trait comm_monoid_add[A] extends ab_semigroup_add[A] with monoid_add[A] {
}
object comm_monoid_add{
  implicit def `Nat.comm_monoid_add_nat`: comm_monoid_add[Nat.nat] = new
    comm_monoid_add[Nat.nat] {
    val `Groups.zero` = Nat.zero_nata
    val `Groups.plus` = (a: Nat.nat, b: Nat.nat) => Nat.plus_nata(a, b)
  }
}

} /* object Groups */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

} /* object Num */

object Product_Type {

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => (HOL.eq[A](x1, y1)) && (HOL.eq[B](x2, y2))
}

def equal_unita(u: Unit, v: Unit): Boolean = true

def less_eq_unit(uu: Unit, uv: Unit): Boolean = true

def less_unit(uu: Unit, uv: Unit): Boolean = false

def apsnd[A, B, C](f: A => B, x1: (C, A)): (C, B) = (f, x1) match {
  case (f, (x, y)) => (x, f(y))
}

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

def Bex[A](x0: set[A], p: A => Boolean): Boolean = (x0, p) match {
  case (seta(xs), p) => Lista.list_ex[A](p, xs)
}

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
  case (x, seta(s)) => (if (s.contains(x)) seta[A](s) else seta[A]((x::s)))
}

def member[A](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, seta(xs)) => xs.contains(x)
}

def remove[A : HOL.equal](a: A, x1: set[A]): set[A] = (a, x1) match {
  case (a, seta(l)) =>
    seta[A](Lista.filter[A](((x: A) => ! (HOL.eq[A](x, a))), l))
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

def less_set[A](a: set[A], b: set[A]): Boolean =
  (less_eq_set[A](a, b)) && (! (less_eq_set[A](b, a)))

def equal_set[A : HOL.equal](a: set[A], b: set[A]): Boolean =
  (less_eq_set[A](a, b)) && (less_eq_set[A](b, a))

} /* object Set */

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
  case (n, (x::xs)) =>
    (if (Nat.equal_nata(n, Nat.zero_nata)) (x::xs)
      else drop[A](Nat.minus_nat(n, Nat.Nata((1))), xs))
}

def find[A](uu: A => Boolean, x1: List[A]): Option[A] = (uu, x1) match {
  case (uu, Nil) => None
  case (p, (x::xs)) => (if (p(x)) Some[A](x) else find[A](p, xs))
}

def fold[A, B](f: A => B => B, xs: List[A], s: B): B =
  Dirties.foldl[B, A](((x: B) => (sa: A) => (f(sa))(x)), s, xs)

def maps[A, B](f: A => List[B], l: List[A]): List[B] = l.par.flatMap(f).toList

def foldr[A, B](f: A => B => B, xs: List[A], a: B): B =
  Dirties.foldl[B, A](((x: B) => (y: A) => (f(y))(x)), a, xs.par.reverse.toList)

def insert[A](x: A, xs: List[A]): List[A] =
  (if (xs.contains(x)) xs else (x::xs))

def union[A]: (List[A]) => (List[A]) => List[A] =
  ((a: List[A]) => (b: List[A]) =>
    fold[A, List[A]](((aa: A) => (ba: List[A]) => insert[A](aa, ba)), a, b))

def filter[A](l: A => Boolean, f: List[A]): List[A] = f.par.filter(l).toList

def tl[A](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case (x21::x22) => x22
}

def list_ex[A](f: A => Boolean, l: List[A]): Boolean = l.par.exists(f)

def map[A, B](f: A => B, l: List[A]): List[B] = l.par.map(f).toList

def product[A, B](xs: List[A], ys: List[B]): List[(A, B)] =
  maps[A, (A, B)](((x: A) => map[B, (A, B)](((a: B) => (x, a)), ys)), xs)

def enumerate[A](n: Nat.nat, xs: List[A]): List[(Nat.nat, A)] =
  (upt(n, Nat.plus_nata(n, Nat.Nata(xs.par.length)))).par.zip(xs).toList

def takeWhile[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, (x::xs)) => (if (p(x)) (x::(takeWhile[A](p, xs))) else Nil)
}

def transpose[A](x0: List[List[A]]): List[List[A]] = x0 match {
  case Nil => Nil
  case (Nil::xss) => transpose[A](xss)
  case (((x::xs))::xss) =>
    (((x::(maps[List[A],
                 A](((a: List[A]) => (a match {
case Nil => Nil
case (h::_) => (h::Nil)
                                      })),
                     xss))))::(transpose[A]((xs::(maps[List[A],
                List[A]](((a: List[A]) => (a match {
     case Nil => Nil
     case (_::t) => (t::Nil)
   })),
                          xss))))))
}

def list_update[A](x0: List[A], i: Nat.nat, y: A): List[A] = (x0, i, y) match {
  case (Nil, i, y) => Nil
  case ((x::xs), i, y) =>
    (if (Nat.equal_nata(i, Nat.zero_nata)) (y::xs)
      else (x::(list_update[A](xs, Nat.minus_nat(i, Nat.Nata((1))), y))))
}

def insort_key[A, B : Orderings.linorder](f: A => B, x: A, xa2: List[A]):
      List[A]
  =
  (f, x, xa2) match {
  case (f, x, Nil) => (x::Nil)
  case (f, x, (y::ys)) =>
    (if (Orderings.less_eq[B](f(x), f(y))) (x::((y::ys)))
      else (y::(insort_key[A, B](f, x, ys))))
}

def sort_key[A, B : Orderings.linorder](f: A => B, xs: List[A]): List[A] =
  foldr[A, List[A]](((a: A) => (b: List[A]) => insort_key[A, B](f, a, b)), xs,
                     Nil)

def sorted_list_of_set[A : Orderings.linorder](x0: Set.set[A]): List[A] = x0
  match {
  case Set.seta(l) => (l.par.distinct.toList).sortWith((Orderings.less))
}

} /* object Lista */

object Code_Target_List {

def upt_tailrec(i: Nat.nat, j: Nat.nat, l: List[Nat.nat]): List[Nat.nat] =
  (if (Nat.equal_nata(j, Nat.zero_nata)) l
    else (if (Nat.less_eq_nat(i, Nat.minus_nat(j, Nat.Nata((1)))))
           upt_tailrec(i, Nat.minus_nat(j, Nat.Nata((1))),
                        ((Nat.minus_nat(j, Nat.Nata((1))))::Nil) ++ l)
           else l))

} /* object Code_Target_List */

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

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (BigInt(0) < l)
           (if (BigInt(0) < k)
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k.abs /% l.abs)).apply(k).apply(l)
             else {
                    val (r, s): (BigInt, BigInt) =
                      ((k: BigInt) => (l: BigInt) => if (l == 0)
                        (BigInt(0), k) else (k.abs /% l.abs)).apply(k).apply(l);
                    (if (s == BigInt(0)) ((- r), BigInt(0))
                      else ((- r) - BigInt(1), l - s))
                  })
           else (if (l == BigInt(0)) (BigInt(0), k)
                  else Product_Type.apsnd[BigInt, BigInt,
   BigInt](((a: BigInt) => (- a)),
            (if (k < BigInt(0))
              ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
                (k.abs /% l.abs)).apply(k).apply(l)
              else {
                     val (r, s): (BigInt, BigInt) =
                       ((k: BigInt) => (l: BigInt) => if (l == 0)
                         (BigInt(0), k) else
                         (k.abs /% l.abs)).apply(k).apply(l);
                     (if (s == BigInt(0)) ((- r), BigInt(0))
                       else ((- r) - BigInt(1), (- l) - s))
                   })))))

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

def nat_of_integer(k: BigInt): Nat.nat =
  Nat.Nata(Orderings.max[BigInt](BigInt(0), k))

def integer_of_int(x0: Int.int): BigInt = x0 match {
  case Int.int_of_integer(k) => k
}

def divide_integer(k: BigInt, l: BigInt): BigInt = (divmod_integer(k, l))._1

def modulo_integer(k: BigInt, l: BigInt): BigInt = (divmod_integer(k, l))._2

} /* object Code_Numeral */

object Int {

abstract sealed class int
final case class int_of_integer(a: BigInt) extends int

def less_eq_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) <= Code_Numeral.integer_of_int(l)

def less_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) < Code_Numeral.integer_of_int(l)

def nat(k: int): Nat.nat =
  Nat.Nata(Orderings.max[BigInt](BigInt(0), Code_Numeral.integer_of_int(k)))

def one_int: int = int_of_integer(BigInt(1))

def plus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) +
                   Code_Numeral.integer_of_int(l))

def zero_int: int = int_of_integer(BigInt(0))

def equal_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

def minus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) -
                   Code_Numeral.integer_of_int(l))

def times_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) *
                   Code_Numeral.integer_of_int(l))

def uminus_int(k: int): int =
  int_of_integer((- (Code_Numeral.integer_of_int(k))))

} /* object Int */

object GCD {

def gcd_int(x0: Int.int, x1: Int.int): Int.int = (x0, x1) match {
  case (Int.int_of_integer(x), Int.int_of_integer(y)) =>
    Int.int_of_integer(x.gcd(y))
}

} /* object GCD */

object Euclidean_Division {

def divide_int(k: Int.int, l: Int.int): Int.int =
  Int.int_of_integer(Code_Numeral.divide_integer(Code_Numeral.integer_of_int(k),
          Code_Numeral.integer_of_int(l)))

def divide_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Code_Numeral.divide_integer(Code_Numeral.integer_of_nat(m),
Code_Numeral.integer_of_nat(n)))

def modulo_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Code_Numeral.modulo_integer(Code_Numeral.integer_of_nat(m),
Code_Numeral.integer_of_nat(n)))

} /* object Euclidean_Division */

object Rat {

abstract sealed class rat
final case class Frct(a: (Int.int, Int.int)) extends rat

def of_int(a: Int.int): rat = Frct((a, Int.one_int))

def normalize(p: (Int.int, Int.int)): (Int.int, Int.int) =
  (if (Int.less_int(Int.zero_int, p._2))
    {
      val a: Int.int = GCD.gcd_int(p._1, p._2);
      (Euclidean_Division.divide_int(p._1, a),
        Euclidean_Division.divide_int(p._2, a))
    }
    else (if (Int.equal_int(p._2, Int.zero_int)) (Int.zero_int, Int.one_int)
           else {
                  val a: Int.int = Int.uminus_int(GCD.gcd_int(p._1, p._2));
                  (Euclidean_Division.divide_int(p._1, a),
                    Euclidean_Division.divide_int(p._2, a))
                }))

def quotient_of(x0: rat): (Int.int, Int.int) = x0 match {
  case Frct(x) => x
}

def less_rat(p: rat, q: rat): Boolean =
  {
    val a: (Int.int, Int.int) = quotient_of(p)
    val (aa, c): (Int.int, Int.int) = a
    val b: (Int.int, Int.int) = quotient_of(q)
    val (ba, d): (Int.int, Int.int) = b;
    Int.less_int(Int.times_int(aa, d), Int.times_int(c, ba))
  }

def plus_rat(p: rat, q: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, c): (Int.int, Int.int) = a
         val b: (Int.int, Int.int) = quotient_of(q)
         val (ba, d): (Int.int, Int.int) = b;
         normalize((Int.plus_int(Int.times_int(aa, d), Int.times_int(ba, c)),
                     Int.times_int(c, d)))
       })

def zero_rat: rat = Frct((Int.zero_int, Int.one_int))

def minus_rat(p: rat, q: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, c): (Int.int, Int.int) = a
         val b: (Int.int, Int.int) = quotient_of(q)
         val (ba, d): (Int.int, Int.int) = b;
         normalize((Int.minus_int(Int.times_int(aa, d), Int.times_int(ba, c)),
                     Int.times_int(c, d)))
       })

def times_rat(p: rat, q: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, c): (Int.int, Int.int) = a
         val b: (Int.int, Int.int) = quotient_of(q)
         val (ba, d): (Int.int, Int.int) = b;
         normalize((Int.times_int(aa, ba), Int.times_int(c, d)))
       })

def divide_rat(p: rat, q: rat): rat =
  Frct({
         val a: (Int.int, Int.int) = quotient_of(p)
         val (aa, c): (Int.int, Int.int) = a
         val b: (Int.int, Int.int) = quotient_of(q)
         val (ba, d): (Int.int, Int.int) = b;
         normalize((Int.times_int(aa, d), Int.times_int(c, ba)))
       })

def floor_rat(p: rat): Int.int = {
                                   val a: (Int.int, Int.int) = quotient_of(p)
                                   val (aa, b): (Int.int, Int.int) = a;
                                   Euclidean_Division.divide_int(aa, b)
                                 }

} /* object Rat */

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

object Real {

abstract sealed class real
final case class Ratreal(a: Rat.rat) extends real

def less_real(x0: real, x1: real): Boolean = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Rat.less_rat(x, y)
}

def plus_real(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.plus_rat(x, y))
}

def zero_real: real = Ratreal(Rat.zero_rat)

def minus_real(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.minus_rat(x, y))
}

def times_real(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.times_rat(x, y))
}

def divide_real(x0: real, x1: real): real = (x0, x1) match {
  case (Ratreal(x), Ratreal(y)) => Ratreal(Rat.divide_rat(x, y))
}

def floor_real(x0: real): Int.int = x0 match {
  case Ratreal(x) => Rat.floor_rat(x)
}

} /* object Real */

object Value {

abstract sealed class value
final case class Inta(a: Int.int) extends value
final case class Reala(a: Real.real) extends value
final case class Str(a: String) extends value

def equal_valuea(x0: value, x1: value): Boolean = (x0, x1) match {
  case (Reala(x2), Str(x3)) => false
  case (Str(x3), Reala(x2)) => false
  case (Inta(x1), Str(x3)) => false
  case (Str(x3), Inta(x1)) => false
  case (Inta(x1), Reala(x2)) => false
  case (Reala(x2), Inta(x1)) => false
  case (Str(x3), Str(y3)) => x3 == y3
  case (Reala(x2), Reala(y2)) => Dirties.doubleEquals(x2, y2)
  case (Inta(x1), Inta(y1)) => Int.equal_int(x1, y1)
}

def value_eq(x0: Option[value], uu: Option[value]): Trilean.trilean = (x0, uu)
  match {
  case (None, uu) => Trilean.invalid()
  case (Some(v), None) => Trilean.invalid()
  case (Some(a), Some(b)) =>
    (if (equal_valuea(a, b)) Trilean.truea() else Trilean.falsea())
}

def MaybeBoolInt(f: Int.int => Int.int => Boolean, uv: Option[value],
                  uw: Option[value]):
      Trilean.trilean
  =
  (f, uv, uw) match {
  case (f, Some(Inta(a)), Some(Inta(b))) =>
    (if ((f(a))(b)) Trilean.truea() else Trilean.falsea())
  case (uu, None, uw) => Trilean.invalid()
  case (uu, Some(Reala(va)), uw) => Trilean.invalid()
  case (uu, Some(Str(va)), uw) => Trilean.invalid()
  case (uu, uv, None) => Trilean.invalid()
  case (uu, uv, Some(Reala(va))) => Trilean.invalid()
  case (uu, uv, Some(Str(va))) => Trilean.invalid()
}

def value_gt(a: Option[value], b: Option[value]): Trilean.trilean =
  MaybeBoolInt(((x: Int.int) => (y: Int.int) => Int.less_int(y, x)), a, b)

def maybe_arith(f: Real.real => Real.real => Real.real, uv: Option[value],
                 uw: Option[value]):
      Option[value]
  =
  (f, uv, uw) match {
  case (f, Some(Inta(x)), Some(Inta(y))) =>
    Some[value](Inta(Real.floor_real((f(Real.Ratreal(Rat.of_int(x))))(Real.Ratreal(Rat.of_int(y))))))
  case (f, Some(Reala(x)), Some(Reala(y))) => Some[value](Reala((f(x))(y)))
  case (uu, None, uw) => None
  case (uu, Some(Reala(va)), None) => None
  case (uu, Some(Reala(va)), Some(Inta(vb))) => None
  case (uu, Some(Reala(va)), Some(Str(vb))) => None
  case (uu, Some(Str(va)), uw) => None
  case (uu, uv, None) => None
  case (uu, Some(Inta(vb)), Some(Reala(va))) => None
  case (uu, uv, Some(Str(va))) => None
}

def value_plus(a: Option[value], b: Option[value]): Option[value] =
  maybe_arith(((aa: Real.real) => (ba: Real.real) => Real.plus_real(aa, ba)), a,
               b)

def value_minus: Option[value] => Option[value] => Option[value] =
  ((a: Option[value]) => (b: Option[value]) =>
    maybe_arith(((aa: Real.real) => (ba: Real.real) => Real.minus_real(aa, ba)),
                 a, b))

def value_times: Option[value] => Option[value] => Option[value] =
  ((a: Option[value]) => (b: Option[value]) =>
    maybe_arith(((aa: Real.real) => (ba: Real.real) => Real.times_real(aa, ba)),
                 a, b))

def value_divide: Option[value] => Option[value] => Option[value] =
  ((a: Option[value]) => (b: Option[value]) =>
    maybe_arith(((aa: Real.real) => (ba: Real.real) =>
                  Real.divide_real(aa, ba)),
                 a, b))

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

abstract sealed class aexp[A]
final case class L[A](a: Value.value) extends aexp[A]
final case class V[A](a: A) extends aexp[A]
final case class Plus[A](a: aexp[A], b: aexp[A]) extends aexp[A]
final case class Minus[A](a: aexp[A], b: aexp[A]) extends aexp[A]
final case class Times[A](a: aexp[A], b: aexp[A]) extends aexp[A]
final case class Divide[A](a: aexp[A], b: aexp[A]) extends aexp[A]

def equal_aexpa[A : HOL.equal](x0: aexp[A], x1: aexp[A]): Boolean = (x0, x1)
  match {
  case (Times(x51, x52), Divide(x61, x62)) => false
  case (Divide(x61, x62), Times(x51, x52)) => false
  case (Minus(x41, x42), Divide(x61, x62)) => false
  case (Divide(x61, x62), Minus(x41, x42)) => false
  case (Minus(x41, x42), Times(x51, x52)) => false
  case (Times(x51, x52), Minus(x41, x42)) => false
  case (Plus(x31, x32), Divide(x61, x62)) => false
  case (Divide(x61, x62), Plus(x31, x32)) => false
  case (Plus(x31, x32), Times(x51, x52)) => false
  case (Times(x51, x52), Plus(x31, x32)) => false
  case (Plus(x31, x32), Minus(x41, x42)) => false
  case (Minus(x41, x42), Plus(x31, x32)) => false
  case (V(x2), Divide(x61, x62)) => false
  case (Divide(x61, x62), V(x2)) => false
  case (V(x2), Times(x51, x52)) => false
  case (Times(x51, x52), V(x2)) => false
  case (V(x2), Minus(x41, x42)) => false
  case (Minus(x41, x42), V(x2)) => false
  case (V(x2), Plus(x31, x32)) => false
  case (Plus(x31, x32), V(x2)) => false
  case (L(x1), Divide(x61, x62)) => false
  case (Divide(x61, x62), L(x1)) => false
  case (L(x1), Times(x51, x52)) => false
  case (Times(x51, x52), L(x1)) => false
  case (L(x1), Minus(x41, x42)) => false
  case (Minus(x41, x42), L(x1)) => false
  case (L(x1), Plus(x31, x32)) => false
  case (Plus(x31, x32), L(x1)) => false
  case (L(x1), V(x2)) => false
  case (V(x2), L(x1)) => false
  case (Divide(x61, x62), Divide(y61, y62)) =>
    (equal_aexpa[A](x61, y61)) && (equal_aexpa[A](x62, y62))
  case (Times(x51, x52), Times(y51, y52)) =>
    (equal_aexpa[A](x51, y51)) && (equal_aexpa[A](x52, y52))
  case (Minus(x41, x42), Minus(y41, y42)) =>
    (equal_aexpa[A](x41, y41)) && (equal_aexpa[A](x42, y42))
  case (Plus(x31, x32), Plus(y31, y32)) =>
    (equal_aexpa[A](x31, y31)) && (equal_aexpa[A](x32, y32))
  case (V(x2), V(y2)) => HOL.eq[A](x2, y2)
  case (L(x1), L(y1)) => Value.equal_valuea(x1, y1)
}

def aval[A](x0: aexp[A], s: A => Option[Value.value]): Option[Value.value] =
  (x0, s) match {
  case (L(x), s) => Some[Value.value](x)
  case (V(x), s) => s(x)
  case (Plus(a1, a2), s) => Value.value_plus(aval[A](a1, s), aval[A](a2, s))
  case (Minus(a1, a2), s) =>
    Value.value_minus.apply(aval[A](a1, s)).apply(aval[A](a2, s))
  case (Times(a1, a2), s) =>
    Value.value_times.apply(aval[A](a1, s)).apply(aval[A](a2, s))
  case (Divide(a1, a2), s) =>
    Value.value_divide.apply(aval[A](a1, s)).apply(aval[A](a2, s))
}

def is_lit[A](x0: aexp[A]): Boolean = x0 match {
  case L(x) => true
  case V(x) => false
  case Plus(a1, a2) => (is_lit[A](a1)) && (is_lit[A](a2))
  case Minus(a1, a2) => (is_lit[A](a1)) && (is_lit[A](a2))
  case Times(a1, a2) => (is_lit[A](a1)) && (is_lit[A](a2))
  case Divide(a1, a2) => (is_lit[A](a1)) && (is_lit[A](a2))
}

def repeat[A](m: Nat.nat, uu: A): List[A] =
  (if (Nat.equal_nata(m, Nat.zero_nata)) Nil
    else (uu::(repeat[A](Nat.minus_nat(m, Nat.Nata((1))), uu))))

def input2state(n: List[Value.value]): Map[Nat.nat, Option[Value.value]] =
  Lista.fold[(Nat.nat, Value.value),
              Map[Nat.nat, Option[Value.value]]](((a: (Nat.nat, Value.value)) =>
           {
             val (k, v): (Nat.nat, Value.value) = a;
             ((f: Map[Nat.nat, Option[Value.value]]) =>
               (f + ((k -> (Some[Value.value](v))))))
           }),
          Lista.enumerate[Value.value](Nat.zero_nata, n),
          scala.collection.immutable.Map().withDefaultValue(None))

def join_ir(i: List[Value.value], r: Map[Nat.nat, Option[Value.value]]):
      VName.vname => Option[Value.value]
  =
  ((a: VName.vname) => (a match {
                          case VName.I(aa) => (input2state(i))(aa)
                          case VName.R(aa) => r(aa)
                        }))

def rename_regs(uu: Nat.nat => Nat.nat, x1: aexp[VName.vname]):
      aexp[VName.vname]
  =
  (uu, x1) match {
  case (uu, L(l)) => L[VName.vname](l)
  case (f, V(VName.R(r))) => V[VName.vname](VName.R(f(r)))
  case (uv, V(VName.I(va))) => V[VName.vname](VName.I(va))
  case (f, Plus(a, b)) =>
    Plus[VName.vname](rename_regs(f, a), rename_regs(f, b))
  case (f, Minus(a, b)) =>
    Minus[VName.vname](rename_regs(f, a), rename_regs(f, b))
  case (f, Times(a, b)) =>
    Minus[VName.vname](rename_regs(f, a), rename_regs(f, b))
  case (f, Divide(a, b)) =>
    Times[VName.vname](rename_regs(f, a), rename_regs(f, b))
}

def enumerate_regs(x0: aexp[VName.vname]): Set.set[Nat.nat] = x0 match {
  case L(uu) => Set.bot_set[Nat.nat]
  case V(VName.R(n)) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case V(VName.I(uv)) => Set.bot_set[Nat.nat]
  case Plus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_regs(v), enumerate_regs(va))
  case Minus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_regs(v), enumerate_regs(va))
  case Times(v, va) =>
    Set.sup_set[Nat.nat](enumerate_regs(v), enumerate_regs(va))
  case Divide(v, va) =>
    Set.sup_set[Nat.nat](enumerate_regs(v), enumerate_regs(va))
}

def enumerate_aexp_inputs(x0: aexp[VName.vname]): Set.set[Nat.nat] = x0 match {
  case L(uu) => Set.bot_set[Nat.nat]
  case V(VName.I(n)) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case V(VName.R(n)) => Set.bot_set[Nat.nat]
  case Plus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs(v), enumerate_aexp_inputs(va))
  case Minus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs(v), enumerate_aexp_inputs(va))
  case Times(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs(v), enumerate_aexp_inputs(va))
  case Divide(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs(v), enumerate_aexp_inputs(va))
}

def enumerate_vars(a: aexp[VName.vname]): Set.set[VName.vname] =
  Set.sup_set[VName.vname](Set.image[Nat.nat,
                                      VName.vname](((aa: Nat.nat) =>
             VName.I(aa)),
            enumerate_aexp_inputs(a)),
                            Set.image[Nat.nat,
                                       VName.vname](((aa: Nat.nat) =>
              VName.R(aa)),
             enumerate_regs(a)))

def aexp_constrains[A : HOL.equal](x0: aexp[A], a: aexp[A]): Boolean = (x0, a)
  match {
  case (L(l), a) => equal_aexpa[A](L[A](l), a)
  case (V(va), v) => equal_aexpa[A](V[A](va), v)
  case (Plus(a1, a2), v) =>
    (equal_aexpa[A](Plus[A](a1, a2),
                     v)) || ((equal_aexpa[A](Plus[A](a1, a2),
      v)) || ((aexp_constrains[A](a1, v)) || (aexp_constrains[A](a2, v))))
  case (Minus(a1, a2), v) =>
    (equal_aexpa[A](Minus[A](a1, a2),
                     v)) || ((aexp_constrains[A](a1,
          v)) || (aexp_constrains[A](a2, v)))
  case (Times(a1, a2), v) =>
    (equal_aexpa[A](Times[A](a1, a2),
                     v)) || ((aexp_constrains[A](a1,
          v)) || (aexp_constrains[A](a2, v)))
  case (Divide(a1, a2), v) =>
    (equal_aexpa[A](Times[A](a1, a2),
                     v)) || ((aexp_constrains[A](a1,
          v)) || (aexp_constrains[A](a2, v)))
}

def enumerate_aexp_ints[A](x0: aexp[A]): Set.set[Int.int] = x0 match {
  case L(Value.Inta(s)) => Set.insert[Int.int](s, Set.bot_set[Int.int])
  case L(Value.Reala(v)) => Set.bot_set[Int.int]
  case L(Value.Str(v)) => Set.bot_set[Int.int]
  case V(uv) => Set.bot_set[Int.int]
  case Plus(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A](a1), enumerate_aexp_ints[A](a2))
  case Minus(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A](a1), enumerate_aexp_ints[A](a2))
  case Times(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A](a1), enumerate_aexp_ints[A](a2))
  case Divide(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A](a1), enumerate_aexp_ints[A](a2))
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
object finite_UNIV{
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
object card_UNIV{
  implicit def `Cardinality.card_UNIV_nat`: card_UNIV[Nat.nat] = new
    card_UNIV[Nat.nat] {
    val `Cardinality.card_UNIV` = card_UNIV_nata
    val `Cardinality.finite_UNIV` = finite_UNIV_nata
  }
}

} /* object Cardinality */

object Code_Cardinality {

def eq_set[A : Cardinality.card_UNIV](x0: Set.set[A], x1: Set.set[A]): Boolean =
  (x0, x1) match {
  case (Set.seta(xs), Set.seta(ys)) =>
    (Lista.list_all[A](((a: A) => ys.contains(a)),
                        xs)) && (Lista.list_all[A](((a: A) => xs.contains(a)),
            ys))
}

def subset[A : Cardinality.card_UNIV](x0: Set.set[A], x1: Set.set[A]): Boolean =
  (x0, x1) match {
  case (Set.seta(l1), Set.seta(l2)) =>
    Lista.list_all[A](((a: A) => l2.contains(a)), l1)
}

} /* object Code_Cardinality */

object Lattices_Big {

def Max[A : Orderings.linorder](x0: Set.set[A]): A = x0 match {
  case Set.seta((x::xs)) =>
    Lista.fold[A, A](((a: A) => (b: A) => Orderings.max[A](a, b)), xs, x)
}

} /* object Lattices_Big */

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

object GExp {

abstract sealed class gexp[A]
final case class Bc[A](a: Boolean) extends gexp[A]
final case class Eq[A](a: AExp.aexp[A], b: AExp.aexp[A]) extends gexp[A]
final case class Gt[A](a: AExp.aexp[A], b: AExp.aexp[A]) extends gexp[A]
final case class In[A](a: A, b: List[Value.value]) extends gexp[A]
final case class Nor[A](a: gexp[A], b: gexp[A]) extends gexp[A]

def equal_gexpa[A : HOL.equal](x0: gexp[A], x1: gexp[A]): Boolean = (x0, x1)
  match {
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
    (equal_gexpa[A](x51, y51)) && (equal_gexpa[A](x52, y52))
  case (In(x41, x42), In(y41, y42)) =>
    (HOL.eq[A](x41, y41)) && (Lista.equal_lista[Value.value](x42, y42))
  case (Gt(x31, x32), Gt(y31, y32)) =>
    (AExp.equal_aexpa[A](x31, y31)) && (AExp.equal_aexpa[A](x32, y32))
  case (Eq(x21, x22), Eq(y21, y22)) =>
    (AExp.equal_aexpa[A](x21, y21)) && (AExp.equal_aexpa[A](x22, y22))
  case (Bc(x1), Bc(y1)) => x1 == y1
}

def gNot[A](g: gexp[A]): gexp[A] = Nor[A](g, g)

def Lt[A](a: AExp.aexp[A], b: AExp.aexp[A]): gexp[A] = Gt[A](b, a)

def Ge[A](v: AExp.aexp[A], va: AExp.aexp[A]): gexp[A] = gNot[A](Lt[A](v, va))

def Le[A](v: AExp.aexp[A], va: AExp.aexp[A]): gexp[A] = gNot[A](Gt[A](v, va))

def Ne[A](v: AExp.aexp[A], va: AExp.aexp[A]): gexp[A] = gNot[A](Eq[A](v, va))

def gOr[A](v: gexp[A], va: gexp[A]): gexp[A] =
  Nor[A](Nor[A](v, va), Nor[A](v, va))

def gAnd[A](v: gexp[A], va: gexp[A]): gexp[A] =
  Nor[A](Nor[A](v, v), Nor[A](va, va))

def gval[A](x0: gexp[A], uu: A => Option[Value.value]): Trilean.trilean =
  (x0, uu) match {
  case (Bc(true), uu) => Trilean.truea()
  case (Bc(false), uv) => Trilean.falsea()
  case (Gt(a1, a2), s) =>
    Value.value_gt(AExp.aval[A](a1, s), AExp.aval[A](a2, s))
  case (Eq(a1, a2), s) =>
    Value.value_eq(AExp.aval[A](a1, s), AExp.aval[A](a2, s))
  case (In(v, l), s) =>
    (s(v) match {
       case None => Trilean.invalid()
       case Some(vv) =>
         (if (l.contains(vv)) Trilean.truea() else Trilean.falsea())
     })
  case (Nor(a1, a2), s) =>
    Trilean.maybe_not(Trilean.plus_trilean(gval[A](a1, s), gval[A](a2, s)))
}

def fold_In[A](uu: A, x1: List[Value.value]): gexp[A] = (uu, x1) match {
  case (uu, Nil) => Bc[A](false)
  case (v, (l::t)) =>
    gOr[A](Eq[A](AExp.V[A](v), AExp.L[A](l)), fold_In[A](v, t))
}

def rename_regs(uu: Nat.nat => Nat.nat, x1: gexp[VName.vname]):
      gexp[VName.vname]
  =
  (uu, x1) match {
  case (uu, Bc(b)) => Bc[VName.vname](b)
  case (f, Eq(a1, a2)) =>
    Eq[VName.vname](AExp.rename_regs(f, a1), AExp.rename_regs(f, a2))
  case (f, Gt(a1, a2)) =>
    Gt[VName.vname](AExp.rename_regs(f, a1), AExp.rename_regs(f, a2))
  case (f, In(VName.R(r), vs)) => In[VName.vname](VName.R(f(r)), vs)
  case (f, In(VName.I(va), vs)) => In[VName.vname](VName.I(va), vs)
  case (f, Nor(g1, g2)) =>
    Nor[VName.vname](rename_regs(f, g1), rename_regs(f, g2))
}

def apply_guards(g: List[gexp[VName.vname]],
                  s: VName.vname => Option[Value.value]):
      Boolean
  =
  Lista.list_all[Trilean.trilean](((ga: Trilean.trilean) =>
                                    Trilean.equal_trilean(ga, Trilean.truea())),
                                   Lista.map[gexp[VName.vname],
      Trilean.trilean](((ga: gexp[VName.vname]) => gval[VName.vname](ga, s)),
                        g))

def enumerate_regs(x0: gexp[VName.vname]): Set.set[Nat.nat] = x0 match {
  case Bc(uu) => Set.bot_set[Nat.nat]
  case Eq(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_regs(v), AExp.enumerate_regs(va))
  case Gt(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_regs(v), AExp.enumerate_regs(va))
  case In(v, va) => AExp.enumerate_regs(AExp.V[VName.vname](v))
  case Nor(v, va) => Set.sup_set[Nat.nat](enumerate_regs(v), enumerate_regs(va))
}

def enumerate_gexp_inputs(x0: gexp[VName.vname]): Set.set[Nat.nat] = x0 match {
  case Bc(uu) => Set.bot_set[Nat.nat]
  case Eq(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_inputs(v),
                          AExp.enumerate_aexp_inputs(va))
  case Gt(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_inputs(v),
                          AExp.enumerate_aexp_inputs(va))
  case In(v, va) => AExp.enumerate_aexp_inputs(AExp.V[VName.vname](v))
  case Nor(v, va) =>
    Set.sup_set[Nat.nat](enumerate_gexp_inputs(v), enumerate_gexp_inputs(va))
}

def enumerate_vars(g: gexp[VName.vname]): List[VName.vname] =
  Lista.sorted_list_of_set[VName.vname](Set.sup_set[VName.vname](Set.image[Nat.nat,
                                    VName.vname](((a: Nat.nat) => VName.R(a)),
          enumerate_regs(g)),
                          Set.image[Nat.nat,
                                     VName.vname](((a: Nat.nat) => VName.I(a)),
           enumerate_gexp_inputs(g))))

def gexp_constrains[A : HOL.equal](x0: gexp[A], uv: AExp.aexp[A]): Boolean =
  (x0, uv) match {
  case (Bc(uu), uv) => false
  case (Eq(a1, a2), a) =>
    (AExp.aexp_constrains[A](a1, a)) || (AExp.aexp_constrains[A](a2, a))
  case (Gt(a1, a2), a) =>
    (AExp.aexp_constrains[A](a1, a)) || (AExp.aexp_constrains[A](a2, a))
  case (Nor(g1, g2), a) =>
    (gexp_constrains[A](g1, a)) || (gexp_constrains[A](g2, a))
  case (In(v, l), a) => AExp.aexp_constrains[A](AExp.V[A](v), a)
}

def enumerate_gexp_ints[A](x0: gexp[A]): Set.set[Int.int] = x0 match {
  case Bc(uu) => Set.bot_set[Int.int]
  case Eq(a1, a2) =>
    Set.sup_set[Int.int](AExp.enumerate_aexp_ints[A](a1),
                          AExp.enumerate_aexp_ints[A](a2))
  case Gt(a1, a2) =>
    Set.sup_set[Int.int](AExp.enumerate_aexp_ints[A](a1),
                          AExp.enumerate_aexp_ints[A](a2))
  case In(v, l) =>
    Lista.fold[Value.value,
                Set.set[Int.int]](((x: Value.value) =>
                                    (acc: Set.set[Int.int]) =>
                                    (x match {
                                       case Value.Inta(n) =>
 Set.insert[Int.int](n, acc)
                                       case Value.Reala(_) => acc
                                       case Value.Str(_) => acc
                                     })),
                                   l, Set.bot_set[Int.int])
  case Nor(g1, g2) =>
    Set.sup_set[Int.int](enumerate_gexp_ints[A](g1), enumerate_gexp_ints[A](g2))
}

} /* object GExp */

object Transition {

abstract sealed class transition_ext[A]
final case class transition_exta[A](a: String, b: Nat.nat,
                                     c: List[GExp.gexp[VName.vname]],
                                     d: List[AExp.aexp[VName.vname]],
                                     e: List[(Nat.nat, AExp.aexp[VName.vname])],
                                     f: A)
  extends transition_ext[A]

def equal_transition_exta[A : HOL.equal](x0: transition_ext[A],
  x1: transition_ext[A]):
      Boolean
  =
  (x0, x1) match {
  case (transition_exta(labela, aritya, guardsa, outputsa, updatesa, morea),
         transition_exta(label, arity, guards, outputs, updates, more))
    => (labela ==
         label) && ((Nat.equal_nata(aritya,
                                     arity)) && ((Lista.equal_lista[GExp.gexp[VName.vname]](guardsa,
             guards)) && ((Lista.equal_lista[AExp.aexp[VName.vname]](outputsa,
                              outputs)) && ((Lista.equal_lista[(Nat.nat,
                         AExp.aexp[VName.vname])](updatesa,
           updates)) && (HOL.eq[A](morea, more))))))
}

def Updates[A](x0: transition_ext[A]): List[(Nat.nat, AExp.aexp[VName.vname])] =
  x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => updates
}

def Outputs[A](x0: transition_ext[A]): List[AExp.aexp[VName.vname]] = x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => outputs
}

def Guards[A](x0: transition_ext[A]): List[GExp.gexp[VName.vname]] = x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => guards
}

def enumerate_regs(t: transition_ext[Unit]): Set.set[Nat.nat] =
  Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[GExp.gexp[VName.vname],
                  Set.set[Nat.nat]](((a: GExp.gexp[VName.vname]) =>
                                      GExp.enumerate_regs(a)),
                                     Guards[Unit](t)))),
                          Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[AExp.aexp[VName.vname],
                   Set.set[Nat.nat]](((a: AExp.aexp[VName.vname]) =>
                                       AExp.enumerate_regs(a)),
                                      Outputs[Unit](t))))),
     Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                                       AExp.aexp[VName.vname]),
                                      Set.set[Nat.nat]](((a:
                    (Nat.nat, AExp.aexp[VName.vname]))
                   =>
                  {
                    val (_, aa): (Nat.nat, AExp.aexp[VName.vname]) = a;
                    AExp.enumerate_regs(aa)
                  }),
                 Updates[Unit](t))))),
                        Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                  AExp.aexp[VName.vname]),
                 Set.set[Nat.nat]](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
                                     {
                                       val
 (r, _): (Nat.nat, AExp.aexp[VName.vname]) = a;
                                       AExp.enumerate_regs(AExp.V[VName.vname](VName.R(r)))
                                     }),
                                    Updates[Unit](t)))))

def max_reg(t: transition_ext[Unit]): Option[Nat.nat] =
  (if (Code_Cardinality.eq_set[Nat.nat](enumerate_regs(t),
 Set.bot_set[Nat.nat]))
    None else Some[Nat.nat](Lattices_Big.Max[Nat.nat](enumerate_regs(t))))

def Updates_update[A](updatesa:
                        (List[(Nat.nat, AExp.aexp[VName.vname])]) =>
                          List[(Nat.nat, AExp.aexp[VName.vname])],
                       x1: transition_ext[A]):
      transition_ext[A]
  =
  (updatesa, x1) match {
  case (updatesa, transition_exta(label, arity, guards, outputs, updates, more))
    => transition_exta[A](label, arity, guards, outputs, updatesa(updates),
                           more)
}

def Outputs_update[A](outputsa:
                        (List[AExp.aexp[VName.vname]]) =>
                          List[AExp.aexp[VName.vname]],
                       x1: transition_ext[A]):
      transition_ext[A]
  =
  (outputsa, x1) match {
  case (outputsa, transition_exta(label, arity, guards, outputs, updates, more))
    => transition_exta[A](label, arity, guards, outputsa(outputs), updates,
                           more)
}

def Guards_update[A](guardsa:
                       (List[GExp.gexp[VName.vname]]) =>
                         List[GExp.gexp[VName.vname]],
                      x1: transition_ext[A]):
      transition_ext[A]
  =
  (guardsa, x1) match {
  case (guardsa, transition_exta(label, arity, guards, outputs, updates, more))
    => transition_exta[A](label, arity, guardsa(guards), outputs, updates, more)
}

def rename_regs(f: Nat.nat => Nat.nat, t: transition_ext[Unit]):
      transition_ext[Unit]
  =
  Updates_update[Unit](((_: List[(Nat.nat, AExp.aexp[VName.vname])]) =>
                         Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
                                    (Nat.nat,
                                      AExp.aexp[VName.vname])](((a:
                           (Nat.nat, AExp.aexp[VName.vname]))
                          =>
                         {
                           val (r, u): (Nat.nat, AExp.aexp[VName.vname]) = a;
                           (f(r), AExp.rename_regs(f, u))
                         }),
                        Updates[Unit](t))),
                        Outputs_update[Unit](((_: List[AExp.aexp[VName.vname]])
        =>
       Lista.map[AExp.aexp[VName.vname],
                  AExp.aexp[VName.vname]](((a: AExp.aexp[VName.vname]) =>
    AExp.rename_regs(f, a)),
   Outputs[Unit](t))),
      Guards_update[Unit](((_: List[GExp.gexp[VName.vname]]) =>
                            Lista.map[GExp.gexp[VName.vname],
                                       GExp.gexp[VName.vname]](((a:
                           GExp.gexp[VName.vname])
                          =>
                         GExp.rename_regs(f, a)),
                        Guards[Unit](t))),
                           t)))

def apply_outputs[A](p: List[AExp.aexp[A]], s: A => Option[Value.value]):
      List[Option[Value.value]]
  =
  Lista.map[AExp.aexp[A],
             Option[Value.value]](((pa: AExp.aexp[A]) => AExp.aval[A](pa, s)),
                                   p)

def apply_updates(u: List[(Nat.nat, AExp.aexp[VName.vname])],
                   old: VName.vname => Option[Value.value]):
      Map[Nat.nat, Option[Value.value]] => Map[Nat.nat, Option[Value.value]]
  =
  ((a: Map[Nat.nat, Option[Value.value]]) =>
    Lista.fold[(Nat.nat, AExp.aexp[VName.vname]),
                Map[Nat.nat, Option[Value.value]]](((h:
               (Nat.nat, AExp.aexp[VName.vname]))
              =>
             (r: Map[Nat.nat, Option[Value.value]]) =>
             (r + (((h._1) -> (AExp.aval[VName.vname](h._2, old)))))),
            u, a))

def enumerate_ints(t: transition_ext[Unit]): Set.set[Int.int] =
  Set.sup_set[Int.int](Set.sup_set[Int.int](Set.sup_set[Int.int](Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[GExp.gexp[VName.vname],
                  Set.set[Int.int]](((a: GExp.gexp[VName.vname]) =>
                                      GExp.enumerate_gexp_ints[VName.vname](a)),
                                     Guards[Unit](t)))),
                          Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[AExp.aexp[VName.vname],
                   Set.set[Int.int]](((a: AExp.aexp[VName.vname]) =>
                                       AExp.enumerate_aexp_ints[VName.vname](a)),
                                      Outputs[Unit](t))))),
     Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[(Nat.nat,
                                       AExp.aexp[VName.vname]),
                                      Set.set[Int.int]](((a:
                    (Nat.nat, AExp.aexp[VName.vname]))
                   =>
                  {
                    val (_, aa): (Nat.nat, AExp.aexp[VName.vname]) = a;
                    AExp.enumerate_aexp_ints[VName.vname](aa)
                  }),
                 Updates[Unit](t))))),
                        Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[(Nat.nat,
                  AExp.aexp[VName.vname]),
                 Set.set[Int.int]](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
                                     {
                                       val
 (r, _): (Nat.nat, AExp.aexp[VName.vname]) = a;
                                       AExp.enumerate_aexp_ints[VName.vname](AExp.V[VName.vname](VName.R(r)))
                                     }),
                                    Updates[Unit](t)))))

def Label[A](x0: transition_ext[A]): String = x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => label
}

def Arity[A](x0: transition_ext[A]): Nat.nat = x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => arity
}

def same_structure(t1: transition_ext[Unit], t2: transition_ext[Unit]): Boolean
  =
  (Label[Unit](t1) ==
    Label[Unit](t2)) && ((Nat.equal_nata(Arity[Unit](t1),
  Arity[Unit](t2))) && (Nat.equal_nata(Nat.Nata((Outputs[Unit](t1)).par.length),
Nat.Nata((Outputs[Unit](t2)).par.length))))

def more[A](x0: transition_ext[A]): A = x0 match {
  case transition_exta(label, arity, guards, outputs, updates, more) => more
}

def identical_except_guard(t1: transition_ext[Unit], t2: transition_ext[Unit]):
      Boolean
  =
  (Label[Unit](t1) ==
    Label[Unit](t2)) && ((Nat.equal_nata(Arity[Unit](t2),
  Arity[Unit](t2))) && ((Lista.equal_lista[AExp.aexp[VName.vname]](Outputs[Unit](t1),
                            Outputs[Unit](t2))) && (Lista.equal_lista[(Nat.nat,
                                AExp.aexp[VName.vname])](Updates[Unit](t1),
                  Updates[Unit](t2)))))

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
  case ((x::xs), (y::ys)) =>
    (Orderings.less[A](x, y)) || ((HOL.eq[A](x,
      y)) && (less_eq_list[A](xs, ys)))
  case (Nil, xs) => true
  case ((x::xs), Nil) => false
}

def less_list[A : HOL.equal : Orderings.order](xs: List[A], x1: List[A]):
      Boolean
  =
  (xs, x1) match {
  case ((x::xs), (y::ys)) =>
    (Orderings.less[A](x, y)) || ((HOL.eq[A](x, y)) && (less_list[A](xs, ys)))
  case (Nil, (x::xs)) => true
  case (xs, Nil) => false
}

} /* object List_Lexorder */

object Value_Lexorder {

def less_value(x0: Value.value, x1: Value.value): Boolean = (x0, x1) match {
  case (Value.Inta(i), Value.Reala(f)) => true
  case (Value.Inta(i), Value.Str(s)) => true
  case (Value.Reala(f), Value.Inta(i)) => false
  case (Value.Reala(f), Value.Str(n)) => true
  case (Value.Str(s), Value.Inta(i)) => false
  case (Value.Str(s), Value.Reala(f)) => false
  case (Value.Str(s1), Value.Str(s2)) => s1 < s2
  case (Value.Reala(f1), Value.Reala(f2)) => Real.less_real(f1, f2)
  case (Value.Inta(i1), Value.Inta(i2)) => Int.less_int(i1, i2)
}

def less_eq_value(v1: Value.value, v2: Value.value): Boolean =
  (less_value(v1, v2)) || (Value.equal_valuea(v1, v2))

} /* object Value_Lexorder */

object AExp_Lexorder {

def less_aexp_aux[A : HOL.equal : Orderings.linorder](x0: AExp.aexp[A],
               x1: AExp.aexp[A]):
      Boolean
  =
  (x0, x1) match {
  case (AExp.L(l1), AExp.L(l2)) => Value_Lexorder.less_value(l1, l2)
  case (AExp.L(l1), AExp.V(v)) => true
  case (AExp.L(l1), AExp.Plus(v, va)) => true
  case (AExp.L(l1), AExp.Minus(v, va)) => true
  case (AExp.L(l1), AExp.Times(v, va)) => true
  case (AExp.L(l1), AExp.Divide(v, va)) => true
  case (AExp.V(v1), AExp.L(l1)) => false
  case (AExp.V(v1), AExp.V(v2)) => Orderings.less[A](v1, v2)
  case (AExp.V(v1), AExp.Plus(v, va)) => true
  case (AExp.V(v1), AExp.Minus(v, va)) => true
  case (AExp.V(v1), AExp.Times(v, va)) => true
  case (AExp.V(v1), AExp.Divide(v, va)) => true
  case (AExp.Plus(e1, e2), AExp.L(l2)) => false
  case (AExp.Plus(e1, e2), AExp.V(v2)) => false
  case (AExp.Plus(e1a, e2a), AExp.Plus(e1, e2)) =>
    (less_aexp_aux[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
                  e1)) && (less_aexp_aux[A](e2a, e2)))
  case (AExp.Plus(e1, e2), AExp.Minus(v, va)) => true
  case (AExp.Plus(e1, e2), AExp.Times(v, va)) => true
  case (AExp.Plus(e1, e2), AExp.Divide(v, va)) => true
  case (AExp.Minus(e1a, e2a), AExp.Minus(e1, e2)) =>
    (less_aexp_aux[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
                  e1)) && (less_aexp_aux[A](e2a, e2)))
  case (AExp.Minus(e1a, e2a), AExp.Times(e1, e2)) => true
  case (AExp.Minus(e1a, e2a), AExp.Divide(e1, e2)) => true
  case (AExp.Minus(e1, e2), AExp.L(v)) => false
  case (AExp.Minus(e1, e2), AExp.V(v)) => false
  case (AExp.Minus(e1, e2), AExp.Plus(v, va)) => false
  case (AExp.Times(e1a, e2a), AExp.Times(e1, e2)) =>
    (less_aexp_aux[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
                  e1)) && (less_aexp_aux[A](e2a, e2)))
  case (AExp.Times(e1a, e2a), AExp.Divide(e1, e2)) => true
  case (AExp.Times(e1, e2), AExp.L(v)) => false
  case (AExp.Times(e1, e2), AExp.V(v)) => false
  case (AExp.Times(e1, e2), AExp.Plus(v, va)) => false
  case (AExp.Times(e1, e2), AExp.Minus(v, va)) => false
  case (AExp.Divide(e1a, e2a), AExp.Divide(e1, e2)) =>
    (less_aexp_aux[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
                  e1)) && (less_aexp_aux[A](e2a, e2)))
  case (AExp.Divide(e1, e2), AExp.L(v)) => false
  case (AExp.Divide(e1, e2), AExp.V(v)) => false
  case (AExp.Divide(e1, e2), AExp.Plus(v, va)) => false
  case (AExp.Divide(e1, e2), AExp.Minus(v, va)) => false
  case (AExp.Divide(e1, e2), AExp.Times(v, va)) => false
}

def height[A](x0: AExp.aexp[A]): Nat.nat = x0 match {
  case AExp.L(l2) => Nat.Nata((1))
  case AExp.V(v2) => Nat.Nata((1))
  case AExp.Plus(e1, e2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A](e1), height[A](e2)))
  case AExp.Minus(e1, e2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A](e1), height[A](e2)))
  case AExp.Times(e1, e2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A](e1), height[A](e2)))
  case AExp.Divide(e1, e2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A](e1), height[A](e2)))
}

def less_aexp[A : HOL.equal : Orderings.linorder](a1: AExp.aexp[A],
           a2: AExp.aexp[A]):
      Boolean
  =
  {
    val h1: Nat.nat = height[A](a1)
    val h2: Nat.nat = height[A](a2);
    (if (Nat.equal_nata(h1, h2)) less_aexp_aux[A](a1, a2)
      else Nat.less_nat(h1, h2))
  }

def less_eq_aexp[A : HOL.equal : Orderings.linorder](e1: AExp.aexp[A],
              e2: AExp.aexp[A]):
      Boolean
  =
  (less_aexp[A](e1, e2)) || (AExp.equal_aexpa[A](e1, e2))

} /* object AExp_Lexorder */

object GExp_Lexorder {

def less_gexp_aux[A : HOL.equal : Orderings.linorder](x0: GExp.gexp[A],
               x1: GExp.gexp[A]):
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
    (AExp_Lexorder.less_aexp[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
                            e1)) && (AExp_Lexorder.less_aexp[A](e2a, e2)))
  case (GExp.Eq(e1, e2), GExp.Gt(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.In(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.Nor(v, va)) => true
  case (GExp.Gt(e1, e2), GExp.Bc(b2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Eq(e1, e2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Gt(e1, e2)) =>
    (AExp_Lexorder.less_aexp[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
                            e1)) && (AExp_Lexorder.less_aexp[A](e2a, e2)))
  case (GExp.Gt(e1, e2), GExp.In(v, va)) => true
  case (GExp.Gt(e1, e2), GExp.Nor(v, va)) => true
  case (GExp.In(vb, vc), GExp.Nor(v, va)) => true
  case (GExp.In(vb, vc), GExp.In(v, va)) =>
    (Orderings.less[A](vb, v)) || ((HOL.eq[A](vb,
       v)) && (List_Lexorder.less_list[Value.value](vc, va)))
  case (GExp.In(vb, vc), GExp.Bc(v)) => false
  case (GExp.In(vb, vc), GExp.Eq(v, va)) => false
  case (GExp.In(vb, vc), GExp.Gt(v, va)) => false
  case (GExp.Nor(g1a, g2a), GExp.Nor(g1, g2)) =>
    (less_gexp_aux[A](g1a, g1)) || ((GExp.equal_gexpa[A](g1a,
                  g1)) && (less_gexp_aux[A](g2a, g2)))
  case (GExp.Nor(g1, g2), GExp.Bc(v)) => false
  case (GExp.Nor(g1, g2), GExp.Eq(v, va)) => false
  case (GExp.Nor(g1, g2), GExp.Gt(v, va)) => false
  case (GExp.Nor(g1, g2), GExp.In(v, va)) => false
}

def height[A](x0: GExp.gexp[A]): Nat.nat = x0 match {
  case GExp.Bc(uu) => Nat.Nata((1))
  case GExp.Eq(a1, a2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](AExp_Lexorder.height[A](a1),
   AExp_Lexorder.height[A](a2)))
  case GExp.Gt(a1, a2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](AExp_Lexorder.height[A](a1),
   AExp_Lexorder.height[A](a2)))
  case GExp.In(v, l) =>
    Nat.plus_nata(Code_Numeral.nat_of_integer(BigInt(2)),
                   Nat.Nata(l.par.length))
  case GExp.Nor(g1, g2) =>
    Nat.plus_nata(Nat.Nata((1)),
                   Orderings.max[Nat.nat](height[A](g1), height[A](g2)))
}

def less_gexp[A : HOL.equal : Orderings.linorder](a1: GExp.gexp[A],
           a2: GExp.gexp[A]):
      Boolean
  =
  {
    val h1: Nat.nat = height[A](a1)
    val h2: Nat.nat = height[A](a2);
    (if (Nat.equal_nata(h1, h2)) less_gexp_aux[A](a1, a2)
      else Nat.less_nat(h1, h2))
  }

def less_eq_gexp[A : HOL.equal : Orderings.linorder](e1: GExp.gexp[A],
              e2: GExp.gexp[A]):
      Boolean
  =
  (less_gexp[A](e1, e2)) || (GExp.equal_gexpa[A](e1, e2))

} /* object GExp_Lexorder */

object Transition_Lexorder {

def less_transition_ext[A : Orderings.linorder](t1:
          Transition.transition_ext[A],
         t2: Transition.transition_ext[A]):
      Boolean
  =
  Product_Lexorder.less_prod[String,
                              (Nat.nat,
                                (List[GExp.gexp[VName.vname]],
                                  (List[AExp.aexp[VName.vname]],
                                    (List[(Nat.nat, AExp.aexp[VName.vname])],
                                      A))))]((Transition.Label[A](t1),
       (Transition.Arity[A](t1),
         (Transition.Guards[A](t1),
           (Transition.Outputs[A](t1),
             (Transition.Updates[A](t1), Transition.more[A](t1)))))),
      (Transition.Label[A](t2),
        (Transition.Arity[A](t2),
          (Transition.Guards[A](t2),
            (Transition.Outputs[A](t2),
              (Transition.Updates[A](t2), Transition.more[A](t2)))))))

def less_eq_transition_ext[A : HOL.equal : Orderings.linorder](t1:
                         Transition.transition_ext[A],
                        t2: Transition.transition_ext[A]):
      Boolean
  =
  (less_transition_ext[A](t1, t2)) || (Transition.equal_transition_exta[A](t1,
                                    t2))

} /* object Transition_Lexorder */

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
  case fset_of_list((x::Nil)) => x
}

def fMax[A : Orderings.linorder](x0: fset[A]): A = x0 match {
  case fset_of_list((h::t)) => t.par.fold(h)(Orderings.max)
}

def fMin[A : Orderings.linorder](x0: fset[A]): A = x0 match {
  case fset_of_list((h::t)) => t.par.fold(h)(Orderings.min)
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

object Subsumption {

def directly_subsumes(e1: FSet.fset[((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])],
                       e2: FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])],
                       s1: Nat.nat, s2: Nat.nat,
                       t1: Transition.transition_ext[Unit],
                       t2: Transition.transition_ext[Unit]):
      Boolean
  =
  (if (Transition.equal_transition_exta[Unit](t1, t2)) true
    else Dirties.scalaDirectlySubsumes(e1, e2, s1, s2, t1, t2))

} /* object Subsumption */

object Finite_Set {

def card[A](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.seta(xs) => Nat.Nata((xs.par.distinct.toList).par.length)
}

} /* object Finite_Set */

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

def fUnion[A](x0: FSet.fset[FSet.fset[A]]): FSet.fset[A] = x0 match {
  case FSet.fset_of_list(ls) =>
    Lista.foldr[FSet.fset[A],
                 FSet.fset[A]](((a: FSet.fset[A]) => (b: FSet.fset[A]) =>
                                 FSet.sup_fset[A](a, b)),
                                ls, FSet.bot_fset[A])
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

object Option_ord {

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

object Code_Generation {

def mutex[A : HOL.equal](uu: GExp.gexp[A], uv: GExp.gexp[A]): Boolean = (uu, uv)
  match {
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.Eq(AExp.V(v), AExp.L(l))) =>
    (if (HOL.eq[A](va, v)) ! (Value.equal_valuea(la, l)) else false)
  case (GExp.In(va, la), GExp.Eq(AExp.V(v), AExp.L(l))) =>
    (HOL.eq[A](va, v)) && (! (la.contains(l)))
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.In(v, l)) =>
    (HOL.eq[A](v, va)) && (! (l.contains(la)))
  case (GExp.In(va, la), GExp.In(v, l)) =>
    (HOL.eq[A](va, v)) && (Set.equal_set[Value.value](Set.inf_set[Value.value](Set.seta[Value.value](la),
Set.seta[Value.value](l)),
               Set.bot_set[Value.value]))
  case (GExp.Bc(v), uv) => false
  case (GExp.Eq(AExp.L(vb), va), uv) => false
  case (GExp.Eq(AExp.Plus(vb, vc), va), uv) => false
  case (GExp.Eq(AExp.Minus(vb, vc), va), uv) => false
  case (GExp.Eq(AExp.Times(vb, vc), va), uv) => false
  case (GExp.Eq(AExp.Divide(vb, vc), va), uv) => false
  case (GExp.Eq(v, AExp.V(vb)), uv) => false
  case (GExp.Eq(v, AExp.Plus(vb, vc)), uv) => false
  case (GExp.Eq(v, AExp.Minus(vb, vc)), uv) => false
  case (GExp.Eq(v, AExp.Times(vb, vc)), uv) => false
  case (GExp.Eq(v, AExp.Divide(vb, vc)), uv) => false
  case (GExp.Gt(v, va), uv) => false
  case (GExp.In(v, va), GExp.Bc(vb)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.L(vd), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Plus(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Minus(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Times(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Divide(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.V(vd))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Plus(vd, ve))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Minus(vd, ve))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Times(vd, ve))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Divide(vd, ve))) => false
  case (GExp.In(v, va), GExp.Gt(vb, vc)) => false
  case (GExp.In(v, va), GExp.Nor(vb, vc)) => false
  case (GExp.Nor(v, va), uv) => false
  case (uu, GExp.Bc(v)) => false
  case (uu, GExp.Eq(AExp.L(vb), va)) => false
  case (uu, GExp.Eq(AExp.Plus(vb, vc), va)) => false
  case (uu, GExp.Eq(AExp.Minus(vb, vc), va)) => false
  case (uu, GExp.Eq(AExp.Times(vb, vc), va)) => false
  case (uu, GExp.Eq(AExp.Divide(vb, vc), va)) => false
  case (uu, GExp.Eq(v, AExp.V(vb))) => false
  case (uu, GExp.Eq(v, AExp.Plus(vb, vc))) => false
  case (uu, GExp.Eq(v, AExp.Minus(vb, vc))) => false
  case (uu, GExp.Eq(v, AExp.Times(vb, vc))) => false
  case (uu, GExp.Eq(v, AExp.Divide(vb, vc))) => false
  case (uu, GExp.Gt(v, va)) => false
  case (uu, GExp.Nor(v, va)) => false
}

def choice_cases(t1: Transition.transition_ext[Unit],
                  t2: Transition.transition_ext[Unit]):
      Boolean
  =
  (if (Lista.list_ex[(GExp.gexp[VName.vname],
                       GExp.gexp[VName.vname])](((a:
            (GExp.gexp[VName.vname], GExp.gexp[VName.vname]))
           =>
          {
            val (aa, b): (GExp.gexp[VName.vname], GExp.gexp[VName.vname]) = a;
            mutex[VName.vname](aa, b)
          }),
         Lista.product[GExp.gexp[VName.vname],
                        GExp.gexp[VName.vname]](Transition.Guards[Unit](t1),
         Transition.Guards[Unit](t2))))
    false
    else (if (Lista.equal_lista[GExp.gexp[VName.vname]](Transition.Guards[Unit](t1),
                 Transition.Guards[Unit](t2)))
           Dirties.satisfiable(Lista.foldr[GExp.gexp[VName.vname],
    GExp.gexp[VName.vname]](((a: GExp.gexp[VName.vname]) =>
                              (b: GExp.gexp[VName.vname]) =>
                              GExp.gAnd[VName.vname](a, b)),
                             Transition.Guards[Unit](t1),
                             GExp.Bc[VName.vname](true)))
           else Dirties.satisfiable(Lista.foldr[GExp.gexp[VName.vname],
         GExp.gexp[VName.vname]](((a: GExp.gexp[VName.vname]) =>
                                   (b: GExp.gexp[VName.vname]) =>
                                   GExp.gAnd[VName.vname](a, b)),
                                  Transition.Guards[Unit](t1) ++
                                    Transition.Guards[Unit](t2),
                                  GExp.Bc[VName.vname](true)))))

def infer_with_log(failedMerges: Set.set[(Nat.nat, Nat.nat)], k: Nat.nat,
                    e: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                    r: (List[Nat.nat]) =>
                         (List[Nat.nat]) =>
                           (FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                             Nat.nat,
                    m: (List[Nat.nat]) =>
                         (List[Nat.nat]) =>
                           Nat.nat =>
                             (FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                               (FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 (FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                   ((FSet.fset[((Nat.nat, Nat.nat),
         Transition.transition_ext[Unit])]) =>
                                     Boolean) =>
                                     Option[FSet.fset[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                    check:
                      (FSet.fset[((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])]) =>
                        Boolean,
                    np: (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], List[Nat.nat]),
  (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val scores: FSet.fset[Inference.score_ext[Unit]] =
      (if (Nat.equal_nata(k, Nat.Nata((1)))) Inference.score_1(e, r)
        else Inference.k_score(k, e, r));
    (Inference.inference_step(failedMerges, e,
                               FSet.ffilter[Inference.score_ext[Unit]](((s:
                                   Inference.score_ext[Unit])
                                  =>
                                 (! (Set.member[(Nat.nat,
          Nat.nat)]((Inference.S1[Unit](s), Inference.S2[Unit](s)),
                     failedMerges))) && (! (Set.member[(Nat.nat,
                 Nat.nat)]((Inference.S2[Unit](s), Inference.S1[Unit](s)),
                            failedMerges)))),
                                scores),
                               m, check, np)
       match {
       case (None, _) => e
       case (Some(newa), x) =>
         (if (FSet.less_fset[Nat.nat](Inference.S(newa), Inference.S(e)))
           {
             Log.logStates(newa, (FSet.size_fset[Nat.nat](Inference.S(e))));
             infer_with_log(x, k, newa, r, m, check, np)
           }
           else e)
     })
  }

def guardMatch_code(uu: List[GExp.gexp[VName.vname]],
                     uv: List[GExp.gexp[VName.vname]]):
      Boolean
  =
  (uu, uv) match {
  case (((GExp.Eq(AExp.V(VName.I(ia)), AExp.L(Value.Inta(na))))::Nil),
         ((GExp.Eq(AExp.V(VName.I(i)), AExp.L(Value.Inta(n))))::Nil))
    => (Nat.equal_nata(ia, Nat.zero_nata)) && (Nat.equal_nata(i, Nat.zero_nata))
  case (Nil, uv) => false
  case (((GExp.Bc(vb))::va), uv) => false
  case (((GExp.Eq(AExp.L(vd), vc))::va), uv) => false
  case (((GExp.Eq(AExp.V(VName.R(ve)), vc))::va), uv) => false
  case (((GExp.Eq(AExp.Plus(vd, ve), vc))::va), uv) => false
  case (((GExp.Eq(AExp.Minus(vd, ve), vc))::va), uv) => false
  case (((GExp.Eq(AExp.Times(vd, ve), vc))::va), uv) => false
  case (((GExp.Eq(AExp.Divide(vd, ve), vc))::va), uv) => false
  case (((GExp.Eq(vb, AExp.L(Value.Reala(ve))))::va), uv) => false
  case (((GExp.Eq(vb, AExp.L(Value.Str(ve))))::va), uv) => false
  case (((GExp.Eq(vb, AExp.V(vd)))::va), uv) => false
  case (((GExp.Eq(vb, AExp.Plus(vd, ve)))::va), uv) => false
  case (((GExp.Eq(vb, AExp.Minus(vd, ve)))::va), uv) => false
  case (((GExp.Eq(vb, AExp.Times(vd, ve)))::va), uv) => false
  case (((GExp.Eq(vb, AExp.Divide(vd, ve)))::va), uv) => false
  case (((GExp.Gt(vb, vc))::va), uv) => false
  case (((GExp.In(vb, vc))::va), uv) => false
  case (((GExp.Nor(vb, vc))::va), uv) => false
  case ((v::((vb::vc))), uv) => false
  case (uu, Nil) => false
  case (uu, ((GExp.Bc(vb))::va)) => false
  case (uu, ((GExp.Eq(AExp.L(vd), vc))::va)) => false
  case (uu, ((GExp.Eq(AExp.V(VName.R(ve)), vc))::va)) => false
  case (uu, ((GExp.Eq(AExp.Plus(vd, ve), vc))::va)) => false
  case (uu, ((GExp.Eq(AExp.Minus(vd, ve), vc))::va)) => false
  case (uu, ((GExp.Eq(AExp.Times(vd, ve), vc))::va)) => false
  case (uu, ((GExp.Eq(AExp.Divide(vd, ve), vc))::va)) => false
  case (uu, ((GExp.Eq(vb, AExp.L(Value.Reala(ve))))::va)) => false
  case (uu, ((GExp.Eq(vb, AExp.L(Value.Str(ve))))::va)) => false
  case (uu, ((GExp.Eq(vb, AExp.V(vd)))::va)) => false
  case (uu, ((GExp.Eq(vb, AExp.Plus(vd, ve)))::va)) => false
  case (uu, ((GExp.Eq(vb, AExp.Minus(vd, ve)))::va)) => false
  case (uu, ((GExp.Eq(vb, AExp.Times(vd, ve)))::va)) => false
  case (uu, ((GExp.Eq(vb, AExp.Divide(vd, ve)))::va)) => false
  case (uu, ((GExp.Gt(vb, vc))::va)) => false
  case (uu, ((GExp.In(vb, vc))::va)) => false
  case (uu, ((GExp.Nor(vb, vc))::va)) => false
  case (uu, (v::((vb::vc)))) => false
}

def outputMatch_code(uu: List[AExp.aexp[VName.vname]],
                      uv: List[AExp.aexp[VName.vname]]):
      Boolean
  =
  (uu, uv) match {
  case (((AExp.L(Value.Inta(na)))::Nil), ((AExp.L(Value.Inta(n)))::Nil)) => true
  case (Nil, uv) => false
  case (((AExp.L(Value.Reala(vc)))::va), uv) => false
  case (((AExp.L(Value.Str(vc)))::va), uv) => false
  case (((AExp.V(vb))::va), uv) => false
  case (((AExp.Plus(vb, vc))::va), uv) => false
  case (((AExp.Minus(vb, vc))::va), uv) => false
  case (((AExp.Times(vb, vc))::va), uv) => false
  case (((AExp.Divide(vb, vc))::va), uv) => false
  case ((v::((vb::vc))), uv) => false
  case (uu, Nil) => false
  case (uu, ((AExp.L(Value.Reala(vc)))::va)) => false
  case (uu, ((AExp.L(Value.Str(vc)))::va)) => false
  case (uu, ((AExp.V(vb))::va)) => false
  case (uu, ((AExp.Plus(vb, vc))::va)) => false
  case (uu, ((AExp.Minus(vb, vc))::va)) => false
  case (uu, ((AExp.Times(vb, vc))::va)) => false
  case (uu, ((AExp.Divide(vb, vc))::va)) => false
  case (uu, (v::((vb::vc)))) => false
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

def S(m: FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[Nat.nat]
  =
  FSet.sup_fset[Nat.nat](FSet.fimage[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit])),
                                      Nat.nat](((a:
           (List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
          =>
         {
           val (_, aa):
                 (List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
             = a
           val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
             aa;
           ({
              val (s, _): (Nat.nat, Nat.nat) = ab;
              ((_: Transition.transition_ext[Unit]) => s)
            })(b)
         }),
        m),
                          FSet.fimage[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                                       Nat.nat](((a:
            (List[Nat.nat],
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
           =>
          {
            val (_, aa):
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
              = a
            val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
              aa;
            ({
               val (_, s): (Nat.nat, Nat.nat) = ab;
               ((_: Transition.transition_ext[Unit]) => s)
             })(b)
          }),
         m))

def tm(e: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               ((Nat.nat, Nat.nat),
                 Transition.transition_ext[Unit])](((a:
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
              =>
             a._2),
            e)

def lob(t1: Transition.transition_ext[Unit],
         t2: Transition.transition_ext[Unit]):
      Transition.transition_ext[Unit]
  =
  Transition.Guards_update[Unit](((_: List[GExp.gexp[VName.vname]]) =>
                                   ((GExp.gOr[VName.vname](Lista.fold[GExp.gexp[VName.vname],
                               GExp.gexp[VName.vname]](((a:
                   GExp.gexp[VName.vname])
                  =>
                 (b: GExp.gexp[VName.vname]) => GExp.gAnd[VName.vname](a, b)),
                Transition.Guards[Unit](t1), GExp.Bc[VName.vname](true)),
                    Lista.fold[GExp.gexp[VName.vname],
                                GExp.gexp[VName.vname]](((a:
                    GExp.gexp[VName.vname])
                   =>
                  (b: GExp.gexp[VName.vname]) => GExp.gAnd[VName.vname](a, b)),
                 Transition.Guards[Unit](t2),
                 GExp.Bc[VName.vname](true))))::Nil)),
                                  t1)

def out(g: FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
         v: Nat.nat):
      FSet.fset[Nat.nat]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               Nat.nat](((a: (List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])))
                           =>
                          {
                            val (_, aa):
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))
                              = a
                            val (ab, b):
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])
                              = aa;
                            ({
                               val (_, to): (Nat.nat, Nat.nat) = ab;
                               ((_: Transition.transition_ext[Unit]) => to)
                             })(b)
                          }),
                         FSet.ffilter[(List[Nat.nat],
((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit]))](((a:
 (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
=>
                                       {
 val (_, aa):
       (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
   = a
 val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = aa;
 ({
    val (from, _): (Nat.nat, Nat.nat) = ab;
    ((_: Transition.transition_ext[Unit]) => Nat.equal_nata(from, v))
  })(b)
                                       }),
                                      g))

def dest(uid: List[Nat.nat],
          t: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  (((FSet.fthe_elem[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))](FSet.ffilter[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))](((x:
                                   (List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])))
                                  =>
                                 Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                           Set.seta[Nat.nat](x._1))),
                                t)))._2)._1)._2

def learn(n: Nat.nat,
           pta: FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))],
           l: List[List[(String, (List[Value.value], List[Value.value]))]],
           r: (List[Nat.nat]) =>
                (List[Nat.nat]) =>
                  (FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]) =>
                    Nat.nat,
           m: (List[Nat.nat]) =>
                (List[Nat.nat]) =>
                  Nat.nat =>
                    (FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          ((FSet.fset[((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])]) =>
                            Boolean) =>
                            Option[FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
           np: (FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]) =>
                 FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit],
                                  List[Nat.nat]),
                                 (Transition.transition_ext[Unit],
                                   List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val check:
          (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
            Boolean
      = ((a: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])])
           =>
          EFSM.accepts_log(Set.seta[List[(String,
   (List[Value.value], List[Value.value]))]](l),
                            a));
    Code_Generation.infer_with_log(Set.bot_set[(Nat.nat, Nat.nat)], n, pta, r,
                                    m, check, np)
  }

def bool2nat(x0: Boolean): Nat.nat = x0 match {
  case true => Nat.Nata((1))
  case false => Nat.zero_nata
}

def score_transitions(t1: Transition.transition_ext[Unit],
                       t2: Transition.transition_ext[Unit]):
      Nat.nat
  =
  (if ((Transition.Label[Unit](t1) ==
         Transition.Label[Unit](t2)) && ((Nat.equal_nata(Transition.Arity[Unit](t1),
                  Transition.Arity[Unit](t2))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).par.length),
                           Nat.Nata((Transition.Outputs[Unit](t2)).par.length)))))
    Nat.plus_nata(Nat.plus_nata(Nat.plus_nata(Nat.plus_nata(Nat.Nata((1)),
                     bool2nat(Transition.equal_transition_exta[Unit](t1, t2))),
       Finite_Set.card[GExp.gexp[VName.vname]](Set.inf_set[GExp.gexp[VName.vname]](Set.seta[GExp.gexp[VName.vname]](Transition.Guards[Unit](t2)),
    Set.seta[GExp.gexp[VName.vname]](Transition.Guards[Unit](t2))))),
                                 Finite_Set.card[(Nat.nat,
           AExp.aexp[VName.vname])](Set.inf_set[(Nat.nat,
          AExp.aexp[VName.vname])](Set.seta[(Nat.nat,
      AExp.aexp[VName.vname])](Transition.Updates[Unit](t2)),
                                    Set.seta[(Nat.nat,
       AExp.aexp[VName.vname])](Transition.Updates[Unit](t2))))),
                   Finite_Set.card[AExp.aexp[VName.vname]](Set.inf_set[AExp.aexp[VName.vname]](Set.seta[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t2)),
                Set.seta[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t2)))))
    else Nat.zero_nata)

def order_nondeterministic_pairs(s: FSet.fset[(Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], List[Nat.nat]),
            (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      List[(Nat.nat,
             ((Nat.nat, Nat.nat),
               ((Transition.transition_ext[Unit], List[Nat.nat]),
                 (Transition.transition_ext[Unit], List[Nat.nat]))))]
  =
  Lista.map[(Nat.nat,
              (Nat.nat,
                ((Nat.nat, Nat.nat),
                  ((Transition.transition_ext[Unit], List[Nat.nat]),
                    (Transition.transition_ext[Unit], List[Nat.nat]))))),
             (Nat.nat,
               ((Nat.nat, Nat.nat),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (Transition.transition_ext[Unit],
                     List[Nat.nat]))))](((a:
    (Nat.nat,
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], List[Nat.nat]),
            (Transition.transition_ext[Unit], List[Nat.nat]))))))
   =>
  a._2),
 FSet.sorted_list_of_fset[(Nat.nat,
                            (Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit],
                                   List[Nat.nat]),
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat])))))](FSet.fimage[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit],
                                   List[Nat.nat]),
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat])))),
                             (Nat.nat,
                               (Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   ((Transition.transition_ext[Unit],
                                      List[Nat.nat]),
                                     (Transition.transition_ext[Unit],
                                       List[Nat.nat])))))](((sa:
                       (Nat.nat,
                         ((Nat.nat, Nat.nat),
                           ((Transition.transition_ext[Unit], List[Nat.nat]),
                             (Transition.transition_ext[Unit],
                               List[Nat.nat])))))
                      =>
                     {
                       val a: (Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  ((Transition.transition_ext[Unit],
                                     List[Nat.nat]),
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat]))))
                         = sa
                       val (_, aa):
                             (Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 ((Transition.transition_ext[Unit],
                                    List[Nat.nat]),
                                   (Transition.transition_ext[Unit],
                                     List[Nat.nat]))))
                         = a
                       val (_, ab):
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit],
                                  List[Nat.nat]),
                                 (Transition.transition_ext[Unit],
                                   List[Nat.nat])))
                         = aa
                       val (ac, b):
                             ((Transition.transition_ext[Unit], List[Nat.nat]),
                               (Transition.transition_ext[Unit], List[Nat.nat]))
                         = ab;
                       ({
                          val (t1, _):
                                (Transition.transition_ext[Unit], List[Nat.nat])
                            = ac;
                          ((ad: (Transition.transition_ext[Unit],
                                  List[Nat.nat]))
                             =>
                            {
                              val (t2, _):
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat])
                                = ad;
                              (score_transitions(t1, t2), sa)
                            })
                        })(b)
                     }),
                    s)))

def insert_transition(uid: List[Nat.nat], from: Nat.nat, to: Nat.nat,
                       t: Transition.transition_ext[Unit],
                       e: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (if (FSet.fBall[(List[Nat.nat],
                    ((Nat.nat, Nat.nat),
                      Transition.transition_ext[Unit]))](e,
                  ((a: (List[Nat.nat],
                         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                     =>
                    {
                      val (_, aa):
                            (List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))
                        = a
                      val (ab, b):
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])
                        = aa;
                      ({
                         val (froma, toa): (Nat.nat, Nat.nat) = ab;
                         ((ta: Transition.transition_ext[Unit]) =>
                           ! ((Nat.equal_nata(from,
       froma)) && ((Nat.equal_nata(to, toa)) && (Transition.identical_except_guard(t,
    ta)))))
                       })(b)
                    })))
    FSet.finsert[(List[Nat.nat],
                   ((Nat.nat, Nat.nat),
                     Transition.transition_ext[Unit]))]((uid, ((from, to), t)),
                 e)
    else FSet.fimage[(List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                      (List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))](((a:
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])))
                        =>
                       {
                         val (uida, aa):
                               (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))
                           = a
                         val (ab, b):
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])
                           = aa;
                         ({
                            val (froma, toa): (Nat.nat, Nat.nat) = ab;
                            ((ta: Transition.transition_ext[Unit]) =>
                              (if ((Nat.equal_nata(from,
            froma)) && ((Nat.equal_nata(to,
 toa)) && (Transition.identical_except_guard(t, ta))))
                                (Lista.union[Nat.nat].apply(uida).apply(uid),
                                  ((froma, toa), lob(ta, t)))
                                else (uida, ((froma, toa), ta))))
                          })(b)
                       }),
                      e))

def make_distinct(e: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet_Utils.ffold_ord[(List[Nat.nat],
                         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                        FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]](((a:
                                      (List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                                     =>
                                    {
                                      val
(uid, aa):
  (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
= a
                                      val
(ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = aa;
                                      ({
 val (ac, ba): (Nat.nat, Nat.nat) = ab;
 ((c: Transition.transition_ext[Unit]) =>
   (d: FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
     =>
   insert_transition(uid, ac, ba, c, d))
                                       })(b)
                                    }),
                                   e, FSet.bot_fset[(List[Nat.nat],
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])

def merge_transitions_aux(e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                           oldID: List[Nat.nat], newID: List[Nat.nat]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val a: (List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
      = FSet.fthe_elem[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))](FSet.ffilter[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))](((a:
                                      (List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                                     =>
                                    {
                                      val
(uids, _):
  (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
= a;
                                      Lista.equal_lista[Nat.nat](oldID, uids)
                                    }),
                                   e))
    val (uids1, aa):
          (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
      = a
    val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = aa;
    ({
       val (_, _): (Nat.nat, Nat.nat) = ab;
       ((old: Transition.transition_ext[Unit]) =>
         {
           val ac: (List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
             = FSet.fthe_elem[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))](FSet.ffilter[(List[Nat.nat],
    ((Nat.nat, Nat.nat),
      Transition.transition_ext[Unit]))](((ac:
     (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
    =>
   {
     val (uids, _):
           (List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
       = ac;
     Lista.equal_lista[Nat.nat](newID, uids)
   }),
  e))
           val (uids2, ad):
                 (List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
             = ac
           val (ae, ba): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
             ad;
           ({
              val (origin, dest): (Nat.nat, Nat.nat) = ae;
              ((newa: Transition.transition_ext[Unit]) =>
                make_distinct(FSet.finsert[(List[Nat.nat],
     ((Nat.nat, Nat.nat),
       Transition.transition_ext[Unit]))]((Lista.union[Nat.nat].apply(uids1).apply(uids2),
    ((origin, dest), newa)),
   FSet.minus_fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit]))](e,
                   FSet.finsert[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]((uids1,
                                 ((origin, dest), old)),
                                FSet.finsert[(List[Nat.nat],
       ((Nat.nat, Nat.nat),
         Transition.transition_ext[Unit]))]((uids2, ((origin, dest), newa)),
     FSet.bot_fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit]))]))))))
            })(ba)
         })
     })(b)
  }

def origin(uid: List[Nat.nat],
            t: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  (((FSet.fthe_elem[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))](FSet.ffilter[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))](((x:
                                   (List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])))
                                  =>
                                 Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                           Set.seta[Nat.nat](x._1))),
                                t)))._2)._1)._1

def merge_transitions(failedMerges: Set.set[(Nat.nat, Nat.nat)],
                       oldEFSM:
                         FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       preDestMerge:
                         FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       destMerge:
                         FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       t1: Transition.transition_ext[Unit], u1: List[Nat.nat],
                       t2: Transition.transition_ext[Unit], u2: List[Nat.nat],
                       modifier:
                         (List[Nat.nat]) =>
                           (List[Nat.nat]) =>
                             Nat.nat =>
                               (FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 (FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                   (FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                     ((FSet.fset[((Nat.nat, Nat.nat),
           Transition.transition_ext[Unit])]) =>
                                       Boolean) =>
                                       Option[FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                       check:
                         (FSet.fset[((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])]) =>
                           Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (Lista.list_all[Nat.nat](((id: Nat.nat) =>
                                 Subsumption.directly_subsumes(tm(oldEFSM),
                        tm(destMerge), origin((id::Nil), oldEFSM),
                        origin(u1, destMerge), t2, t1)),
                                u1))
    Some[FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit]))]](merge_transitions_aux(destMerge,
  u1, u2))
    else (if (Lista.list_all[Nat.nat](((id: Nat.nat) =>
Subsumption.directly_subsumes(tm(oldEFSM), tm(destMerge),
                               origin((id::Nil), oldEFSM),
                               origin(u2, destMerge), t1, t2)),
                                       u2))
           Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](merge_transitions_aux(destMerge,
         u2, u1))
           else (((((((modifier(u1))(u2))(origin(u1,
          destMerge)))(destMerge))(preDestMerge))(oldEFSM))(check)
                   match {
                   case None => None
                   case Some(e) =>
                     Some[FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]](make_distinct(e))
                 })))

def deterministic(t: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                   np: (FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
                         FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       ((Transition.transition_ext[Unit],
  List[Nat.nat]),
 (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      Boolean
  =
  FSet.equal_fseta[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       ((Transition.transition_ext[Unit], List[Nat.nat]),
                         (Transition.transition_ext[Unit],
                           List[Nat.nat]))))](np(t),
       FSet.bot_fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], List[Nat.nat]),
                           (Transition.transition_ext[Unit], List[Nat.nat]))))])

def merge_states_aux(s1: Nat.nat, s2: Nat.nat,
                      e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, aa):
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a
                  val (ab, b):
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                    = aa;
                  ({
                     val (origin, dest): (Nat.nat, Nat.nat) = ab;
                     ((t: Transition.transition_ext[Unit]) =>
                       (uid, (((if (Nat.equal_nata(origin, s1)) s2 else origin),
                                (if (Nat.equal_nata(dest, s1)) s2 else dest)),
                               t)))
                   })(b)
                }),
               e)

def merge_states(x: Nat.nat, y: Nat.nat,
                  t: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (if (Nat.equal_nata(x, y)) t
    else (if (Nat.less_nat(y, x)) merge_states_aux(x, y, t)
           else merge_states_aux(y, x, t)))

def resolve_nondeterminism(failedMerges: Set.set[(Nat.nat, Nat.nat)],
                            x1: List[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 ((Transition.transition_ext[Unit], List[Nat.nat]),
   (Transition.transition_ext[Unit], List[Nat.nat]))))],
                            uu: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            newEFSM:
                              FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            uv: (List[Nat.nat]) =>
                                  (List[Nat.nat]) =>
                                    Nat.nat =>
                                      (FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
(FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
  (FSet.fset[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
    ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
      Boolean) =>
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]],
                            check:
                              (FSet.fset[((Nat.nat, Nat.nat),
   Transition.transition_ext[Unit])]) =>
                                Boolean,
                            np: (FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                  FSet.fset[(Nat.nat,
      ((Nat.nat, Nat.nat),
        ((Transition.transition_ext[Unit], List[Nat.nat]),
          (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      (Option[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]],
        Set.set[(Nat.nat, Nat.nat)])
  =
  (failedMerges, x1, uu, newEFSM, uv, check, np) match {
  case (failedMerges, Nil, uu, newEFSM, uv, check, np) =>
    ((if ((deterministic(newEFSM, np)) && (check(tm(newEFSM))))
       Some[FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))]](newEFSM)
       else None),
      failedMerges)
  case (failedMerges, ((from, ((dest1, dest2), ((t1, u1), (t2, u2))))::ss),
         oldEFSM, newEFSM, m, check, np)
    => (if ((Set.member[(Nat.nat,
                          Nat.nat)]((dest1, dest2),
                                     failedMerges)) || (Set.member[(Nat.nat,
                             Nat.nat)]((dest2, dest1), failedMerges)))
         (None, failedMerges)
         else {
                val destMerge:
                      FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]
                  = merge_states(dest1, dest2, newEFSM);
                (merge_transitions(failedMerges, oldEFSM, newEFSM, destMerge,
                                    t1, u1, t2, u2, m, check)
                   match {
                   case None =>
                     resolve_nondeterminism(Set.insert[(Nat.nat,
                 Nat.nat)]((dest1, dest2), failedMerges),
     ss, oldEFSM, newEFSM, m, check, np)
                   case Some(newa) =>
                     {
                       val newScores:
                             List[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      ((Transition.transition_ext[Unit],
 List[Nat.nat]),
(Transition.transition_ext[Unit], List[Nat.nat]))))]
                         = order_nondeterministic_pairs(np(newa));
                       (if (Product_Lexorder.less_prod[Nat.nat,
                (Nat.nat,
                  Nat.nat)]((FSet.size_fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](newa),
                              (FSet.size_fset[Nat.nat](S(newa)),
                                Nat.Nata(newScores.par.length))),
                             (FSet.size_fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](newEFSM),
                               (FSet.size_fset[Nat.nat](S(newEFSM)),
                                 Nat.Nata(ss.par.length)))))
                         (resolve_nondeterminism(failedMerges, newScores,
          oldEFSM, newa, m, check, np)
                            match {
                            case (None, failedMergesa) =>
                              resolve_nondeterminism(Set.insert[(Nat.nat,
                          Nat.nat)]((dest1, dest2), failedMergesa),
              ss, oldEFSM, newEFSM, m, check, np)
                            case (Some(newb), failedMergesa) =>
                              (Some[FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]](newb),
                                failedMergesa)
                          })
                         else (None, failedMerges))
                     }
                 })
              })
}

def merge(failedMerges: Set.set[(Nat.nat, Nat.nat)],
           e: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
           s1: Nat.nat, s2: Nat.nat,
           m: (List[Nat.nat]) =>
                (List[Nat.nat]) =>
                  Nat.nat =>
                    (FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          ((FSet.fset[((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])]) =>
                            Boolean) =>
                            Option[FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
           check:
             (FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit])]) =>
               Boolean,
           np: (FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]) =>
                 FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit],
                                  List[Nat.nat]),
                                 (Transition.transition_ext[Unit],
                                   List[Nat.nat]))))]):
      (Option[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]],
        Set.set[(Nat.nat, Nat.nat)])
  =
  (if ((Nat.equal_nata(s1, s2)) || ((Set.member[(Nat.nat,
          Nat.nat)]((s1, s2),
                     failedMerges)) || (Set.member[(Nat.nat,
             Nat.nat)]((s2, s1), failedMerges))))
    (None, failedMerges)
    else {
           val ea: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]
             = make_distinct(merge_states(s1, s2, e));
           resolve_nondeterminism(failedMerges,
                                   order_nondeterministic_pairs(np(ea)), e, ea,
                                   m, check, np)
         })

def nodes(g: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]):
      FSet.fset[Nat.nat]
  =
  FSet.sup_fset[Nat.nat](FSet.fimage[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit])),
                                      Nat.nat](((a:
           (List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
          =>
         {
           val (_, aa):
                 (List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
             = a
           val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
             aa;
           ({
              val (from, _): (Nat.nat, Nat.nat) = ab;
              ((_: Transition.transition_ext[Unit]) => from)
            })(b)
         }),
        g),
                          FSet.fimage[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                                       Nat.nat](((a:
            (List[Nat.nat],
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
           =>
          {
            val (_, aa):
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
              = a
            val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
              aa;
            ({
               val (_, to): (Nat.nat, Nat.nat) = ab;
               ((_: Transition.transition_ext[Unit]) => to)
             })(b)
          }),
         g))

def step_score(xs: List[(List[Nat.nat], List[Nat.nat])],
                e: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                s: (List[Nat.nat]) =>
                     (List[Nat.nat]) =>
                       (FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
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

def score_from_list(p1: FSet.fset[List[List[Nat.nat]]],
                     p2: FSet.fset[List[List[Nat.nat]]],
                     e: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                     s: (List[Nat.nat]) =>
                          (List[Nat.nat]) =>
                            (FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
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
                              step_score(l, e, s)),
                             pairs);
    FSet_Utils.fSum[Nat.nat](a)
  }

def outgoing_transitions(s: Nat.nat,
                          e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (Nat.nat,
                 (Transition.transition_ext[Unit],
                   List[Nat.nat]))](((a:
(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                                       =>
                                      {
val (uid, aa):
      (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
  = a
val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = aa;
({
   val (_, to): (Nat.nat, Nat.nat) = ab;
   ((t: Transition.transition_ext[Unit]) => (to, (t, uid)))
 })(b)
                                      }),
                                     FSet.ffilter[(List[Nat.nat],
            ((Nat.nat, Nat.nat),
              Transition.transition_ext[Unit]))](((a:
             (List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
            =>
           {
             val (_, aa):
                   (List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
               = a
             val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
               = aa;
             ({
                val (origin, _): (Nat.nat, Nat.nat) = ab;
                ((_: Transition.transition_ext[Unit]) =>
                  Nat.equal_nata(origin, s))
              })(b)
           }),
          e))

def paths_of_length(m: Nat.nat,
                     uu: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                     uv: Nat.nat):
      FSet.fset[List[List[Nat.nat]]]
  =
  (if (Nat.equal_nata(m, Nat.zero_nata))
    FSet.finsert[List[List[Nat.nat]]](Nil, FSet.bot_fset[List[List[Nat.nat]]])
    else {
           val outgoing:
                 FSet.fset[(Nat.nat,
                             (Transition.transition_ext[Unit], List[Nat.nat]))]
             = outgoing_transitions(uv, uu)
           val a: FSet.fset[List[List[Nat.nat]]] =
             FSet.ffUnion[List[List[Nat.nat]]](FSet.fimage[(Nat.nat,
                     (Transition.transition_ext[Unit], List[Nat.nat])),
                    FSet.fset[List[List[Nat.nat]]]](((a:
                (Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])))
               =>
              {
                val (d, (_, id)):
                      (Nat.nat,
                        (Transition.transition_ext[Unit], List[Nat.nat]))
                  = a;
                FSet.fimage[List[List[Nat.nat]],
                             List[List[Nat.nat]]](((aa: List[List[Nat.nat]]) =>
            (id::aa)),
           paths_of_length(Nat.minus_nat(m, Nat.Nata((1))), uu, d))
              }),
             outgoing));
           FSet.ffilter[List[List[Nat.nat]]](((l: List[List[Nat.nat]]) =>
       Nat.equal_nata(Nat.Nata(l.par.length),
                       Nat.Suc(Nat.minus_nat(m, Nat.Nata((1)))))),
      a)
         })

def finfun_to_pairs[A : HOL.equal : Orderings.linorder, B](f: Map[A, B]):
      List[(A, B)]
  =
  Lista.map[A, (A, B)](((k: A) => (k, f(k))), f.keySet.toList)

def scoreboard_add(a: FSet.fset[score_ext[Unit]],
                    b: FSet.fset[score_ext[Unit]]):
      FSet.fset[score_ext[Unit]]
  =
  FSet.fset_of_list[score_ext[Unit]](Lista.map[((Nat.nat, Nat.nat), Nat.nat),
        score_ext[Unit]](((aa: ((Nat.nat, Nat.nat), Nat.nat)) =>
                           {
                             val (ab, ba): ((Nat.nat, Nat.nat), Nat.nat) = aa;
                             ({
                                val (s1, s2): (Nat.nat, Nat.nat) = ab;
                                ((l: Nat.nat) =>
                                  score_exta[Unit](l, s1, s2, ()))
                              })(ba)
                           }),
                          finfun_to_pairs[(Nat.nat, Nat.nat),
   Nat.nat](Lista.fold[score_ext[Unit],
                        Map[((Nat.nat,
                              Nat.nat)), Nat.nat]](((s: score_ext[Unit]) =>
             (scores: Map[((Nat.nat, Nat.nat)), Nat.nat]) =>
             (scores + (((S1[Unit](s),
                           S2[Unit](s)) -> (Nat.plus_nata(scores((S1[Unit](s),
                           S2[Unit](s))),
                   Score[Unit](s))))))),
            FSet.sorted_list_of_fset[score_ext[Unit]](a) ++
              FSet.sorted_list_of_fset[score_ext[Unit]](b),
            scala.collection.immutable.Map().withDefaultValue(Nat.zero_nata)))))

def bonus_score(e: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]):
      FSet.fset[score_ext[Unit]]
  =
  {
    val states: FSet.fset[Nat.nat] = S(e);
    FSet.ffilter[(Nat.nat,
                   Nat.nat)](((a: (Nat.nat, Nat.nat)) =>
                               {
                                 val (aa, b): (Nat.nat, Nat.nat) = a;
                                 Nat.less_nat(aa, b)
                               }),
                              FSet_Utils.fprod[Nat.nat,
        Nat.nat](states, states))
    val state_transitions:
          FSet.fset[(Nat.nat,
                      FSet.fset[(Nat.nat,
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat]))])]
      = FSet.fimage[Nat.nat,
                     (Nat.nat,
                       FSet.fset[(Nat.nat,
                                   (Transition.transition_ext[Unit],
                                     List[Nat.nat]))])](((s: Nat.nat) =>
                  (s, outgoing_transitions(s, e))),
                 states)
    val state_pairs:
          FSet.fset[(Nat.nat,
                      FSet.fset[((Nat.nat,
                                   (Transition.transition_ext[Unit],
                                     List[Nat.nat])),
                                  (Nat.nat,
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat])))])]
      = FSet.fimage[(Nat.nat,
                      FSet.fset[(Nat.nat,
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat]))]),
                     (Nat.nat,
                       FSet.fset[((Nat.nat,
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat])),
                                   (Nat.nat,
                                     (Transition.transition_ext[Unit],
                                       List[Nat.nat])))])](((a:
                       (Nat.nat,
                         FSet.fset[(Nat.nat,
                                     (Transition.transition_ext[Unit],
                                       List[Nat.nat]))]))
                      =>
                     {
                       val (s, ts):
                             (Nat.nat,
                               FSet.fset[(Nat.nat,
   (Transition.transition_ext[Unit], List[Nat.nat]))])
                         = a;
                       (s, FSet_Utils.fprod[(Nat.nat,
      (Transition.transition_ext[Unit], List[Nat.nat])),
     (Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat]))](ts, ts))
                     }),
                    state_transitions)
    val states_bonuses: FSet.fset[(Nat.nat, (Nat.nat, Boolean))] =
      FSet.ffUnion[(Nat.nat,
                     (Nat.nat,
                       Boolean))](FSet.fimage[(Nat.nat,
        FSet.fset[((Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])),
                    (Nat.nat,
                      (Transition.transition_ext[Unit], List[Nat.nat])))]),
       FSet.fset[(Nat.nat,
                   (Nat.nat,
                     Boolean))]](((a: (Nat.nat,
FSet.fset[((Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])),
            (Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])))]))
                                    =>
                                   {
                                     val (_, aa):
   (Nat.nat,
     FSet.fset[((Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])),
                 (Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])))])
                                       = a;
                                     FSet.fimage[((Nat.nat,
            (Transition.transition_ext[Unit], List[Nat.nat])),
           (Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat]))),
          (Nat.nat,
            (Nat.nat,
              Boolean))](((ab: ((Nat.nat,
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat])),
                                 (Nat.nat,
                                   (Transition.transition_ext[Unit],
                                     List[Nat.nat]))))
                            =>
                           {
                             val (ac, b):
                                   ((Nat.nat,
                                      (Transition.transition_ext[Unit],
List[Nat.nat])),
                                     (Nat.nat,
                                       (Transition.transition_ext[Unit],
 List[Nat.nat])))
                               = ab;
                             ({
                                val (d1, (t1, id1)):
                                      (Nat.nat,
(Transition.transition_ext[Unit], List[Nat.nat]))
                                  = ac;
                                ((ad: (Nat.nat,
(Transition.transition_ext[Unit], List[Nat.nat])))
                                   =>
                                  {
                                    val (d2, (t2, id2)):
  (Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat]))
                                      = ad;
                                    (d1, (d2,
   (! (Lista.equal_lista[Nat.nat](id1, id2))) && (Transition.identical_except_guard(t1,
     t2))))
                                  })
                              })(b)
                           }),
                          aa)
                                   }),
                                  state_pairs))
    val states_scoreboard: Map[((Nat.nat, Nat.nat)), Nat.nat] =
      Lista.fold[(Nat.nat, (Nat.nat, Boolean)),
                  Map[((Nat.nat,
                        Nat.nat)), Nat.nat]](((a: (Nat.nat, (Nat.nat, Boolean)))
        =>
       {
         val (s1, (s2, l)): (Nat.nat, (Nat.nat, Boolean)) = a;
         ((scores: Map[((Nat.nat, Nat.nat)), Nat.nat]) =>
           (scores + (((s1, s2) -> (Nat.plus_nata(scores((s1, s2)),
           bool2nat(l)))))))
       }),
      FSet.sorted_list_of_fset[(Nat.nat, (Nat.nat, Boolean))](states_bonuses),
      scala.collection.immutable.Map().withDefaultValue(Nat.zero_nata));
    FSet.fset_of_list[score_ext[Unit]](Lista.map[((Nat.nat, Nat.nat), Nat.nat),
          score_ext[Unit]](((a: ((Nat.nat, Nat.nat), Nat.nat)) =>
                             {
                               val (aa, b): ((Nat.nat, Nat.nat), Nat.nat) = a;
                               ({
                                  val (s1, s2): (Nat.nat, Nat.nat) = aa;
                                  ((l: Nat.nat) =>
                                    score_exta[Unit](l, s1, s2, ()))
                                })(b)
                             }),
                            finfun_to_pairs[(Nat.nat, Nat.nat),
     Nat.nat](states_scoreboard)))
  }

def k_score(k: Nat.nat,
             e: FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))],
             strat:
               (List[Nat.nat]) =>
                 (List[Nat.nat]) =>
                   (FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]) =>
                     Nat.nat):
      FSet.fset[score_ext[Unit]]
  =
  {
    val states: FSet.fset[Nat.nat] = S(e)
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
                          (s1, (s2, (paths_of_length(k, e, s1),
                                      paths_of_length(k, e, s2))))
                        }),
                       pairs_to_score)
    val scores: FSet.fset[score_ext[Unit]] =
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
score_exta[Unit](score_from_list(p1, p2, e, strat), s1, s2, ())
                                      }),
                                     paths)
    val bonus_scores: FSet.fset[score_ext[Unit]] = bonus_score(e);
    FSet.ffilter[score_ext[Unit]](((x: score_ext[Unit]) =>
                                    Nat.less_nat(Nat.zero_nata,
          Score[Unit](x))),
                                   scoreboard_add(bonus_scores, scores))
  }

def max_int(e: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Int.int
  =
  EFSM.max_int(tm(e))

def max_reg(e: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Option[Nat.nat]
  =
  EFSM.max_reg(tm(e))

def score_state_pair(strat:
                       (List[Nat.nat]) =>
                         (List[Nat.nat]) =>
                           (FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                             Nat.nat,
                      e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                      s1: Nat.nat, s2: Nat.nat):
      Nat.nat
  =
  {
    val t1: FSet.fset[(Nat.nat,
                        (Transition.transition_ext[Unit], List[Nat.nat]))]
      = outgoing_transitions(s1, e)
    val t2: FSet.fset[(Nat.nat,
                        (Transition.transition_ext[Unit], List[Nat.nat]))]
      = outgoing_transitions(s2, e);
    FSet_Utils.fSum[Nat.nat](FSet.fimage[((Nat.nat,
    (Transition.transition_ext[Unit], List[Nat.nat])),
   (Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat]))),
  Nat.nat](((a: ((Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])),
                  (Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat]))))
              =>
             {
               val (aa, b):
                     ((Nat.nat,
                        (Transition.transition_ext[Unit], List[Nat.nat])),
                       (Nat.nat,
                         (Transition.transition_ext[Unit], List[Nat.nat])))
                 = a;
               ({
                  val (_, (_, t1a)):
                        (Nat.nat,
                          (Transition.transition_ext[Unit], List[Nat.nat]))
                    = aa;
                  ((ab: (Nat.nat,
                          (Transition.transition_ext[Unit], List[Nat.nat])))
                     =>
                    {
                      val (_, (_, t2a)):
                            (Nat.nat,
                              (Transition.transition_ext[Unit], List[Nat.nat]))
                        = ab;
                      ((strat(t1a))(t2a))(e)
                    })
                })(b)
             }),
            FSet_Utils.fprod[(Nat.nat,
                               (Transition.transition_ext[Unit],
                                 List[Nat.nat])),
                              (Nat.nat,
                                (Transition.transition_ext[Unit],
                                  List[Nat.nat]))](t1, t2)))
  }

def score_1(e: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))],
             strat:
               (List[Nat.nat]) =>
                 (List[Nat.nat]) =>
                   (FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]) =>
                     Nat.nat):
      FSet.fset[score_ext[Unit]]
  =
  {
    val states: FSet.fset[Nat.nat] = S(e)
    val pairs_to_score: FSet.fset[(Nat.nat, Nat.nat)] =
      FSet.ffilter[(Nat.nat,
                     Nat.nat)](((a: (Nat.nat, Nat.nat)) =>
                                 {
                                   val (aa, b): (Nat.nat, Nat.nat) = a;
                                   Nat.less_nat(aa, b)
                                 }),
                                FSet_Utils.fprod[Nat.nat,
          Nat.nat](states, states))
    val scores: FSet.fset[score_ext[Unit]] =
      FSet.fimage[(Nat.nat, Nat.nat),
                   score_ext[Unit]](((a: (Nat.nat, Nat.nat)) =>
                                      {
val (s1, s2): (Nat.nat, Nat.nat) = a;
score_exta[Unit](score_state_pair(strat, e, s1, s2), s1, s2, ())
                                      }),
                                     pairs_to_score)
    val bonus_scores: FSet.fset[score_ext[Unit]] = bonus_score(e);
    FSet.ffilter[score_ext[Unit]](((x: score_ext[Unit]) =>
                                    Nat.less_nat(Nat.zero_nata,
          Score[Unit](x))),
                                   scoreboard_add(bonus_scores, scores))
  }

def all_regs(e: FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]):
      Set.set[Nat.nat]
  =
  EFSM.all_regs(tm(e))

def make_outputs(p: List[Value.value]): List[AExp.aexp[VName.vname]] =
  Lista.map[Value.value,
             AExp.aexp[VName.vname]](((a: Value.value) =>
                                       AExp.L[VName.vname](a)),
                                      p)

def make_guard(g: List[Value.value], n: Nat.nat): List[GExp.gexp[VName.vname]] =
  Lista.map[(Nat.nat, Value.value),
             GExp.gexp[VName.vname]](((a: (Nat.nat, Value.value)) =>
                                       {
 val (na, h): (Nat.nat, Value.value) = a;
 GExp.Eq[VName.vname](AExp.V[VName.vname](VName.I(na)), AExp.L[VName.vname](h))
                                       }),
                                      Lista.enumerate[Value.value](n, g))

def make_transition(label: String, inputs: List[Value.value],
                     outputs: List[Value.value]):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](label, Nat.Nata(inputs.par.length),
                                    make_guard(inputs, Nat.zero_nata),
                                    make_outputs(outputs), Nil, ())

def enumerate_log(x0: List[List[Transition.transition_ext[Unit]]], uu: Nat.nat):
      List[List[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]]
  =
  (x0, uu) match {
  case (Nil, uu) => Nil
  case ((h::t), n) =>
    ((Lista.map[(Nat.nat, Transition.transition_ext[Unit]),
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit])](((a:
                 (Nat.nat, Transition.transition_ext[Unit]))
                =>
               {
                 val (s, aa): (Nat.nat, Transition.transition_ext[Unit]) = a;
                 ((s, Nat.plus_nata(s, Nat.Nata((1)))), aa)
               }),
              Lista.enumerate[Transition.transition_ext[Unit]](n,
                        h)))::(enumerate_log(t,
      Nat.plus_nata(n, Nat.Nata(h.par.length)))))
}

def merge_branch(e: List[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
                  s: Nat.nat,
                  x2: List[((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])]):
      List[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  (e, s, x2) match {
  case (e, s, Nil) => e
  case (e, s, (((from, to), t)::ts)) =>
    (Lista.find[((Nat.nat, Nat.nat),
                  Transition.transition_ext[Unit])](((a:
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
               =>
              {
                val (aa, b):
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                  = a;
                ({
                   val (froma, _): (Nat.nat, Nat.nat) = aa;
                   ((tran: Transition.transition_ext[Unit]) =>
                     (Nat.equal_nata(froma,
                                      s)) && (Transition.equal_transition_exta[Unit](tran,
      t)))
                 })(b)
              }),
             e)
       match {
       case None => e ++ (((s, to), t)::ts)
       case Some(((_, toa), _)) => merge_branch(e, toa, ts)
     })
}

def make_pta(log: List[List[(String, (List[Value.value], List[Value.value]))]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val transitions: List[List[Transition.transition_ext[Unit]]] =
      Lista.map[List[(String, (List[Value.value], List[Value.value]))],
                 List[Transition.transition_ext[Unit]]](((a:
                    List[(String, (List[Value.value], List[Value.value]))])
                   =>
                  Lista.map[(String, (List[Value.value], List[Value.value])),
                             Transition.transition_ext[Unit]](((aa:
                          (String, (List[Value.value], List[Value.value])))
                         =>
                        {
                          val (l, ab):
                                (String, (List[Value.value], List[Value.value]))
                            = aa
                          val (ac, b): (List[Value.value], List[Value.value]) =
                            ab;
                          make_transition(l, ac, b)
                        }),
                       a)),
                 log)
    val enumerated:
          List[List[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]]
      = enumerate_log(transitions, Nat.zero_nata);
    FSet.fset_of_list[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))](Lista.map[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])),
                                (List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))](((a:
                                   (Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])))
                                  =>
                                 {
                                   val (id, aa):
 (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                     = a;
                                   ((id::Nil), aa)
                                 }),
                                Lista.enumerate[((Nat.nat, Nat.nat),
          Transition.transition_ext[Unit])](Nat.zero_nata,
     Lista.fold[List[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
                 List[((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit])]](((branch:
                       List[((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])])
                      =>
                     (acc: List[((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])])
                       =>
                     merge_branch(acc, Nat.zero_nata, branch)),
                    enumerated, Nil))))
  }

def i_possible_steps(e: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      s: Nat.nat, r: Map[Nat.nat, Option[Value.value]],
                      l: String, i: List[Value.value]):
      FSet.fset[(List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (List[Nat.nat],
                 (Nat.nat,
                   Transition.transition_ext[Unit]))](((a:
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, aa):
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a
                  val (ab, b):
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                    = aa;
                  ({
                     val (_, dest): (Nat.nat, Nat.nat) = ab;
                     ((t: Transition.transition_ext[Unit]) => (uid, (dest, t)))
                   })(b)
                }),
               FSet.ffilter[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))](((a:
                               (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])))
                              =>
                             {
                               val (_, aa):
                                     (List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))
                                 = a
                               val (ab, b):
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])
                                 = aa;
                               ({
                                  val (origin, _): (Nat.nat, Nat.nat) = ab;
                                  ((t: Transition.transition_ext[Unit]) =>
                                    (Nat.equal_nata(origin,
             s)) && ((Transition.Label[Unit](t) ==
                       l) && ((Nat.equal_nata(Nat.Nata(i.par.length),
       Transition.Arity[Unit](t))) && (GExp.apply_guards(Transition.Guards[Unit](t),
                  AExp.join_ir(i, r))))))
                                })(b)
                             }),
                            e))

def test_trace(x0: List[(String, (List[Value.value], List[Value.value]))],
                uu: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))],
                uv: Nat.nat, uw: Map[Nat.nat, Option[Value.value]]):
      (List[(String,
              (List[Value.value],
                (Nat.nat,
                  (Nat.nat,
                    (Map[Nat.nat, Option[Value.value]],
                      (List[Nat.nat],
                        (List[Value.value], List[Option[Value.value]])))))))],
        List[(String, (List[Value.value], List[Value.value]))])
  =
  (x0, uu, uv, uw) match {
  case (Nil, uu, uv, uw) => (Nil, Nil)
  case (((l, (i, expected))::es), e, s, r) =>
    {
      val ps: FSet.fset[(List[Nat.nat],
                          (Nat.nat, Transition.transition_ext[Unit]))]
        = i_possible_steps(e, s, r, l, i);
      (if (FSet_Utils.fis_singleton[(List[Nat.nat],
                                      (Nat.nat,
Transition.transition_ext[Unit]))](ps))
        {
          val (id, (sa, t)):
                (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
            = FSet.fthe_elem[(List[Nat.nat],
                               (Nat.nat, Transition.transition_ext[Unit]))](ps)
          val ra: Map[Nat.nat, Option[Value.value]] =
            (Transition.apply_updates(Transition.Updates[Unit](t),
                                       AExp.join_ir(i, r))).apply(r)
          val actual: List[Option[Value.value]] =
            Transition.apply_outputs[VName.vname](Transition.Outputs[Unit](t),
           AExp.join_ir(i, r))
          val a: (List[(String,
                         (List[Value.value],
                           (Nat.nat,
                             (Nat.nat,
                               (Map[Nat.nat, Option[Value.value]],
                                 (List[Nat.nat],
                                   (List[Value.value],
                                     List[Option[Value.value]])))))))],
                   List[(String, (List[Value.value], List[Value.value]))])
            = test_trace(es, e, sa, ra)
          val (est, aa):
                (List[(String,
                        (List[Value.value],
                          (Nat.nat,
                            (Nat.nat,
                              (Map[Nat.nat, Option[Value.value]],
                                (List[Nat.nat],
                                  (List[Value.value],
                                    List[Option[Value.value]])))))))],
                  List[(String, (List[Value.value], List[Value.value]))])
            = a;
          (((l, (i, (s, (sa, (r, (id, (expected, actual)))))))::est), aa)
        }
        else (Nil, ((l, (i, expected))::es)))
    }
}

def test_log(l: List[List[(String, (List[Value.value], List[Value.value]))]],
              e: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]):
      List[(List[(String,
                   (List[Value.value],
                     (Nat.nat,
                       (Nat.nat,
                         (Map[Nat.nat, Option[Value.value]],
                           (List[Nat.nat],
                             (List[Value.value],
                               List[Option[Value.value]])))))))],
             List[(String, (List[Value.value], List[Value.value]))])]
  =
  Lista.map[List[(String, (List[Value.value], List[Value.value]))],
             (List[(String,
                     (List[Value.value],
                       (Nat.nat,
                         (Nat.nat,
                           (Map[Nat.nat, Option[Value.value]],
                             (List[Nat.nat],
                               (List[Value.value],
                                 List[Option[Value.value]])))))))],
               List[(String,
                      (List[Value.value],
                        List[Value.value]))])](((t:
           List[(String, (List[Value.value], List[Value.value]))])
          =>
         test_trace(t, e, Nat.zero_nata,
                     scala.collection.immutable.Map().withDefaultValue(None))),
        l)

def all_paths(g: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))],
               v: Nat.nat, closed: List[Nat.nat]):
      FSet.fset[List[Nat.nat]]
  =
  (if ((closed.contains(v)) || (! (FSet.fmember[Nat.nat](v, nodes(g)))))
    FSet.bot_fset[List[Nat.nat]]
    else (if (FSet.equal_fseta[Nat.nat](out(g, v), FSet.bot_fset[Nat.nat]))
           FSet.finsert[List[Nat.nat]]((v::Nil), FSet.bot_fset[List[Nat.nat]])
           else FSet.finsert[List[Nat.nat]]((v::Nil),
     FSet.fimage[List[Nat.nat],
                  List[Nat.nat]](((a: List[Nat.nat]) => (v::a)),
                                  FSet_Utils.fUnion[List[Nat.nat]](FSet.fimage[Nat.nat,
FSet.fset[List[Nat.nat]]](((s: Nat.nat) => all_paths(g, s, (v::closed))),
                           out(g, v)))))))

def get_by_ids(e: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
                uid: List[Nat.nat]):
      Transition.transition_ext[Unit]
  =
  (Fun.comp[((Nat.nat, Nat.nat), Transition.transition_ext[Unit]),
             Transition.transition_ext[Unit],
             (List[Nat.nat],
               ((Nat.nat, Nat.nat),
                 Transition.transition_ext[Unit]))](((a:
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
               =>
              a._2),
             ((a: (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                =>
               a._2))).apply(FSet.fthe_elem[(List[Nat.nat],
      ((Nat.nat, Nat.nat),
        Transition.transition_ext[Unit]))](FSet.ffilter[(List[Nat.nat],
                  ((Nat.nat, Nat.nat),
                    Transition.transition_ext[Unit]))](((a:
                   (List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                  =>
                 {
                   val (tids, _):
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))
                     = a;
                   Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
             Set.seta[Nat.nat](tids))
                 }),
                e)))

def replace_transition(e: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                        uid: List[Nat.nat],
                        newa: Transition.transition_ext[Unit]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uids, aa):
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a
                  val (ab, b):
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                    = aa;
                  ({
                     val (from, to): (Nat.nat, Nat.nat) = ab;
                     ((t: Transition.transition_ext[Unit]) =>
                       (if (Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                      Set.seta[Nat.nat](uids)))
                         (uids, ((from, to), newa))
                         else (uids, ((from, to), t))))
                   })(b)
                }),
               e)

def replace_all(e: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                 ids: List[List[Nat.nat]],
                 newa: Transition.transition_ext[Unit]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[List[Nat.nat],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((id:
                            List[Nat.nat])
                           =>
                          (acc: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                            =>
                          replace_transition(acc, id, newa)),
                         ids, e)

def rename_heads(f: List[(Nat.nat, Nat.nat)], x1: List[Nat.nat], uu: Nat.nat):
      List[(Nat.nat, Nat.nat)]
  =
  (f, x1, uu) match {
  case (f, Nil, uu) => f
  case (f, (h::t), n) =>
    (if (Lista.list_ex[(Nat.nat,
                         Nat.nat)](((a: (Nat.nat, Nat.nat)) =>
                                     {
                                       val (aa, _): (Nat.nat, Nat.nat) = a;
                                       Nat.equal_nata(aa, h)
                                     }),
                                    f))
      rename_heads(f, t, n)
      else rename_heads(((h, n)::f), t, Nat.plus_nata(n, Nat.Nata((1)))))
}

def max_reg_total(e: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  (max_reg(e) match {
     case None => Nat.zero_nata
     case Some(r) => r
   })

def null_modifier(f: List[Nat.nat], uu: List[Nat.nat], uv: Nat.nat,
                   uw: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   ux: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   uy: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   uz: (FSet.fset[((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])]) =>
                         Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  None

def inference_step(failedMerges: Set.set[(Nat.nat, Nat.nat)],
                    e: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                    s: FSet.fset[score_ext[Unit]],
                    m: (List[Nat.nat]) =>
                         (List[Nat.nat]) =>
                           Nat.nat =>
                             (FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                               (FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 (FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                   ((FSet.fset[((Nat.nat, Nat.nat),
         Transition.transition_ext[Unit])]) =>
                                     Boolean) =>
                                     Option[FSet.fset[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                    check:
                      (FSet.fset[((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])]) =>
                        Boolean,
                    np: (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], List[Nat.nat]),
  (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      (Option[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]],
        Set.set[(Nat.nat, Nat.nat)])
  =
  (if (FSet.equal_fseta[score_ext[Unit]](s, FSet.bot_fset[score_ext[Unit]]))
    (None, failedMerges)
    else {
           val h: score_ext[Unit] = FSet.fMin[score_ext[Unit]](s)
           val t: FSet.fset[score_ext[Unit]] =
             FSet_Utils.fremove[score_ext[Unit]](h, s);
           (merge(failedMerges, e, S1[Unit](h), S2[Unit](h), m, check, np) match
              {
              case (None, failedMergesa) =>
                inference_step(Set.insert[(Nat.nat,
    Nat.nat)]((S1[Unit](h), S2[Unit](h)), failedMergesa),
                                e, t, m, check, np)
              case (Some(newa), failedMergesa) =>
                (Some[FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]](newa),
                  failedMergesa)
            })
         })

def nondeterministic(t: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      np: (FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]) =>
                            FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat),
  ((Transition.transition_ext[Unit], List[Nat.nat]),
    (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      Boolean
  =
  ! (deterministic(t, np))

def reindex_statewise(e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fset_of_list[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))](Lista.map[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])),
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))](((a:
                                 (Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])))
                                =>
                               {
                                 val (i, aa):
                                       (Nat.nat,
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                   = a;
                                 ((i::Nil), aa)
                               }),
                              Lista.enumerate[((Nat.nat, Nat.nat),
        Transition.transition_ext[Unit])](Nat.zero_nata,
   FSet.sorted_list_of_fset[((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])](tm(e)))))

def depth_first_label(e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val paths: FSet.fset[List[Nat.nat]] = all_paths(e, Nat.zero_nata, Nil)
    val enumerated: List[(Nat.nat, Nat.nat)] =
      Lista.foldr[(Nat.nat, List[Nat.nat]),
                   List[(Nat.nat,
                          Nat.nat)]](((a: (Nat.nat, List[Nat.nat])) =>
                                       {
 val (_, l): (Nat.nat, List[Nat.nat]) = a;
 ((acc: List[(Nat.nat, Nat.nat)]) =>
   acc ++ Lista.enumerate[Nat.nat](Nat.Nata(acc.par.length), l))
                                       }),
                                      Lista.sort_key[(Nat.nat, List[Nat.nat]),
              (Nat.nat,
                List[Nat.nat])](((x: (Nat.nat, List[Nat.nat])) => x),
                                 Lista.map[List[Nat.nat],
    (Nat.nat,
      List[Nat.nat])](((l: List[Nat.nat]) => (Nat.Nata(l.par.length), l)),
                       FSet.sorted_list_of_fset[List[Nat.nat]](paths))),
                                      Nil)
    val rename_opt: Nat.nat => Option[Nat.nat] =
      Lista.fold[(Nat.nat, Nat.nat),
                  Nat.nat =>
                    Option[Nat.nat]](((a: (Nat.nat, Nat.nat)) =>
                                       {
 val (inx, state): (Nat.nat, Nat.nat) = a;
 ((acc: Nat.nat => Option[Nat.nat]) =>
   (if (Optiona.is_none[Nat.nat](acc(state)))
     Fun.fun_upd[Nat.nat, Option[Nat.nat]](acc, state, Some[Nat.nat](inx))
     else acc))
                                       }),
                                      enumerated, ((_: Nat.nat) => None))
    val rename: Nat.nat => Nat.nat =
      Lista.fold[Nat.nat,
                  Nat.nat =>
                    Nat.nat](((k: Nat.nat) => (acc: Nat.nat => Nat.nat) =>
                               {
                                 val (Some(a)): Option[Nat.nat] = rename_opt(k);
                                 Fun.fun_upd[Nat.nat, Nat.nat](acc, k, a)
                               }),
                              FSet.sorted_list_of_fset[Nat.nat](S(e)),
                              Fun.id[Nat.nat])
    val a: FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))](((a:
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])))
                       =>
                      {
                        val (id, aa):
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))
                          = a
                        val (ab, b):
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])
                          = aa;
                        ({
                           val (from, to): (Nat.nat, Nat.nat) = ab;
                           ((t: Transition.transition_ext[Unit]) =>
                             (id, ((rename(from), rename(to)), t)))
                         })(b)
                      }),
                     e);
    reindex_statewise(a)
  }

def breadth_first_rename(l: List[List[Nat.nat]], f: List[(Nat.nat, Nat.nat)]):
      List[(Nat.nat, Nat.nat)]
  =
  {
    val la: List[List[Nat.nat]] =
      Lista.filter[List[Nat.nat]](((x: List[Nat.nat]) =>
                                    Nat.less_nat(Nat.zero_nata,
          Nat.Nata(x.par.length))),
                                   l);
    (if (la.isEmpty) f
      else {
             val heads: List[Nat.nat] =
               Lista.map[List[Nat.nat],
                          Nat.nat](((a: List[Nat.nat]) => a.head), la)
             val tails: List[List[Nat.nat]] =
               Lista.map[List[Nat.nat],
                          List[Nat.nat]](((a: List[Nat.nat]) =>
   Lista.tl[Nat.nat](a)),
  la)
             val a: List[(Nat.nat, Nat.nat)] =
               rename_heads(f, heads, Nat.Nata(f.par.length));
             breadth_first_rename(tails, a)
           })
  }

def breadth_first_label(e: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val paths: FSet.fset[List[Nat.nat]] = all_paths(e, Nat.zero_nata, Nil)
    val rename_pairs: List[(Nat.nat, Nat.nat)] =
      breadth_first_rename(FSet.sorted_list_of_fset[List[Nat.nat]](paths), Nil)
    val rename: Nat.nat => Nat.nat =
      Lista.fold[(Nat.nat, Nat.nat),
                  Nat.nat =>
                    Nat.nat](((a: (Nat.nat, Nat.nat)) =>
                               {
                                 val (old, newa): (Nat.nat, Nat.nat) = a;
                                 ((acc: Nat.nat => Nat.nat) =>
                                   Fun.fun_upd[Nat.nat,
        Nat.nat](acc, old, newa))
                               }),
                              rename_pairs, Fun.id[Nat.nat])
    val a: FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))](((a:
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])))
                       =>
                      {
                        val (id, aa):
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))
                          = a
                        val (ab, b):
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])
                          = aa;
                        ({
                           val (from, to): (Nat.nat, Nat.nat) = ab;
                           ((t: Transition.transition_ext[Unit]) =>
                             (id, ((rename(from), rename(to)), t)))
                         })(b)
                      }),
                     e);
    reindex_statewise(a)
  }

def replace_transitions(e: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))],
                         ts: List[(List[Nat.nat],
                                    Transition.transition_ext[Unit])]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[(List[Nat.nat], Transition.transition_ext[Unit]),
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((a:
                            (List[Nat.nat], Transition.transition_ext[Unit]))
                           =>
                          {
                            val (uid, newa):
                                  (List[Nat.nat],
                                    Transition.transition_ext[Unit])
                              = a;
                            ((acc: FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                               =>
                              replace_transition(acc, uid, newa))
                          }),
                         ts, e)

def state_nondeterminism(og: Nat.nat,
                          nt: FSet.fset[(Nat.nat,
  (Transition.transition_ext[Unit], List[Nat.nat]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (Transition.transition_ext[Unit], List[Nat.nat]))))]
  =
  (if (Nat.less_nat(FSet.size_fset[(Nat.nat,
                                     (Transition.transition_ext[Unit],
                                       List[Nat.nat]))](nt),
                     Code_Numeral.nat_of_integer(BigInt(2))))
    FSet.bot_fset[(Nat.nat,
                    ((Nat.nat, Nat.nat),
                      ((Transition.transition_ext[Unit], List[Nat.nat]),
                        (Transition.transition_ext[Unit], List[Nat.nat]))))]
    else FSet.ffUnion[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          ((Transition.transition_ext[Unit], List[Nat.nat]),
                            (Transition.transition_ext[Unit],
                              List[Nat.nat]))))](FSet.fimage[(Nat.nat,
                       (Transition.transition_ext[Unit], List[Nat.nat])),
                      FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    ((Transition.transition_ext[Unit],
                                       List[Nat.nat]),
                                      (Transition.transition_ext[Unit],
List[Nat.nat]))))]](((x: (Nat.nat,
                           (Transition.transition_ext[Unit], List[Nat.nat])))
                       =>
                      {
                        val (dest, t):
                              (Nat.nat,
                                (Transition.transition_ext[Unit],
                                  List[Nat.nat]))
                          = x;
                        FSet.fimage[(Nat.nat,
                                      (Transition.transition_ext[Unit],
List[Nat.nat])),
                                     (Nat.nat,
                                       ((Nat.nat, Nat.nat),
 ((Transition.transition_ext[Unit], List[Nat.nat]),
   (Transition.transition_ext[Unit],
     List[Nat.nat]))))](((y: (Nat.nat,
                               (Transition.transition_ext[Unit],
                                 List[Nat.nat])))
                           =>
                          {
                            val (desta, ta):
                                  (Nat.nat,
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat]))
                              = y;
                            (og, ((dest, desta), (t, ta)))
                          }),
                         FSet_Utils.fremove[(Nat.nat,
      (Transition.transition_ext[Unit], List[Nat.nat]))](x, nt))
                      }),
                     nt)))

def try_heuristics_check(uu: (FSet.fset[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])]) =>
                               Boolean,
                          x1: List[(List[Nat.nat]) =>
                                     (List[Nat.nat]) =>
                                       Nat.nat =>
 (FSet.fset[(List[Nat.nat],
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
   (FSet.fset[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
     (FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
       ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
         Boolean) =>
         Option[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]]]):
      (List[Nat.nat]) =>
        (List[Nat.nat]) =>
          Nat.nat =>
            (FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              (FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                (FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]) =>
                  ((FSet.fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])]) =>
                    Boolean) =>
                    Option[FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]]
  =
  (uu, x1) match {
  case (uu, Nil) =>
    ((a: List[Nat.nat]) => (b: List[Nat.nat]) => (c: Nat.nat) =>
      (d: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (e: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (f: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (g: (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
            Boolean)
        =>
      null_modifier(a, b, c, d, e, f, g))
  case (check, (h::t)) =>
    ((a: List[Nat.nat]) => (b: List[Nat.nat]) => (c: Nat.nat) =>
      (d: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (e: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (f: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (ch: (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
             Boolean)
        =>
      (((((((h(a))(b))(c))(d))(e))(f))(ch) match {
         case None =>
           (try_heuristics_check(check,
                                  t)).apply(a).apply(b).apply(c).apply(d).apply(e).apply(f).apply(ch)
         case Some(aa) =>
           Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](aa)
       }))
}

def nondeterministic_pairs(t: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (Transition.transition_ext[Unit], List[Nat.nat]))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (Transition.transition_ext[Unit],
                       List[Nat.nat]))))](((a:
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], List[Nat.nat]),
            (Transition.transition_ext[Unit], List[Nat.nat])))))
     =>
    {
      val (_, aa):
            (Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (Transition.transition_ext[Unit], List[Nat.nat]))))
        = a
      val (_, ab):
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[Unit], List[Nat.nat]),
                (Transition.transition_ext[Unit], List[Nat.nat])))
        = aa
      val (ac, b):
            ((Transition.transition_ext[Unit], List[Nat.nat]),
              (Transition.transition_ext[Unit], List[Nat.nat]))
        = ab;
      ({
         val (ta, _): (Transition.transition_ext[Unit], List[Nat.nat]) = ac;
         ((ad: (Transition.transition_ext[Unit], List[Nat.nat])) =>
           {
             val (taa, _): (Transition.transition_ext[Unit], List[Nat.nat]) =
               ad;
             (Transition.Label[Unit](ta) ==
               Transition.Label[Unit](taa)) && ((Nat.equal_nata(Transition.Arity[Unit](ta),
                         Transition.Arity[Unit](taa))) && (EFSM.choice(ta,
                                taa)))
           })
       })(b)
    }),
   FSet.ffUnion[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (Transition.transition_ext[Unit],
                        List[Nat.nat]))))](FSet.fimage[Nat.nat,
                FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              ((Transition.transition_ext[Unit], List[Nat.nat]),
                                (Transition.transition_ext[Unit],
                                  List[Nat.nat]))))]](((s: Nat.nat) =>
                state_nondeterminism(s, outgoing_transitions(s, t))),
               S(t))))

def nondeterministic_pairs_labar(t: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (Transition.transition_ext[Unit], List[Nat.nat]))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (Transition.transition_ext[Unit],
                       List[Nat.nat]))))](((a:
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], List[Nat.nat]),
            (Transition.transition_ext[Unit], List[Nat.nat])))))
     =>
    {
      val (_, aa):
            (Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (Transition.transition_ext[Unit], List[Nat.nat]))))
        = a
      val (ab, b):
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[Unit], List[Nat.nat]),
                (Transition.transition_ext[Unit], List[Nat.nat])))
        = aa;
      ({
         val (_, _): (Nat.nat, Nat.nat) = ab;
         ((ac: ((Transition.transition_ext[Unit], List[Nat.nat]),
                 (Transition.transition_ext[Unit], List[Nat.nat])))
            =>
           {
             val (ad, ba):
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (Transition.transition_ext[Unit], List[Nat.nat]))
               = ac;
             ({
                val (ta, _): (Transition.transition_ext[Unit], List[Nat.nat]) =
                  ad;
                ((ae: (Transition.transition_ext[Unit], List[Nat.nat])) =>
                  {
                    val (taa, _):
                          (Transition.transition_ext[Unit], List[Nat.nat])
                      = ae;
                    (Transition.Label[Unit](ta) ==
                      Transition.Label[Unit](taa)) && ((Nat.equal_nata(Transition.Arity[Unit](ta),
                                Transition.Arity[Unit](taa))) && ((EFSM.choice(ta,
taa)) || (Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](ta),
             Transition.Outputs[Unit](taa)))))
                  })
              })(ba)
           })
       })(b)
    }),
   FSet.ffUnion[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (Transition.transition_ext[Unit],
                        List[Nat.nat]))))](FSet.fimage[Nat.nat,
                FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              ((Transition.transition_ext[Unit], List[Nat.nat]),
                                (Transition.transition_ext[Unit],
                                  List[Nat.nat]))))]](((s: Nat.nat) =>
                state_nondeterminism(s, outgoing_transitions(s, t))),
               S(t))))

def nondeterministic_pairs_labar_dest(t:
FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (Transition.transition_ext[Unit], List[Nat.nat]))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (Transition.transition_ext[Unit],
                       List[Nat.nat]))))](((a:
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], List[Nat.nat]),
            (Transition.transition_ext[Unit], List[Nat.nat])))))
     =>
    {
      val (_, aa):
            (Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (Transition.transition_ext[Unit], List[Nat.nat]))))
        = a
      val (ab, b):
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[Unit], List[Nat.nat]),
                (Transition.transition_ext[Unit], List[Nat.nat])))
        = aa;
      ({
         val (d, da): (Nat.nat, Nat.nat) = ab;
         ((ac: ((Transition.transition_ext[Unit], List[Nat.nat]),
                 (Transition.transition_ext[Unit], List[Nat.nat])))
            =>
           {
             val (ad, ba):
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (Transition.transition_ext[Unit], List[Nat.nat]))
               = ac;
             ({
                val (ta, _): (Transition.transition_ext[Unit], List[Nat.nat]) =
                  ad;
                ((ae: (Transition.transition_ext[Unit], List[Nat.nat])) =>
                  {
                    val (taa, _):
                          (Transition.transition_ext[Unit], List[Nat.nat])
                      = ae;
                    (Transition.Label[Unit](ta) ==
                      Transition.Label[Unit](taa)) && ((Nat.equal_nata(Transition.Arity[Unit](ta),
                                Transition.Arity[Unit](taa))) && ((EFSM.choice(ta,
taa)) || ((Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](ta),
              Transition.Outputs[Unit](taa))) && (Nat.equal_nata(d, da)))))
                  })
              })(ba)
           })
       })(b)
    }),
   FSet.ffUnion[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (Transition.transition_ext[Unit],
                        List[Nat.nat]))))](FSet.fimage[Nat.nat,
                FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              ((Transition.transition_ext[Unit], List[Nat.nat]),
                                (Transition.transition_ext[Unit],
                                  List[Nat.nat]))))]](((s: Nat.nat) =>
                state_nondeterminism(s, outgoing_transitions(s, t))),
               S(t))))

} /* object Inference */

object EFSM {

def S(m: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]):
      FSet.fset[Nat.nat]
  =
  FSet.sup_fset[Nat.nat](FSet.fimage[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]),
                                      Nat.nat](((a:
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
          =>
         {
           val (aa, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
             a;
           ({
              val (s, _): (Nat.nat, Nat.nat) = aa;
              ((_: Transition.transition_ext[Unit]) => s)
            })(b)
         }),
        m),
                          FSet.fimage[((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]),
                                       Nat.nat](((a:
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
           =>
          {
            val (aa, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
              a;
            ({
               val (_, s): (Nat.nat, Nat.nat) = aa;
               ((_: Transition.transition_ext[Unit]) => s)
             })(b)
          }),
         m))

def choice(ta: Transition.transition_ext[Unit],
            t: Transition.transition_ext[Unit]):
      Boolean
  =
  Code_Generation.choice_cases(ta, t)

def enumerate_ints(e: FSet.fset[((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])]):
      Set.set[Int.int]
  =
  Complete_Lattices.Sup_set[Int.int](Set.image[((Nat.nat, Nat.nat),
         Transition.transition_ext[Unit]),
        Set.set[Int.int]](((a: ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))
                             =>
                            {
                              val (_, aa):
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])
                                = a;
                              Transition.enumerate_ints(aa)
                            }),
                           FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])](e)))

def max_int(e: FSet.fset[((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit])]):
      Int.int
  =
  Lattices_Big.Max[Int.int](Set.insert[Int.int](Int.zero_int,
         enumerate_ints(e)))

def max_reg(e: FSet.fset[((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit])]):
      Option[Nat.nat]
  =
  {
    val maxes: FSet.fset[Option[Nat.nat]] =
      FSet.fimage[((Nat.nat, Nat.nat), Transition.transition_ext[Unit]),
                   Option[Nat.nat]](((a:
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                       =>
                                      {
val (_, aa): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = a;
Transition.max_reg(aa)
                                      }),
                                     e);
    (if (FSet.equal_fseta[Option[Nat.nat]](maxes,
    FSet.bot_fset[Option[Nat.nat]]))
      None else FSet.fMax[Option[Nat.nat]](maxes))
  }

def all_regs(e: FSet.fset[((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])]):
      Set.set[Nat.nat]
  =
  Complete_Lattices.Sup_set[Nat.nat](Set.image[((Nat.nat, Nat.nat),
         Transition.transition_ext[Unit]),
        Set.set[Nat.nat]](((a: ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))
                             =>
                            {
                              val (_, aa):
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])
                                = a;
                              Transition.enumerate_regs(aa)
                            }),
                           FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])](e)))

def possible_steps(e: FSet.fset[((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])],
                    s: Nat.nat, r: Map[Nat.nat, Option[Value.value]], l: String,
                    i: List[Value.value]):
      FSet.fset[(Nat.nat, Transition.transition_ext[Unit])]
  =
  FSet.fimage[((Nat.nat, Nat.nat), Transition.transition_ext[Unit]),
               (Nat.nat,
                 Transition.transition_ext[Unit])](((a:
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
              =>
             {
               val (aa, b):
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                 = a;
               ({
                  val (_, ab): (Nat.nat, Nat.nat) = aa;
                  ((ba: Transition.transition_ext[Unit]) => (ab, ba))
                })(b)
             }),
            FSet.ffilter[((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit])](((a:
                         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                        =>
                       {
                         val (aa, b):
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])
                           = a;
                         ({
                            val (origin, _): (Nat.nat, Nat.nat) = aa;
                            ((t: Transition.transition_ext[Unit]) =>
                              (Nat.equal_nata(origin,
       s)) && ((Transition.Label[Unit](t) ==
                 l) && ((Nat.equal_nata(Nat.Nata(i.par.length),
 Transition.Arity[Unit](t))) && (GExp.apply_guards(Transition.Guards[Unit](t),
            AExp.join_ir(i, r))))))
                          })(b)
                       }),
                      e))

def accepts_trace_prim(uu: FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])],
                        uv: Nat.nat, uw: Map[Nat.nat, Option[Value.value]],
                        x3: List[(String,
                                   (List[Value.value], List[Value.value]))]):
      Boolean
  =
  (uu, uv, uw, x3) match {
  case (uu, uv, uw, Nil) => true
  case (e, s, r, ((l, (i, p))::t)) =>
    {
      val poss_steps: FSet.fset[(Nat.nat, Transition.transition_ext[Unit])] =
        possible_steps(e, s, r, l, i);
      (if (FSet_Utils.fis_singleton[(Nat.nat,
                                      Transition.transition_ext[Unit])](poss_steps))
        {
          val (sa, ta): (Nat.nat, Transition.transition_ext[Unit]) =
            FSet.fthe_elem[(Nat.nat,
                             Transition.transition_ext[Unit])](poss_steps)
          val outputs: List[Option[Value.value]] =
            Transition.apply_outputs[VName.vname](Transition.Outputs[Unit](ta),
           AExp.join_ir(i, r));
          (if (Lista.equal_lista[Option[Value.value]](outputs,
               Lista.map[Value.value,
                          Option[Value.value]](((a: Value.value) =>
         Some[Value.value](a)),
        p)))
            accepts_trace_prim(e, sa,
                                (Transition.apply_updates(Transition.Updates[Unit](ta),
                   AExp.join_ir(i, r))).apply(r),
                                t)
            else false)
        }
        else FSet.fBex[(Nat.nat,
                         Transition.transition_ext[Unit])](poss_steps,
                    ((a: (Nat.nat, Transition.transition_ext[Unit])) =>
                      {
                        val (sa, ta): (Nat.nat, Transition.transition_ext[Unit])
                          = a;
                        (Lista.equal_lista[Option[Value.value]](Transition.apply_outputs[VName.vname](Transition.Outputs[Unit](ta),
                       AExp.join_ir(i, r)),
                         Lista.map[Value.value,
                                    Option[Value.value]](((aa: Value.value) =>
                   Some[Value.value](aa)),
                  p))) && (accepts_trace_prim(e, sa,
       (Transition.apply_updates(Transition.Updates[Unit](ta),
                                  AExp.join_ir(i, r))).apply(r),
       t))
                      })))
    }
}

def accepts_trace(e: FSet.fset[((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])],
                   s: Nat.nat, r: Map[Nat.nat, Option[Value.value]],
                   l: List[(String, (List[Value.value], List[Value.value]))]):
      Boolean
  =
  accepts_trace_prim(e, s, r, l)

def accepts_log(l: Set.set[List[(String,
                                  (List[Value.value], List[Value.value]))]],
                 e: FSet.fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])]):
      Boolean
  =
  Set.Ball[List[(String,
                  (List[Value.value],
                    List[Value.value]))]](l,
   ((a: List[(String, (List[Value.value], List[Value.value]))]) =>
     accepts_trace(e, Nat.zero_nata,
                    scala.collection.immutable.Map().withDefaultValue(None),
                    a)))

def recognises_prim(e: FSet.fset[((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])],
                     s: Nat.nat, r: Map[Nat.nat, Option[Value.value]],
                     x3: List[(String, List[Value.value])]):
      Boolean
  =
  (e, s, r, x3) match {
  case (e, s, r, Nil) => true
  case (e, s, r, ((l, i)::t)) =>
    {
      val poss_steps: FSet.fset[(Nat.nat, Transition.transition_ext[Unit])] =
        possible_steps(e, s, r, l, i);
      FSet.fBex[(Nat.nat,
                  Transition.transition_ext[Unit])](poss_steps,
             ((a: (Nat.nat, Transition.transition_ext[Unit])) =>
               {
                 val (sa, ta): (Nat.nat, Transition.transition_ext[Unit]) = a;
                 recognises_prim(e, sa,
                                  (Transition.apply_updates(Transition.Updates[Unit](ta),
                     AExp.join_ir(i, r))).apply(r),
                                  t)
               }))
    }
}

def recognises_execution(e: FSet.fset[((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])],
                          s: Nat.nat, r: Map[Nat.nat, Option[Value.value]],
                          t: List[(String, List[Value.value])]):
      Boolean
  =
  recognises_prim(e, s, r, t)

} /* object EFSM */

object Sublist {

def prefixes[A](xs: List[A]): List[List[A]] =
  ((Dirties.foldl[(List[A], List[List[A]]),
                   A](((a: (List[A], List[List[A]])) =>
                        {
                          val (acc1, acc2): (List[A], List[List[A]]) = a;
                          ((x: A) =>
                            ((x::acc1),
                              ((((x::acc1)).par.reverse.toList)::acc2)))
                        }),
                       (Nil, (Nil::Nil)), xs))._2).par.reverse.toList

} /* object Sublist */

object EFSM_Dot {

def vname2dot(x0: VName.vname): String = x0 match {
  case VName.I(n) =>
    "i<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub>"
  case VName.R(n) =>
    "r<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub>"
}

def shows_string: String => String => String =
  ((a: String) => (b: String) => a + b)

def showsp_decimal(p: String, n: Real.real, places: Nat.nat): String => String =
  (if (Dirties.doubleEquals(n, Real.zero_real)) shows_string.apply(p)
    else (if (Nat.equal_nata(places, Nat.zero_nata)) shows_string.apply("...")
           else Fun.comp[String, String,
                          String](showsp_decimal(p,
          Real.minus_real(Real.times_real(n,
   Real.Ratreal(Rat.of_int(Int.int_of_integer(BigInt(10))))),
                           Real.Ratreal(Rat.of_int(Real.floor_real(Real.times_real(n,
    Real.Ratreal(Rat.of_int(Int.int_of_integer(BigInt(10))))))))),
          Nat.minus_nat(places, Nat.Nata((1)))),
                                   shows_string.apply(Code_Numeral.integer_of_int(Real.floor_real(Real.times_real(n,
                                   Real.Ratreal(Rat.of_int(Int.int_of_integer(BigInt(10))))))).toString()))))

def show_decimal(n: Real.real, p: Nat.nat): String =
  ((showsp_decimal("", n, p)).apply(".").reverse)

def string_of_digit(n: Nat.nat): String =
  (if (Nat.equal_nata(n, Nat.zero_nata)) "0"
    else (if (Nat.equal_nata(n, Nat.Nata((1)))) "1"
           else (if (Nat.equal_nata(n, Code_Numeral.nat_of_integer(BigInt(2))))
                  "2" else (if (Nat.equal_nata(n,
        Code_Numeral.nat_of_integer(BigInt(3))))
                             "3" else (if (Nat.equal_nata(n,
                   Code_Numeral.nat_of_integer(BigInt(4))))
"4" else (if (Nat.equal_nata(n, Code_Numeral.nat_of_integer(BigInt(5)))) "5"
           else (if (Nat.equal_nata(n, Code_Numeral.nat_of_integer(BigInt(6))))
                  "6" else (if (Nat.equal_nata(n,
        Code_Numeral.nat_of_integer(BigInt(7))))
                             "7" else (if (Nat.equal_nata(n,
                   Code_Numeral.nat_of_integer(BigInt(8))))
"8" else "9")))))))))

def showsp_nat(p: String, n: Nat.nat): String => String =
  (if (Nat.less_nat(n, Code_Numeral.nat_of_integer(BigInt(10))))
    shows_string.apply(string_of_digit(n))
    else Fun.comp[String, String,
                   String](showsp_nat(p, Euclidean_Division.divide_nat(n,
                                Code_Numeral.nat_of_integer(BigInt(10)))),
                            shows_string.apply(string_of_digit(Euclidean_Division.modulo_nat(n,
              Code_Numeral.nat_of_integer(BigInt(10)))))))

def showsp_int(p: String, i: Int.int): String => String =
  (if (Int.less_int(i, Int.zero_int))
    Fun.comp[String, String,
              String](shows_string.apply("-"),
                       showsp_nat(p, Int.nat(Int.uminus_int(i))))
    else showsp_nat(p, Int.nat(i)))

def show_real(r: Real.real, precision: Nat.nat): String =
  (showsp_int("", Real.floor_real(r))).apply(show_decimal(Real.minus_real(r,
                                   Real.Ratreal(Rat.of_int(Real.floor_real(r)))),
                   precision))

def value2dot(x0: Value.value): String = x0 match {
  case Value.Str(s) => "\"" + s.replace("\\", "\\\\") + "\""
  case Value.Inta(n) => Code_Numeral.integer_of_int(n).toString()
  case Value.Reala(n) => show_real(n, Code_Numeral.nat_of_integer(BigInt(3)))
}

def aexp2dot(x0: AExp.aexp[VName.vname]): String = x0 match {
  case AExp.L(v) => value2dot(v)
  case AExp.V(v) => vname2dot(v)
  case AExp.Plus(a1, a2) => aexp2dot(a1) + " + " + aexp2dot(a2)
  case AExp.Minus(a1, a2) => aexp2dot(a1) + " - " + aexp2dot(a2)
  case AExp.Times(a1, a2) => aexp2dot(a1) + " &times; " + aexp2dot(a2)
  case AExp.Divide(a1, a2) => aexp2dot(a1) + " &divide; " + aexp2dot(a2)
}

def updates2dot_aux(l: List[(Nat.nat, AExp.aexp[VName.vname])]): List[String] =
  Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
             String](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
                       {
                         val (r, u): (Nat.nat, AExp.aexp[VName.vname]) = a;
                         vname2dot(VName.R(r)) + " := " + aexp2dot(u)
                       }),
                      l)

def updates2dot(x0: List[(Nat.nat, AExp.aexp[VName.vname])]): String = x0 match
  {
  case Nil => ""
  case (v::va) => "&#91;" + (updates2dot_aux((v::va))).mkString(", ") + "&#93;"
}

def outputs2dot(x0: List[AExp.aexp[VName.vname]], uu: Nat.nat): List[String] =
  (x0, uu) match {
  case (Nil, uu) => Nil
  case ((h::t), n) =>
    (("o<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub> := " +
       aexp2dot(h))::(outputs2dot(t, Nat.plus_nata(n, Nat.Nata((1))))))
}

def latter2dot(t: Transition.transition_ext[Unit]): String =
  {
    val l: String =
      (outputs2dot(Transition.Outputs[Unit](t), Nat.Nata((1)))).mkString(", ") +
        updates2dot(Transition.Updates[Unit](t));
    (if (l == "") "" else "/" + l)
  }

def gexp2dot(x0: GExp.gexp[VName.vname]): String = x0 match {
  case GExp.Bc(true) => "True"
  case GExp.Bc(false) => "False"
  case GExp.Eq(a1, a2) => aexp2dot(a1) + " = " + aexp2dot(a2)
  case GExp.Gt(a1, a2) => aexp2dot(a1) + " &gt; " + aexp2dot(a2)
  case GExp.In(v, l) =>
    vname2dot(v) + "&isin;{" +
      (Lista.map[Value.value,
                  String](((a: Value.value) => value2dot(a)),
                           l)).mkString(", ") +
      "}"
  case GExp.Nor(g1, g2) =>
    (if (GExp.equal_gexpa[VName.vname](g1, g2))
      (g1 match {
         case GExp.Bc(_) => "&not;(" + gexp2dot(g1) + ")"
         case GExp.Eq(_, _) => "&not;(" + gexp2dot(g1) + ")"
         case GExp.Gt(a1, a2) => aexp2dot(a1) + " &le; " + aexp2dot(a2)
         case GExp.In(_, _) => "&not;(" + gexp2dot(g1) + ")"
         case GExp.Nor(_, _) => "&not;(" + gexp2dot(g1) + ")"
       })
      else "!(" + gexp2dot(g1) + "&or;" + gexp2dot(g2) + ")")
}

def guards2dot(x0: List[GExp.gexp[VName.vname]]): String = x0 match {
  case Nil => ""
  case (v::va) =>
    "&#91;" +
      (Lista.map[GExp.gexp[VName.vname],
                  String](((a: GExp.gexp[VName.vname]) => gexp2dot(a)),
                           (v::va))).mkString(", ") +
      "&#93;"
}

def transition2dot(t: Transition.transition_ext[Unit]): String =
  Transition.Label[Unit](t) + ":" +
    Code_Numeral.integer_of_nat(Transition.Arity[Unit](t)).toString() +
    guards2dot(Transition.Guards[Unit](t)) +
    latter2dot(t)

def efsm2dot(e: FSet.fset[((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])]):
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
        EFSM.S(e))))).mkString("\u000A") +
    "\u000A" +
    "\u000A" +
    (Lista.map[((Nat.nat, Nat.nat), Transition.transition_ext[Unit]),
                String](((a: ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))
                           =>
                          {
                            val (aa, b):
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])
                              = a;
                            ({
                               val (from, to): (Nat.nat, Nat.nat) = aa;
                               ((t: Transition.transition_ext[Unit]) =>
                                 "  s" +
                                   Code_Numeral.integer_of_nat(from).toString() +
                                   "->s" +
                                   Code_Numeral.integer_of_nat(to).toString() +
                                   "[label=<<i>" +
                                   transition2dot(t) +
                                   "</i>>];")
                             })(b)
                          }),
                         FSet.sorted_list_of_fset[((Nat.nat, Nat.nat),
            Transition.transition_ext[Unit])](e))).mkString("\u000A") +
    "\u000A" +
    "}"

def show_nats(l: List[Nat.nat]): String =
  (Lista.map[Nat.nat,
              String](((a: Nat.nat) =>
                        Code_Numeral.integer_of_nat(a).toString()),
                       l)).mkString(", ")

def iefsm2dot(e: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]):
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
        Inference.S(e))))).mkString("\u000A") +
    "\u000A" +
    "\u000A" +
    (Lista.map[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                String](((a: (List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])))
                           =>
                          {
                            val (uid, aa):
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))
                              = a
                            val (ab, b):
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])
                              = aa;
                            ({
                               val (from, to): (Nat.nat, Nat.nat) = ab;
                               ((t: Transition.transition_ext[Unit]) =>
                                 "  s" +
                                   Code_Numeral.integer_of_nat(from).toString() +
                                   "->s" +
                                   Code_Numeral.integer_of_nat(to).toString() +
                                   "[label=<<i> [" +
                                   show_nats(Lista.sort_key[Nat.nat,
                     Nat.nat](((x: Nat.nat) => x), uid)) +
                                   "]" +
                                   transition2dot(t) +
                                   "</i>>];")
                             })(b)
                          }),
                         FSet.sorted_list_of_fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat),
              Transition.transition_ext[Unit]))](e))).mkString("\u000A") +
    "\u000A" +
    "}"

} /* object EFSM_Dot */

object Group_By {

def group_by[A](f: A => A => Boolean, x1: List[A]): List[List[A]] = (f, x1)
  match {
  case (f, Nil) => Nil
  case (f, (h::t)) =>
    {
      val group: List[A] = Lista.takeWhile[A](f(h), t)
      val dropped: List[A] = Lista.drop[A](Nat.Nata(group.par.length), t);
      (((h::group))::(group_by[A](f, dropped)))
    }
}

} /* object Group_By */

object SelectionStrategies {

def leaves(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
            e: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t2ID);
    (if ((Transition.Label[Unit](t1) ==
           Transition.Label[Unit](t2)) && ((Nat.equal_nata(Transition.Arity[Unit](t1),
                    Transition.Arity[Unit](t2))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).par.length),
                             Nat.Nata((Transition.Outputs[Unit](t2)).par.length)))))
      Nat.plus_nata(Inference.origin(t1ID, e), Inference.origin(t2ID, e))
      else Nat.zero_nata)
  }

def naive_score(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                 e: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t2ID);
    Inference.bool2nat((Transition.Label[Unit](t1) ==
                         Transition.Label[Unit](t2)) && ((Nat.equal_nata(Transition.Arity[Unit](t1),
                                  Transition.Arity[Unit](t2))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).par.length),
   Nat.Nata((Transition.Outputs[Unit](t2)).par.length)))))
  }

def exactly_equal(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                   e: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  Inference.bool2nat(Transition.equal_transition_exta[Unit](Inference.get_by_ids(e,
  t1ID),
                     Inference.get_by_ids(e, t2ID)))

def naive_score_outputs(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                         e: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t2ID);
    Nat.plus_nata(Nat.plus_nata(Inference.bool2nat(Transition.Label[Unit](t1) ==
             Transition.Label[Unit](t2)),
                                 Inference.bool2nat(Nat.equal_nata(Transition.Arity[Unit](t1),
                            Transition.Arity[Unit](t2)))),
                   Inference.bool2nat(Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t1),
 Transition.Outputs[Unit](t2))))
  }

def naive_score_eq_bonus(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                          e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t1ID)
    val a: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t2ID);
    Inference.score_transitions(t1, a)
  }

def naive_score_comprehensive(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                               e: FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t2ID);
    (if ((Transition.Label[Unit](t1) ==
           Transition.Label[Unit](t2)) && (Nat.equal_nata(Transition.Arity[Unit](t1),
                   Transition.Arity[Unit](t2))))
      (if (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).par.length),
                           Nat.Nata((Transition.Outputs[Unit](t2)).par.length)))
        Nat.plus_nata(Finite_Set.card[GExp.gexp[VName.vname]](Set.inf_set[GExp.gexp[VName.vname]](Set.seta[GExp.gexp[VName.vname]](Transition.Guards[Unit](t1)),
                   Set.seta[GExp.gexp[VName.vname]](Transition.Guards[Unit](t2)))),
                       Nat.Nata((Lista.filter[(AExp.aexp[VName.vname],
        AExp.aexp[VName.vname])](((a: (AExp.aexp[VName.vname],
AExp.aexp[VName.vname]))
                                    =>
                                   {
                                     val (aa, b):
   (AExp.aexp[VName.vname], AExp.aexp[VName.vname])
                                       = a;
                                     AExp.equal_aexpa[VName.vname](aa, b)
                                   }),
                                  (Transition.Outputs[Unit](t1)).par.zip(Transition.Outputs[Unit](t2)).toList)).par.length))
        else Nat.zero_nata)
      else Nat.zero_nata)
  }

def naive_score_comprehensive_eq_high(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                                       e:
 FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t2ID);
    (if (Transition.equal_transition_exta[Unit](t1, t2))
      Code_Numeral.nat_of_integer(BigInt(100))
      else (if ((Transition.Label[Unit](t1) ==
                  Transition.Label[Unit](t2)) && (Nat.equal_nata(Transition.Arity[Unit](t1),
                          Transition.Arity[Unit](t2))))
             (if (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).par.length),
                                  Nat.Nata((Transition.Outputs[Unit](t2)).par.length)))
               Nat.plus_nata(Finite_Set.card[GExp.gexp[VName.vname]](Set.inf_set[GExp.gexp[VName.vname]](Set.seta[GExp.gexp[VName.vname]](Transition.Guards[Unit](t1)),
                          Set.seta[GExp.gexp[VName.vname]](Transition.Guards[Unit](t2)))),
                              Nat.Nata((Lista.filter[(AExp.aexp[VName.vname],
               AExp.aexp[VName.vname])](((a:
    (AExp.aexp[VName.vname], AExp.aexp[VName.vname]))
   =>
  {
    val (aa, b): (AExp.aexp[VName.vname], AExp.aexp[VName.vname]) = a;
    AExp.equal_aexpa[VName.vname](aa, b)
  }),
 (Transition.Outputs[Unit](t1)).par.zip(Transition.Outputs[Unit](t2)).toList)).par.length))
               else Nat.zero_nata)
             else Nat.zero_nata))
  }

} /* object SelectionStrategies */

object Basic_BNF_LFPs {

def size_prod[A, B](x0: (A, B)): Nat.nat = x0 match {
  case (x1, x2) => Nat.Suc(Nat.zero_nata)
}

} /* object Basic_BNF_LFPs */

object Blue_Fringe {

abstract sealed class colour
final case class Red() extends colour
final case class Blue() extends colour
final case class White() extends colour

def equal_colour(x0: colour, x1: colour): Boolean = (x0, x1) match {
  case (Blue(), White()) => false
  case (White(), Blue()) => false
  case (Red(), White()) => false
  case (White(), Red()) => false
  case (Red(), Blue()) => false
  case (Blue(), Red()) => false
  case (White(), White()) => true
  case (Blue(), Blue()) => true
  case (Red(), Red()) => true
}

def show_colour(x0: colour): String = x0 match {
  case Red() => "red"
  case Blue() => "royalblue"
  case White() => "white"
}

def iefsm2dot_red_blue(e: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                        f: Map[Nat.nat, colour]):
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
    show_colour(f(Nat.zero_nata)) +
    "\"" +
    ", label=<s<sub>0</sub>>];" +
    "\u000A" +
    (Lista.map[Nat.nat,
                String](((s: Nat.nat) =>
                          "  s" + Code_Numeral.integer_of_nat(s).toString() +
                            "[fillcolor=" +
                            "\"" +
                            show_colour(f(s)) +
                            "\"" +
                            "label=<s<sub>" +
                            Code_Numeral.integer_of_nat(s).toString() +
                            "</sub>>];"),
                         FSet.sorted_list_of_fset[Nat.nat](FSet_Utils.fremove[Nat.nat](Nat.zero_nata,
        Inference.S(e))))).mkString("\u000A") +
    "\u000A" +
    "\u000A" +
    (Lista.map[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                String](((a: (List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])))
                           =>
                          {
                            val (uid, aa):
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))
                              = a
                            val (ab, b):
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])
                              = aa;
                            ({
                               val (from, to): (Nat.nat, Nat.nat) = ab;
                               ((t: Transition.transition_ext[Unit]) =>
                                 "  s" +
                                   Code_Numeral.integer_of_nat(from).toString() +
                                   "->s" +
                                   Code_Numeral.integer_of_nat(to).toString() +
                                   "[label=<<i> [" +
                                   EFSM_Dot.show_nats(Lista.sort_key[Nat.nat,
                              Nat.nat](((x: Nat.nat) => x), uid)) +
                                   "]" +
                                   EFSM_Dot.transition2dot(t) +
                                   "</i>>];")
                             })(b)
                          }),
                         FSet.sorted_list_of_fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat),
              Transition.transition_ext[Unit]))](e))).mkString("\u000A") +
    "\u000A" +
    "}"

def inference_step(f: Map[Nat.nat, colour],
                    e: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                    scores: FSet.fset[Inference.score_ext[Unit]],
                    m: (List[Nat.nat]) =>
                         (List[Nat.nat]) =>
                           Nat.nat =>
                             (FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                               (FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 (FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                   ((FSet.fset[((Nat.nat, Nat.nat),
         Transition.transition_ext[Unit])]) =>
                                     Boolean) =>
                                     Option[FSet.fset[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                    check:
                      (FSet.fset[((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])]) =>
                        Boolean,
                    np: (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], List[Nat.nat]),
  (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (if (FSet.equal_fseta[Inference.score_ext[Unit]](scores,
            FSet.bot_fset[Inference.score_ext[Unit]]))
    e else {
             val scoresa: FSet.fset[Inference.score_ext[Unit]] =
               FSet.ffilter[Inference.score_ext[Unit]](((s:
                   Inference.score_ext[Unit])
                  =>
                 (FSet.fmember[Nat.nat](Inference.S1[Unit](s),
 Inference.S(e))) && (FSet.fmember[Nat.nat](Inference.S2[Unit](s),
     Inference.S(e)))),
                scores);
             (if (FSet.equal_fseta[Inference.score_ext[Unit]](scoresa,
                       FSet.bot_fset[Inference.score_ext[Unit]]))
               e else {
                        val h: Inference.score_ext[Unit] =
                          FSet.fMin[Inference.score_ext[Unit]](scoresa)
                        val t: FSet.fset[Inference.score_ext[Unit]] =
                          FSet_Utils.fremove[Inference.score_ext[Unit]](h,
                                 scoresa);
                        (Inference.merge(Set.bot_set[(Nat.nat, Nat.nat)], e,
  Inference.S1[Unit](h), Inference.S2[Unit](h), m, check, np)
                           match {
                           case (None, _) =>
                             inference_step(f, e, t, m, check, np)
                           case (Some(newa), _) =>
                             inference_step(f, newa, t, m, check, np)
                         })
                      })
           })

def score_state_pair(tidsa: FSet.fset[List[Nat.nat]],
                      tids: FSet.fset[List[Nat.nat]],
                      e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                      strat:
                        (List[Nat.nat]) =>
                          (List[Nat.nat]) =>
                            (FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                              Nat.nat):
      Nat.nat
  =
  FSet_Utils.fSum[Nat.nat](FSet.fimage[(List[Nat.nat], List[Nat.nat]),
Nat.nat](((a: (List[Nat.nat], List[Nat.nat])) =>
           {
             val (t, ta): (List[Nat.nat], List[Nat.nat]) = a;
             ((strat(t))(ta))(e)
           }),
          FSet_Utils.fprod[List[Nat.nat], List[Nat.nat]](tidsa, tids)))

def score(f: Map[Nat.nat, colour],
           e: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
           strat:
             (List[Nat.nat]) =>
               (List[Nat.nat]) =>
                 (FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                   Nat.nat):
      FSet.fset[Inference.score_ext[Unit]]
  =
  {
    val states_transitions: FSet.fset[(Nat.nat, FSet.fset[List[Nat.nat]])] =
      FSet.fimage[Nat.nat,
                   (Nat.nat,
                     FSet.fset[List[Nat.nat]])](((s: Nat.nat) =>
          (s, FSet.fimage[(Nat.nat,
                            (Transition.transition_ext[Unit], List[Nat.nat])),
                           List[Nat.nat]](Fun.comp[(Transition.transition_ext[Unit],
             List[Nat.nat]),
            List[Nat.nat],
            (Nat.nat,
              (Transition.transition_ext[Unit],
                List[Nat.nat]))](((a: (Transition.transition_ext[Unit],
List[Nat.nat]))
                                    =>
                                   a._2),
                                  ((a: (Nat.nat,
 (Transition.transition_ext[Unit], List[Nat.nat])))
                                     =>
                                    a._2)),
   Inference.outgoing_transitions(s, e)))),
         Inference.S(e))
    val red: FSet.fset[(Nat.nat, FSet.fset[List[Nat.nat]])] =
      FSet.ffilter[(Nat.nat,
                     FSet.fset[List[Nat.nat]])](((a:
            (Nat.nat, FSet.fset[List[Nat.nat]]))
           =>
          {
            val (s, _): (Nat.nat, FSet.fset[List[Nat.nat]]) = a;
            equal_colour(f(s), Red())
          }),
         states_transitions)
    val blue: FSet.fset[(Nat.nat, FSet.fset[List[Nat.nat]])] =
      FSet.ffilter[(Nat.nat,
                     FSet.fset[List[Nat.nat]])](((a:
            (Nat.nat, FSet.fset[List[Nat.nat]]))
           =>
          {
            val (s, _): (Nat.nat, FSet.fset[List[Nat.nat]]) = a;
            equal_colour(f(s), Blue())
          }),
         states_transitions)
    val pairs:
          FSet.fset[((Nat.nat, FSet.fset[List[Nat.nat]]),
                      (Nat.nat, FSet.fset[List[Nat.nat]]))]
      = FSet_Utils.fprod[(Nat.nat, FSet.fset[List[Nat.nat]]),
                          (Nat.nat, FSet.fset[List[Nat.nat]])](red, blue)
    val bonus_scores: FSet.fset[Inference.score_ext[Unit]] =
      Inference.bonus_score(e);
    FSet.ffilter[Inference.score_ext[Unit]](((s: Inference.score_ext[Unit]) =>
      Nat.less_nat(Nat.zero_nata, Inference.Score[Unit](s))),
     Inference.scoreboard_add(bonus_scores,
                               FSet.fimage[((Nat.nat, FSet.fset[List[Nat.nat]]),
     (Nat.nat, FSet.fset[List[Nat.nat]])),
    Inference.score_ext[Unit]](((a: ((Nat.nat, FSet.fset[List[Nat.nat]]),
                                      (Nat.nat, FSet.fset[List[Nat.nat]])))
                                  =>
                                 {
                                   val (aa, b):
 ((Nat.nat, FSet.fset[List[Nat.nat]]), (Nat.nat, FSet.fset[List[Nat.nat]]))
                                     = a;
                                   ({
                                      val
(rs, rt): (Nat.nat, FSet.fset[List[Nat.nat]]) = aa;
                                      ((ab: (Nat.nat, FSet.fset[List[Nat.nat]]))
 =>
{
  val (bs, bt): (Nat.nat, FSet.fset[List[Nat.nat]]) = ab;
  Inference.score_exta[Unit](score_state_pair(rt, bt, e, strat), rs, bs, ())
})
                                    })(b)
                                 }),
                                pairs)))
  }

def infer(f: Map[Nat.nat, colour],
           e: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
           r: (List[Nat.nat]) =>
                (List[Nat.nat]) =>
                  (FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]) =>
                    Nat.nat,
           m: (List[Nat.nat]) =>
                (List[Nat.nat]) =>
                  Nat.nat =>
                    (FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          ((FSet.fset[((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])]) =>
                            Boolean) =>
                            Option[FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
           check:
             (FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit])]) =>
               Boolean,
           np: (FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]) =>
                 FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit],
                                  List[Nat.nat]),
                                 (Transition.transition_ext[Unit],
                                   List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    iefsm2dot_red_blue(e, f)
    val scores: FSet.fset[Inference.score_ext[Unit]] = score(f, e, r)
    val newa: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
      = inference_step(f, e, scores, m, check, np)
    val all_red: Map[Nat.nat, colour] =
      Lista.fold[Nat.nat,
                  Map[Nat.nat, colour]](((c: Nat.nat) =>
  (acc: Map[Nat.nat, colour]) => (acc + ((c -> (Red()))))),
 f.keySet.toList, f)
    val new_blue_states: FSet.fset[Nat.nat] =
      FSet.fimage[(Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])),
                   Nat.nat](((a: (Nat.nat,
                                   (Transition.transition_ext[Unit],
                                     List[Nat.nat])))
                               =>
                              a._1),
                             Lista.fold[Nat.nat,
 FSet.fset[(Nat.nat,
             (Transition.transition_ext[Unit],
               List[Nat.nat]))]](Fun.comp[FSet.fset[(Nat.nat,
              (Transition.transition_ext[Unit], List[Nat.nat]))],
   (FSet.fset[(Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat]))]) =>
     FSet.fset[(Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat]))],
   Nat.nat](((a: FSet.fset[(Nat.nat,
                             (Transition.transition_ext[Unit], List[Nat.nat]))])
               =>
              (b: FSet.fset[(Nat.nat,
                              (Transition.transition_ext[Unit],
                                List[Nat.nat]))])
                =>
              FSet.sup_fset[(Nat.nat,
                              (Transition.transition_ext[Unit],
                                List[Nat.nat]))](a, b)),
             ((s: Nat.nat) => Inference.outgoing_transitions(s, e))),
                                  all_red.keySet.toList,
                                  FSet.bot_fset[(Nat.nat,
          (Transition.transition_ext[Unit], List[Nat.nat]))]))
    val new_blue_children: Map[Nat.nat, colour] =
      Lista.fold[Nat.nat,
                  Map[Nat.nat, colour]](((s: Nat.nat) =>
  (acc: Map[Nat.nat, colour]) =>
  (if (equal_colour(acc(s), White())) (acc + ((s -> (Blue())))) else acc)),
 FSet.sorted_list_of_fset[Nat.nat](new_blue_states), all_red);
    Log.logBFStates(newa, new_blue_children, (FSet.size_fset[Nat.nat](Inference.S(e))));
    (if (FSet.less_fset[Nat.nat](FSet.ffilter[Nat.nat](((s: Nat.nat) =>
                 equal_colour(new_blue_children(s), White())),
                Inference.S(newa)),
                                  FSet.ffilter[Nat.nat](((s: Nat.nat) =>
                  equal_colour(f(s), White())),
                 Inference.S(e))))
      infer(new_blue_children, newa, r, m, check, np) else e)
  }

def learn(n: Nat.nat,
           pta: FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))],
           l: List[List[(String, (List[Value.value], List[Value.value]))]],
           r: (List[Nat.nat]) =>
                (List[Nat.nat]) =>
                  (FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]) =>
                    Nat.nat,
           m: (List[Nat.nat]) =>
                (List[Nat.nat]) =>
                  Nat.nat =>
                    (FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          ((FSet.fset[((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])]) =>
                            Boolean) =>
                            Option[FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
           np: (FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]) =>
                 FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit],
                                  List[Nat.nat]),
                                 (Transition.transition_ext[Unit],
                                   List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val check:
          (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
            Boolean
      = ((a: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])])
           =>
          EFSM.accepts_log(Set.seta[List[(String,
   (List[Value.value], List[Value.value]))]](l),
                            a))
    val blue_states: FSet.fset[Nat.nat] =
      FSet.fimage[(Nat.nat, (Transition.transition_ext[Unit], List[Nat.nat])),
                   Nat.nat](((a: (Nat.nat,
                                   (Transition.transition_ext[Unit],
                                     List[Nat.nat])))
                               =>
                              a._1),
                             Inference.outgoing_transitions(Nat.zero_nata, pta))
    val colours: Map[Nat.nat, colour] =
      Lista.fold[Nat.nat,
                  Map[Nat.nat, colour]](((s: Nat.nat) =>
  (acc: Map[Nat.nat, colour]) => (acc + ((s -> (Blue()))))),
 FSet.sorted_list_of_fset[Nat.nat](blue_states),
 ((scala.collection.immutable.Map().withDefaultValue(White())) + ((Nat.zero_nata -> (Red())))));
    infer(colours, pta, r, m, check, np)
  }

def score_merge_size(rt: List[Nat.nat], bt: List[Nat.nat],
                      e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  (if (Nat.equal_nata(SelectionStrategies.naive_score(rt, bt, e),
                       Nat.zero_nata))
    Nat.zero_nata
    else Nat.minus_nat(FSet.size_fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](e),
                        Basic_BNF_LFPs.size_prod[Option[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]],
          Set.set[(Nat.nat,
                    Nat.nat)]](Inference.merge(Set.bot_set[(Nat.nat, Nat.nat)],
        e, Inference.origin(rt, e), Inference.origin(bt, e),
        ((_: List[Nat.nat]) => (_: List[Nat.nat]) => (_: Nat.nat) =>
          (_: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))])
            =>
          (_: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))])
            =>
          (_: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))])
            =>
          (_: (FSet.fset[((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit])]) =>
                Boolean)
            =>
          None),
        ((_: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])])
           =>
          true),
        ((a: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))])
           =>
          Inference.nondeterministic_pairs(a))))))

} /* object Blue_Fringe */

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
  case (a, (h::t)) =>
    (if (HOL.eq[A](a, h)) Nat.plus_nata(Nat.Nata((1)), count[A](a, t))
      else count[A](a, t))
}

def index(x0: List[Value.value], uu: Nat.nat, uv: ioTag, uw: Nat.nat):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  (x0, uu, uv, uw) match {
  case (Nil, uu, uv, uw) => FSet.bot_fset[(Nat.nat, (ioTag, Nat.nat))]
  case ((h::t), actionNo, io, ind) =>
    FSet.finsert[(Nat.nat,
                   (ioTag,
                     Nat.nat))]((actionNo, (io, ind)),
                                 index(t, actionNo, io,
Nat.plus_nata(ind, Nat.Nata((1)))))
}

def i_step(tr: List[(String, List[Value.value])],
            e: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))],
            s: Nat.nat, r: Map[Nat.nat, Option[Value.value]], l: String,
            i: List[Value.value]):
      Option[(Transition.transition_ext[Unit],
               (Nat.nat, (List[Nat.nat], Map[Nat.nat, Option[Value.value]])))]
  =
  {
    val poss_steps:
          FSet.fset[(List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))]
      = Inference.i_possible_steps(e, s, r, l, i)
    val possibilities:
          FSet.fset[(List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))]
      = FSet.ffilter[(List[Nat.nat],
                       (Nat.nat,
                         Transition.transition_ext[Unit]))](((a:
                        (List[Nat.nat],
                          (Nat.nat, Transition.transition_ext[Unit])))
                       =>
                      {
                        val (_, (sa, t)):
                              (List[Nat.nat],
                                (Nat.nat, Transition.transition_ext[Unit]))
                          = a;
                        EFSM.recognises_execution(Inference.tm(e), sa,
           (Transition.apply_updates(Transition.Updates[Unit](t),
                                      AExp.join_ir(i, r))).apply(r),
           tr)
                      }),
                     poss_steps);
    (Dirties.randomMember[(List[Nat.nat],
                            (Nat.nat,
                              Transition.transition_ext[Unit]))](possibilities)
       match {
       case None => None
       case Some((u, (sa, t))) =>
         Some[(Transition.transition_ext[Unit],
                (Nat.nat,
                  (List[Nat.nat],
                    Map[Nat.nat, Option[Value.value]])))]((t,
                    (sa, (u, (Transition.apply_updates(Transition.Updates[Unit](t),
                AExp.join_ir(i, r))).apply(r)))))
     })
  }

def lookup(x0: (Nat.nat, (ioTag, Nat.nat)),
            t: List[(String, (List[Value.value], List[Value.value]))]):
      Value.value
  =
  (x0, t) match {
  case ((actionNo, (In(), inx)), t) =>
    {
      val (_, (inputs, _)): (String, (List[Value.value], List[Value.value])) =
        t(Code_Numeral.integer_of_nat(actionNo).toInt);
      inputs(Code_Numeral.integer_of_nat(inx).toInt)
    }
  case ((actionNo, (Out(), inx)), t) =>
    {
      val (_, (_, outputs)): (String, (List[Value.value], List[Value.value])) =
        t(Code_Numeral.integer_of_nat(actionNo).toInt);
      outputs(Code_Numeral.integer_of_nat(inx).toInt)
    }
}

def remove_guard_add_update(t: Transition.transition_ext[Unit], inputX: Nat.nat,
                             outputX: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    Lista.filter[GExp.gexp[VName.vname]](((g:
                                     GExp.gexp[VName.vname])
                                    =>
                                   ! (GExp.gexp_constrains[VName.vname](g,
                                 AExp.V[VName.vname](VName.I(inputX))))),
                                  Transition.Guards[Unit](t)),
                                    Transition.Outputs[Unit](t),
                                    ((outputX,
                                       AExp.V[VName.vname](VName.I(inputX)))::(Transition.Updates[Unit](t))),
                                    ())

def replaceAll(e: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
                old: Transition.transition_ext[Unit],
                newa: Transition.transition_ext[Unit]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, aa):
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a
                  val (ab, b):
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                    = aa;
                  ({
                     val (from, dest): (Nat.nat, Nat.nat) = ab;
                     ((t: Transition.transition_ext[Unit]) =>
                       (if (Transition.equal_transition_exta[Unit](t, old))
                         (uid, ((from, dest), newa))
                         else (uid, ((from, dest), t))))
                   })(b)
                }),
               e)

def generalise_transitions(x0: List[((((Transition.transition_ext[Unit],
 List[Nat.nat]),
(ioTag, Nat.nat)),
                                       ((Transition.transition_ext[Unit],
  List[Nat.nat]),
 (ioTag, Nat.nat))),
                                      (((Transition.transition_ext[Unit],
  List[Nat.nat]),
 (ioTag, Nat.nat)),
((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))))],
                            e: FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (x0, e) match {
  case (Nil, e) => e
  case ((h::t), e) =>
    {
      val a: ((((Transition.transition_ext[Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat))),
               (((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat))))
        = h
      val (aa, b):
            ((((Transition.transition_ext[Unit], List[Nat.nat]),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[Unit], List[Nat.nat]),
                 (ioTag, Nat.nat))),
              (((Transition.transition_ext[Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat))))
        = a;
      ({
         val (ab, ba):
               (((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))
           = aa;
         ({
            val (ac, bb):
                  ((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))
              = ab;
            ({
               val (orig1, _): (Transition.transition_ext[Unit], List[Nat.nat])
                 = ac;
               ((_: (ioTag, Nat.nat)) =>
                 (ad: ((Transition.transition_ext[Unit], List[Nat.nat]),
                        (ioTag, Nat.nat)))
                   =>
                 {
                   val (ae, bc):
                         ((Transition.transition_ext[Unit], List[Nat.nat]),
                           (ioTag, Nat.nat))
                     = ad;
                   ({
                      val (orig2, _):
                            (Transition.transition_ext[Unit], List[Nat.nat])
                        = ae;
                      ((_: (ioTag, Nat.nat)) =>
                        (af: (((Transition.transition_ext[Unit], List[Nat.nat]),
                                (ioTag, Nat.nat)),
                               ((Transition.transition_ext[Unit],
                                  List[Nat.nat]),
                                 (ioTag, Nat.nat))))
                          =>
                        {
                          val (ag, bd):
                                (((Transition.transition_ext[Unit],
                                    List[Nat.nat]),
                                   (ioTag, Nat.nat)),
                                  ((Transition.transition_ext[Unit],
                                     List[Nat.nat]),
                                    (ioTag, Nat.nat)))
                            = af;
                          ({
                             val (ah, be):
                                   ((Transition.transition_ext[Unit],
                                      List[Nat.nat]),
                                     (ioTag, Nat.nat))
                               = ag;
                             ({
                                val (gen1, _):
                                      (Transition.transition_ext[Unit],
List[Nat.nat])
                                  = ah;
                                ((_: (ioTag, Nat.nat)) =>
                                  (ai: ((Transition.transition_ext[Unit],
  List[Nat.nat]),
 (ioTag, Nat.nat)))
                                    =>
                                  {
                                    val (aj, bf):
  ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))
                                      = ai;
                                    ({
                                       val
 (gen2, _): (Transition.transition_ext[Unit], List[Nat.nat]) = aj;
                                       ((_: (ioTag, Nat.nat)) =>
 generalise_transitions(t, replaceAll(replaceAll(e, orig1, gen1), orig2, gen2)))
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

def generalise_output(t: Transition.transition_ext[Unit], regX: Nat.nat,
                       outputX: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    Transition.Guards[Unit](t),
                                    Lista.list_update[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t),
                                       outputX,
                                       AExp.V[VName.vname](VName.R(regX))),
                                    Transition.Updates[Unit](t), ())

def strip_uids(x: (((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat)))):
      ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
        (Transition.transition_ext[Unit], (ioTag, Nat.nat)))
  =
  {
    val a: (((Transition.transition_ext[Unit], List[Nat.nat]),
              (ioTag, Nat.nat)),
             ((Transition.transition_ext[Unit], List[Nat.nat]),
               (ioTag, Nat.nat)))
      = x
    val (aa, b):
          (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
            ((Transition.transition_ext[Unit], List[Nat.nat]),
              (ioTag, Nat.nat)))
      = a;
    ({
       val (ab, ba):
             ((Transition.transition_ext[Unit], List[Nat.nat]),
               (ioTag, Nat.nat))
         = aa;
       ({
          val (t1, _): (Transition.transition_ext[Unit], List[Nat.nat]) = ab;
          ((ac: (ioTag, Nat.nat)) =>
            {
              val (io1, in1): (ioTag, Nat.nat) = ac;
              ((ad: ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat)))
                 =>
                {
                  val (ae, bb):
                        ((Transition.transition_ext[Unit], List[Nat.nat]),
                          (ioTag, Nat.nat))
                    = ad;
                  ({
                     val (t2, _):
                           (Transition.transition_ext[Unit], List[Nat.nat])
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

def modify(matches:
             List[(((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat)))],
            u1: List[Nat.nat], u2: List[Nat.nat],
            old: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val relevant:
          List[(((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))]
      = Lista.filter[(((Transition.transition_ext[Unit], List[Nat.nat]),
                        (ioTag, Nat.nat)),
                       ((Transition.transition_ext[Unit], List[Nat.nat]),
                         (ioTag,
                           Nat.nat)))](((a:
   (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
     ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))))
  =>
 {
   val (aa, b):
         (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
           ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)))
     = a;
   ({
      val (ab, ba):
            ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))
        = aa;
      ({
         val (_, u1a): (Transition.transition_ext[Unit], List[Nat.nat]) = ab;
         ((ac: (ioTag, Nat.nat)) =>
           {
             val (io, _): (ioTag, Nat.nat) = ac;
             ((ad: ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)))
                =>
               {
                 val (ae, bb):
                       ((Transition.transition_ext[Unit], List[Nat.nat]),
                         (ioTag, Nat.nat))
                   = ad;
                 ({
                    val (_, u2a):
                          (Transition.transition_ext[Unit], List[Nat.nat])
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
    val newReg: Nat.nat = (Inference.max_reg(old) match {
                             case None => Nat.Nata((1))
                             case Some(r) => Nat.plus_nata(r, Nat.Nata((1)))
                           })
    val replacements:
          List[(((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat))),
                   (((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat)),
                     ((Transition.transition_ext[Unit], List[Nat.nat]),
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
   ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))))
=>
                                       {
 val (aa, b):
       (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
         ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)))
   = a;
 ({
    val (ab, ba):
          ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))
      = aa;
    ({
       val (t1, u1a): (Transition.transition_ext[Unit], List[Nat.nat]) = ab;
       ((ac: (ioTag, Nat.nat)) =>
         {
           val (io1, inx1): (ioTag, Nat.nat) = ac;
           ((ad: ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))
              =>
             {
               val (ae, bb):
                     ((Transition.transition_ext[Unit], List[Nat.nat]),
                       (ioTag, Nat.nat))
                 = ad;
               ({
                  val (t2, u2a):
                        (Transition.transition_ext[Unit], List[Nat.nat])
                    = ae;
                  ((af: (ioTag, Nat.nat)) =>
                    {
                      val (io2, inx2): (ioTag, Nat.nat) = af;
                      (((remove_guard_add_update(t1, inx1, newReg), u1a),
                         (io1, inx1)),
                        ((generalise_output(t2, newReg, inx2), u2a),
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
          List[((((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat))))]
      = relevant.par.zip(replacements).toList
    val stripped_replacements:
          List[((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                 (Transition.transition_ext[Unit], (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat))),
                   ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                     (Transition.transition_ext[Unit],
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
   ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))))
=>
                                       strip_uids(a)),
                                      replacements)
    val to_replace:
          List[((((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat))))]
      = Lista.filter[((((Transition.transition_ext[Unit], List[Nat.nat]),
                         (ioTag, Nat.nat)),
                        ((Transition.transition_ext[Unit], List[Nat.nat]),
                          (ioTag, Nat.nat))),
                       (((Transition.transition_ext[Unit], List[Nat.nat]),
                          (ioTag, Nat.nat)),
                         ((Transition.transition_ext[Unit], List[Nat.nat]),
                           (ioTag,
                             Nat.nat))))](((a:
      ((((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
         ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))),
        (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
          ((Transition.transition_ext[Unit], List[Nat.nat]),
            (ioTag, Nat.nat)))))
     =>
    {
      val (_, s):
            ((((Transition.transition_ext[Unit], List[Nat.nat]),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[Unit], List[Nat.nat]),
                 (ioTag, Nat.nat))),
              (((Transition.transition_ext[Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat))))
        = a;
      Nat.less_nat(Nat.Nata((1)),
                    count[((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                            (Transition.transition_ext[Unit],
                              (ioTag,
                                Nat.nat)))](strip_uids(s),
     stripped_replacements))
    }),
   comparisons);
    (if (to_replace.isEmpty) None
      else Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](generalise_transitions(to_replace,
          old)))
  }

def io_index(actionNo: Nat.nat, inputs: List[Value.value],
              outputs: List[Value.value]):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  FSet.sup_fset[(Nat.nat,
                  (ioTag,
                    Nat.nat))](index(inputs, actionNo, In(), Nat.zero_nata),
                                index(outputs, actionNo, Out(), Nat.zero_nata))

def indices(e: List[(String, (List[Value.value], List[Value.value]))]):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  Dirties.foldl[FSet.fset[(Nat.nat, (ioTag, Nat.nat))],
                 (Nat.nat,
                   (String,
                     (List[Value.value],
                       List[Value.value])))](((a:
         FSet.fset[(Nat.nat, (ioTag, Nat.nat))])
        =>
       (x: (Nat.nat, (String, (List[Value.value], List[Value.value])))) =>
       FSet.sup_fset[(Nat.nat,
                       (ioTag,
                         Nat.nat))](a, {
 val (actionNo, aa): (Nat.nat, (String, (List[Value.value], List[Value.value])))
   = x
 val (_, ab): (String, (List[Value.value], List[Value.value])) = aa
 val (ac, b): (List[Value.value], List[Value.value]) = ab;
 io_index(actionNo, ac, b)
                                       })),
      FSet.bot_fset[(Nat.nat, (ioTag, Nat.nat))],
      Lista.enumerate[(String,
                        (List[Value.value],
                          List[Value.value]))](Nat.zero_nata, e))

def remove_guards_add_update(t: Transition.transition_ext[Unit],
                              inputX: Nat.nat, outputX: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t), Nil,
                                    Transition.Outputs[Unit](t),
                                    ((outputX,
                                       AExp.V[VName.vname](VName.I(inputX)))::(Transition.Updates[Unit](t))),
                                    ())

def structural_count(uu: ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                           (Transition.transition_ext[Unit], (ioTag, Nat.nat))),
                      x1: List[((Transition.transition_ext[Unit],
                                  (ioTag, Nat.nat)),
                                 (Transition.transition_ext[Unit],
                                   (ioTag, Nat.nat)))]):
      Nat.nat
  =
  (uu, x1) match {
  case (uu, Nil) => Nat.zero_nata
  case (a, (((t1, (io1, i1)), (t2, (io2, i2)))::t)) =>
    {
      val b: ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
               (Transition.transition_ext[Unit], (ioTag, Nat.nat)))
        = a
      val (ba, c):
            ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
              (Transition.transition_ext[Unit], (ioTag, Nat.nat)))
        = b;
      ({
         val (t1a, (io1a, i1a)):
               (Transition.transition_ext[Unit], (ioTag, Nat.nat))
           = ba;
         ((bb: (Transition.transition_ext[Unit], (ioTag, Nat.nat))) =>
           {
             val (t2a, (io2a, i2a)):
                   (Transition.transition_ext[Unit], (ioTag, Nat.nat))
               = bb;
             (if ((Transition.same_structure(t1a,
      t1)) && ((Transition.same_structure(t2a,
   t2)) && ((equal_ioTaga(io1a,
                           io1)) && ((equal_ioTaga(io2a,
            io2)) && ((Nat.equal_nata(i1a, i1)) && (Nat.equal_nata(i2a,
                            i2)))))))
               Nat.plus_nata(Nat.Nata((1)), structural_count(a, t))
               else structural_count(a, t))
           })
       })(c)
    }
}

def generalise_input(t: Transition.transition_ext[Unit], r: Nat.nat,
                      i: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    Lista.map[GExp.gexp[VName.vname],
       GExp.gexp[VName.vname]](((g: GExp.gexp[VName.vname]) =>
                                 (g match {
                                    case GExp.Bc(_) => g
                                    case GExp.Eq(AExp.L(_), _) => g
                                    case GExp.Eq(AExp.V(VName.I(ia)), AExp.L(_))
                                      => (if (Nat.equal_nata(i, ia))
   GExp.Eq[VName.vname](AExp.V[VName.vname](VName.I(i)),
                         AExp.V[VName.vname](VName.R(r)))
   else g)
                                    case GExp.Eq(AExp.V(VName.I(_)), AExp.V(_))
                                      => g
                                    case GExp.Eq(AExp.V(VName.I(_)),
          AExp.Plus(_, _))
                                      => g
                                    case GExp.Eq(AExp.V(VName.I(_)),
          AExp.Minus(_, _))
                                      => g
                                    case GExp.Eq(AExp.V(VName.I(_)),
          AExp.Times(_, _))
                                      => g
                                    case GExp.Eq(AExp.V(VName.I(_)),
          AExp.Divide(_, _))
                                      => g
                                    case GExp.Eq(AExp.V(VName.R(_)), _) => g
                                    case GExp.Eq(AExp.Plus(_, _), _) => g
                                    case GExp.Eq(AExp.Minus(_, _), _) => g
                                    case GExp.Eq(AExp.Times(_, _), _) => g
                                    case GExp.Eq(AExp.Divide(_, _), _) => g
                                    case GExp.Gt(_, _) => g
                                    case GExp.In(_, _) => g
                                    case GExp.Nor(_, _) => g
                                  })),
                                Transition.Guards[Unit](t)),
                                    Transition.Outputs[Unit](t),
                                    Transition.Updates[Unit](t), ())

def modify_2(matches:
               List[(((Transition.transition_ext[Unit], List[Nat.nat]),
                       (ioTag, Nat.nat)),
                      ((Transition.transition_ext[Unit], List[Nat.nat]),
                        (ioTag, Nat.nat)))],
              u1: List[Nat.nat], u2: List[Nat.nat],
              old: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val relevant:
          List[(((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))]
      = Lista.filter[(((Transition.transition_ext[Unit], List[Nat.nat]),
                        (ioTag, Nat.nat)),
                       ((Transition.transition_ext[Unit], List[Nat.nat]),
                         (ioTag,
                           Nat.nat)))](((a:
   (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
     ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))))
  =>
 {
   val (aa, b):
         (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
           ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)))
     = a;
   ({
      val (ab, ba):
            ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))
        = aa;
      ({
         val (_, u1a): (Transition.transition_ext[Unit], List[Nat.nat]) = ab;
         ((ac: (ioTag, Nat.nat)) =>
           {
             val (io, _): (ioTag, Nat.nat) = ac;
             ((ad: ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)))
                =>
               {
                 val (ae, bb):
                       ((Transition.transition_ext[Unit], List[Nat.nat]),
                         (ioTag, Nat.nat))
                   = ad;
                 ({
                    val (_, u2a):
                          (Transition.transition_ext[Unit], List[Nat.nat])
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
    val newReg: Nat.nat = (Inference.max_reg(old) match {
                             case None => Nat.Nata((1))
                             case Some(r) => Nat.plus_nata(r, Nat.Nata((1)))
                           })
    val replacements:
          List[(((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat))),
                   (((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat)),
                     ((Transition.transition_ext[Unit], List[Nat.nat]),
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
   ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))))
=>
                                       {
 val (aa, b):
       (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
         ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)))
   = a;
 ({
    val (ab, ba):
          ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))
      = aa;
    ({
       val (t1, u1a): (Transition.transition_ext[Unit], List[Nat.nat]) = ab;
       ((ac: (ioTag, Nat.nat)) =>
         {
           val (io1, inx1): (ioTag, Nat.nat) = ac;
           ((ad: ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)))
              =>
             {
               val (ae, bb):
                     ((Transition.transition_ext[Unit], List[Nat.nat]),
                       (ioTag, Nat.nat))
                 = ad;
               ({
                  val (t2, u2a):
                        (Transition.transition_ext[Unit], List[Nat.nat])
                    = ae;
                  ((af: (ioTag, Nat.nat)) =>
                    {
                      val (io2, inx2): (ioTag, Nat.nat) = af;
                      (((remove_guards_add_update(t1, inx1, newReg), u1a),
                         (io1, inx1)),
                        ((generalise_input(t2, newReg, inx2), u2a),
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
          List[((((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat))))]
      = relevant.par.zip(replacements).toList
    val stripped_replacements:
          List[((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                 (Transition.transition_ext[Unit], (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (ioTag, Nat.nat))),
                   ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                     (Transition.transition_ext[Unit],
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
   ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))))
=>
                                       strip_uids(a)),
                                      replacements)
    val to_replace:
          List[((((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (ioTag, Nat.nat))))]
      = Lista.filter[((((Transition.transition_ext[Unit], List[Nat.nat]),
                         (ioTag, Nat.nat)),
                        ((Transition.transition_ext[Unit], List[Nat.nat]),
                          (ioTag, Nat.nat))),
                       (((Transition.transition_ext[Unit], List[Nat.nat]),
                          (ioTag, Nat.nat)),
                         ((Transition.transition_ext[Unit], List[Nat.nat]),
                           (ioTag,
                             Nat.nat))))](((a:
      ((((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
         ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))),
        (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
          ((Transition.transition_ext[Unit], List[Nat.nat]),
            (ioTag, Nat.nat)))))
     =>
    {
      val (_, s):
            ((((Transition.transition_ext[Unit], List[Nat.nat]),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[Unit], List[Nat.nat]),
                 (ioTag, Nat.nat))),
              (((Transition.transition_ext[Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat))))
        = a;
      Nat.less_nat(Nat.Nata((1)),
                    structural_count(strip_uids(s), stripped_replacements))
    }),
   comparisons);
    (if (to_replace.isEmpty) None
      else Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](generalise_transitions(to_replace,
          old)))
  }

def exec2trace[A, B, C](t: List[(A, (B, C))]): List[(A, B)] =
  Lista.map[(A, (B, C)),
             (A, B)](((a: (A, (B, C))) =>
                       {
                         val (label, (inputs, _)): (A, (B, C)) = a;
                         (label, inputs)
                       }),
                      t)

def walk_up_to(n: Nat.nat,
                e: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                s: Nat.nat, r: Map[Nat.nat, Option[Value.value]],
                x4: List[(String, (List[Value.value], List[Value.value]))]):
      (Transition.transition_ext[Unit], List[Nat.nat])
  =
  (n, e, s, r, x4) match {
  case (n, e, s, r, (h::t)) =>
    {
      val (Some((transition, (sa, (uid, updated))))):
            Option[(Transition.transition_ext[Unit],
                     (Nat.nat,
                       (List[Nat.nat], Map[Nat.nat, Option[Value.value]])))]
        = i_step(exec2trace[String, List[Value.value], List[Value.value]](t), e,
                  s, r, h._1, (h._2)._1);
      (if (Nat.equal_nata(n, Nat.zero_nata)) (transition, uid)
        else walk_up_to(Nat.minus_nat(n, Nat.Nata((1))), e, sa, updated, t))
    }
}

def get_by_id_intratrace_matches(e: List[(String,
   (List[Value.value], List[Value.value]))]):
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
                                     (Value.equal_valuea(lookup(aa, e),
                  lookup(b, e))) && ((Nat.less_eq_nat(aa._1,
               b._1)) && (! (Product_Type.equal_proda[Nat.nat,
               (ioTag, Nat.nat)](aa, b))))
                                   }),
                                  FSet_Utils.fprod[(Nat.nat, (ioTag, Nat.nat)),
            (Nat.nat, (ioTag, Nat.nat))](indices(e), indices(e)))

def find_intertrace_matches_aux(intras:
                                  FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
      (Nat.nat, (ioTag, Nat.nat)))],
                                 e: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                 t: List[(String,
   (List[Value.value], List[Value.value]))]):
      FSet.fset[(((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], List[Nat.nat]),
                    (ioTag, Nat.nat)))]
  =
  FSet.fimage[((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat))),
               (((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
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
    ((walk_up_to(e1, e, Nat.zero_nata,
                  scala.collection.immutable.Map().withDefaultValue(None), t),
       (io1, inx1)),
      (walk_up_to(e2, e, Nat.zero_nata,
                   scala.collection.immutable.Map().withDefaultValue(None), t),
        (io2, inx2)))
  })
                                      })(b)
                                   }),
                                  intras)

def find_intertrace_matches(l: List[List[(String,
   (List[Value.value], List[Value.value]))]],
                             e: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      List[(((Transition.transition_ext[Unit], List[Nat.nat]),
              (ioTag, Nat.nat)),
             ((Transition.transition_ext[Unit], List[Nat.nat]),
               (ioTag, Nat.nat)))]
  =
  Lista.filter[(((Transition.transition_ext[Unit], List[Nat.nat]),
                  (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], List[Nat.nat]),
                   (ioTag,
                     Nat.nat)))](((a: (((Transition.transition_ext[Unit],
  List[Nat.nat]),
 (ioTag, Nat.nat)),
((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))))
                                    =>
                                   {
                                     val (aa, b):
   (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
     ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)))
                                       = a;
                                     ({
val (e1, (_, _)):
      ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))
  = aa;
((ab: ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))) =>
  {
    val (e2, (_, _)):
          ((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat))
      = ab;
    ! (Product_Type.equal_proda[Transition.transition_ext[Unit],
                                 List[Nat.nat]](e1, e2))
  })
                                      })(b)
                                   }),
                                  Lista.maps[(List[(String,
             (List[Value.value], List[Value.value]))],
       FSet.fset[((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat)))]),
      (((Transition.transition_ext[Unit], List[Nat.nat]), (ioTag, Nat.nat)),
        ((Transition.transition_ext[Unit], List[Nat.nat]),
          (ioTag,
            Nat.nat)))](((a: (List[(String,
                                     (List[Value.value], List[Value.value]))],
                               FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
   (Nat.nat, (ioTag, Nat.nat)))]))
                           =>
                          {
                            val (t, m):
                                  (List[(String,
  (List[Value.value], List[Value.value]))],
                                    FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
        (Nat.nat, (ioTag, Nat.nat)))])
                              = a;
                            FSet.sorted_list_of_fset[(((Transition.transition_ext[Unit],
                 List[Nat.nat]),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[Unit], List[Nat.nat]),
                 (ioTag, Nat.nat)))](find_intertrace_matches_aux(m, e, t))
                          }),
                         l.par.zip(Lista.map[List[(String,
            (List[Value.value], List[Value.value]))],
      FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
                  (Nat.nat,
                    (ioTag,
                      Nat.nat)))]](((a: List[(String,
       (List[Value.value], List[Value.value]))])
                                      =>
                                     get_by_id_intratrace_matches(a)),
                                    l)).toList))

def heuristic_1(l: List[List[(String, (List[Value.value], List[Value.value]))]],
                 t1: List[Nat.nat], t2: List[Nat.nat], s: Nat.nat,
                 newa: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                 uu: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                 old: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                 check:
                   (FSet.fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])]) =>
                     Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (modify(find_intertrace_matches(l, old), t1, t2, newa) match {
     case None => None
     case Some(e) =>
       (if (check(Inference.tm(e)))
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](e)
         else None)
   })

def heuristic_2(l: List[List[(String, (List[Value.value], List[Value.value]))]],
                 t1: List[Nat.nat], t2: List[Nat.nat], s: Nat.nat,
                 newa: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                 uu: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                 old: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                 check:
                   (FSet.fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])]) =>
                     Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (modify_2(find_intertrace_matches(l, old), t1, t2, newa) match {
     case None => None
     case Some(e) =>
       (if (check(Inference.tm(e)))
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](e)
         else None)
   })

} /* object Store_Reuse */

object Run_Info_DOT {

def show_finfun_list(l: List[Map[Nat.nat, Option[Value.value]]]): String =
  "[" + (Lista.map[Map[Nat.nat, Option[Value.value]],
                    String](((a: Map[Nat.nat, Option[Value.value]]) =>
                              PrettyPrinter.dot(a)),
                             l)).mkString(", ") +
    "]"

def runinfo2dot(e: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                 run_info:
                   List[(Map[Nat.nat, Option[Value.value]],
                          (Nat.nat,
                            (Map[Nat.nat, Option[Value.value]],
                              (Map[Nat.nat, Option[Value.value]],
                                (List[Value.value],
                                  (List[Nat.nat],
                                    Transition.transition_ext[Unit]))))))]):
      String
  =
  {
    val state_targets: List[(Nat.nat, Map[Nat.nat, Option[Value.value]])] =
      Lista.map[(Map[Nat.nat, Option[Value.value]],
                  (Nat.nat,
                    (Map[Nat.nat, Option[Value.value]],
                      (Map[Nat.nat, Option[Value.value]],
                        (List[Value.value],
                          (List[Nat.nat], Transition.transition_ext[Unit])))))),
                 (Nat.nat,
                   Map[Nat.nat, Option[Value.value]])](((a:
                   (Map[Nat.nat, Option[Value.value]],
                     (Nat.nat,
                       (Map[Nat.nat, Option[Value.value]],
                         (Map[Nat.nat, Option[Value.value]],
                           (List[Value.value],
                             (List[Nat.nat],
                               Transition.transition_ext[Unit])))))))
                  =>
                 {
                   val (target, (state, _)):
                         (Map[Nat.nat, Option[Value.value]],
                           (Nat.nat,
                             (Map[Nat.nat, Option[Value.value]],
                               (Map[Nat.nat, Option[Value.value]],
                                 (List[Value.value],
                                   (List[Nat.nat],
                                     Transition.transition_ext[Unit]))))))
                     = a;
                   (state, target)
                 }),
                run_info)
    val state_targetsa: Nat.nat => List[Map[Nat.nat, Option[Value.value]]] =
      Lista.foldr[(Nat.nat, Map[Nat.nat, Option[Value.value]]),
                   Nat.nat =>
                     List[Map[Nat.nat, Option[Value.value]]]](((a:
                          (Nat.nat, Map[Nat.nat, Option[Value.value]]))
                         =>
                        {
                          val (state, target):
                                (Nat.nat, Map[Nat.nat, Option[Value.value]])
                            = a;
                          ((acc: Nat.nat =>
                                   List[Map[Nat.nat, Option[Value.value]]])
                             =>
                            Fun.fun_upd[Nat.nat,
 List[Map[Nat.nat, Option[Value.value]]]](acc, state, (target::(acc(state)))))
                        }),
                       state_targets, ((_: Nat.nat) => Nil));
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
      (Lista.map[Nat.nat,
                  String](((s: Nat.nat) =>
                            "  s" + Code_Numeral.integer_of_nat(s).toString() +
                              "[label=<s<sub>" +
                              Code_Numeral.integer_of_nat(s).toString() +
                              "</sub><br/>" +
                              show_finfun_list(state_targetsa(s)) +
                              ">];"),
                           FSet.sorted_list_of_fset[Nat.nat](Inference.S(e)))).mkString("\u000A") +
      "\u000A" +
      "\u000A" +
      (Lista.map[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                  String](((a: (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])))
                             =>
                            {
                              val (uid, aa):
                                    (List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))
                                = a
                              val (ab, b):
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])
                                = aa;
                              ({
                                 val (from, to): (Nat.nat, Nat.nat) = ab;
                                 ((t: Transition.transition_ext[Unit]) =>
                                   "  s" +
                                     Code_Numeral.integer_of_nat(from).toString() +
                                     "->s" +
                                     Code_Numeral.integer_of_nat(to).toString() +
                                     "[label=<<i> [" +
                                     EFSM_Dot.show_nats(Lista.sort_key[Nat.nat,
                                Nat.nat](((x: Nat.nat) => x), uid)) +
                                     "]" +
                                     EFSM_Dot.transition2dot(t) +
                                     "</i>>];")
                               })(b)
                            }),
                           FSet.sorted_list_of_fset[(List[Nat.nat],
              ((Nat.nat, Nat.nat),
                Transition.transition_ext[Unit]))](e))).mkString("\u000A") +
      "\u000A" +
      "}"
  }

} /* object Run_Info_DOT */

object Same_Register {

def replace_with(e: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))],
                  r1: Nat.nat, r2: Nat.nat):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (u, (tf, t)):
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a;
                  (u, (tf, Transition.rename_regs(Fun.fun_upd[Nat.nat,
                       Nat.nat](Fun.id[Nat.nat], r1, r2),
           t)))
                }),
               e)

def merge_if_same(e: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                   uu: (FSet.fset[((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])]) =>
                         Boolean,
                   x2: List[(Nat.nat, Nat.nat)]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (e, uu, x2) match {
  case (e, uu, Nil) => e
  case (e, check, ((r1, r2)::rs)) =>
    {
      val transitions: FSet.fset[Transition.transition_ext[Unit]] =
        FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                     Transition.transition_ext[Unit]](Fun.comp[((Nat.nat,
                          Nat.nat),
                         Transition.transition_ext[Unit]),
                        Transition.transition_ext[Unit],
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))](((a:
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))
                          =>
                         a._2),
                        ((a: (List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])))
                           =>
                          a._2)),
               e);
      (if (FSet.fBex[(Transition.transition_ext[Unit],
                       Transition.transition_ext[Unit])](FSet.ffilter[(Transition.transition_ext[Unit],
                                Transition.transition_ext[Unit])](((a:
                              (Transition.transition_ext[Unit],
                                Transition.transition_ext[Unit]))
                             =>
                            {
                              val (aa, b):
                                    (Transition.transition_ext[Unit],
                                      Transition.transition_ext[Unit])
                                = a;
                              Transition_Lexorder.less_transition_ext[Unit](aa,
                                     b)
                            }),
                           FSet_Utils.fprod[Transition.transition_ext[Unit],
     Transition.transition_ext[Unit]](transitions, transitions)),
                  ((a: (Transition.transition_ext[Unit],
                         Transition.transition_ext[Unit]))
                     =>
                    {
                      val (t1, t2):
                            (Transition.transition_ext[Unit],
                              Transition.transition_ext[Unit])
                        = a;
                      (Transition.same_structure(t1,
          t2)) && ((Set.member[Nat.nat](r1,
 Transition.enumerate_regs(t1))) && (Set.member[Nat.nat](r2,
                  Transition.enumerate_regs(t2))))
                    })))
        {
          val newE: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]
            = replace_with(e, r1, r2);
          (if (check(Inference.tm(newE))) merge_if_same(newE, check, rs)
            else merge_if_same(e, check, rs))
        }
        else merge_if_same(e, check, rs))
    }
}

def merge_regs(e: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
                check:
                  (FSet.fset[((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit])]) =>
                    Boolean):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val regs: Set.set[Nat.nat] = Inference.all_regs(e)
    val a: List[(Nat.nat, Nat.nat)] =
      Lista.sorted_list_of_set[(Nat.nat,
                                 Nat.nat)](Set.filter[(Nat.nat,
                Nat.nat)](((a: (Nat.nat, Nat.nat)) =>
                            {
                              val (aa, b): (Nat.nat, Nat.nat) = a;
                              Nat.less_nat(aa, b)
                            }),
                           Product_Type.product[Nat.nat, Nat.nat](regs, regs)));
    merge_if_same(e, check, a)
  }

def same_register(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                   newa: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                   uu: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   old: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                   check:
                     (FSet.fset[((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])]) =>
                       Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val newaa:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = merge_regs(newa, check);
    (if (FSet.equal_fseta[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))](newaa, newa))
      None
      else Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](newaa))
  }

} /* object Same_Register */

object Increment_Reset {

def guardMatch[A, B](t1: Transition.transition_ext[A],
                      t2: Transition.transition_ext[B]):
      Boolean
  =
  Code_Generation.guardMatch_code(Transition.Guards[A](t1),
                                   Transition.Guards[B](t2))

def outputMatch[A, B](t1: Transition.transition_ext[A],
                       t2: Transition.transition_ext[B]):
      Boolean
  =
  Code_Generation.outputMatch_code(Transition.Outputs[A](t1),
                                    Transition.Outputs[B](t2))

def initialiseReg(t: Transition.transition_ext[Unit], newReg: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    Transition.Guards[Unit](t),
                                    Transition.Outputs[Unit](t),
                                    ((newReg,
                                       AExp.L[VName.vname](Value.Inta(Int.zero_int)))::(Transition.Updates[Unit](t))),
                                    ())

def struct_replace_all(e: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                        old: Transition.transition_ext[Unit],
                        newa: Transition.transition_ext[Unit]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val to_replace:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = FSet.ffilter[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))](((a:
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])))
                       =>
                      {
                        val (_, aa):
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))
                          = a
                        val (ab, b):
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])
                          = aa;
                        ({
                           val (_, _): (Nat.nat, Nat.nat) = ab;
                           ((t: Transition.transition_ext[Unit]) =>
                             Transition.same_structure(t, old))
                         })(b)
                      }),
                     e)
    val replacements:
          FSet.fset[(List[Nat.nat], Transition.transition_ext[Unit])]
      = FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                     (List[Nat.nat],
                       Transition.transition_ext[Unit])](((a:
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                    =>
                   {
                     val (uid, aa):
                           (List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))
                       = a
                     val (ab, b):
                           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                       = aa;
                     ({
                        val (_, _): (Nat.nat, Nat.nat) = ab;
                        ((_: Transition.transition_ext[Unit]) => (uid, newa))
                      })(b)
                   }),
                  to_replace);
    Inference.replace_transitions(e, FSet.sorted_list_of_fset[(List[Nat.nat],
                        Transition.transition_ext[Unit])](replacements))
  }

def insert_increment_2(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                        newa: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                        uu: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                        old: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                        check:
                          (FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])]) =>
                            Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t2ID);
    (if ((guardMatch[Unit, Unit](t1, t2)) && (outputMatch[Unit, Unit](t1, t2)))
      {
        val r: Nat.nat = (Inference.max_reg(newa) match {
                            case None => Nat.Nata((1))
                            case Some(r) => Nat.plus_nata(r, Nat.Nata((1)))
                          })
        val newReg: VName.vname = VName.R(r)
        val newT1: Transition.transition_ext[Unit] =
          Transition.transition_exta[Unit](Transition.Label[Unit](t1),
    Transition.Arity[Unit](t1), Nil,
    ((AExp.Plus[VName.vname](AExp.V[VName.vname](newReg),
                              AExp.V[VName.vname](VName.I(Nat.zero_nata))))::Nil),
    ((r, AExp.Plus[VName.vname](AExp.V[VName.vname](newReg),
                                 AExp.V[VName.vname](VName.I(Nat.zero_nata))))::(Transition.Updates[Unit](t1))),
    ())
        val newT2: Transition.transition_ext[Unit] =
          Transition.transition_exta[Unit](Transition.Label[Unit](t2),
    Transition.Arity[Unit](t2), Nil,
    ((AExp.Plus[VName.vname](AExp.V[VName.vname](newReg),
                              AExp.V[VName.vname](VName.I(Nat.zero_nata))))::Nil),
    ((r, AExp.Plus[VName.vname](AExp.V[VName.vname](newReg),
                                 AExp.V[VName.vname](VName.I(Nat.zero_nata))))::(Transition.Updates[Unit](t2))),
    ())
        val to_initialise:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
          = FSet.ffilter[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))](((a:
                            (List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])))
                           =>
                          {
                            val (_, aa):
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))
                              = a
                            val (ab, b):
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])
                              = aa;
                            ({
                               val (_, to): (Nat.nat, Nat.nat) = ab;
                               ((t: Transition.transition_ext[Unit]) =>
                                 ((Nat.equal_nata(to,
           Inference.dest(t1ID,
                           newa))) || (Nat.equal_nata(to,
               Inference.dest(t2ID,
                               newa)))) && ((! (Transition.equal_transition_exta[Unit](t,
        t1))) && (! (Transition.equal_transition_exta[Unit](t, t2)))))
                             })(b)
                          }),
                         newa)
        val initialisedTrans:
              FSet.fset[(List[Nat.nat], Transition.transition_ext[Unit])]
          = FSet.fimage[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])),
                         (List[Nat.nat],
                           Transition.transition_ext[Unit])](((a:
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])))
                        =>
                       {
                         val (uid, aa):
                               (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))
                           = a
                         val (ab, b):
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])
                           = aa;
                         ({
                            val (_, _): (Nat.nat, Nat.nat) = ab;
                            ((t: Transition.transition_ext[Unit]) =>
                              (uid, initialiseReg(t, r)))
                          })(b)
                       }),
                      to_initialise)
        val initialised:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
          = Inference.replace_transitions(newa,
   FSet.sorted_list_of_fset[(List[Nat.nat],
                              Transition.transition_ext[Unit])](initialisedTrans))
        val rep: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]
          = struct_replace_all(struct_replace_all(initialised, t2, newT2), t1,
                                newT1);
        (if (check(Inference.tm(rep)))
          Some[FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]](rep)
          else None)
      }
      else None)
  }

} /* object Increment_Reset */

object Weak_Subsumption {

def maxBy[A, B : Orderings.linorder](f: A => B, a: A, b: A): A =
  (if (Orderings.less[B](f(b), f(a))) a else b)

def weak_subsumption(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                      newa: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                      uu: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                      old: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))],
                      check:
                        (FSet.fset[((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])]) =>
                          Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t2ID);
    (if (Transition.same_structure(t1, t2))
      {
        val maxT: Transition.transition_ext[Unit] =
          maxBy[Transition.transition_ext[Unit],
                 (Nat.nat,
                   List[AExp.aexp[VName.vname]])](((x:
              Transition.transition_ext[Unit])
             =>
            ((Fun.comp[List[(Nat.nat, AExp.aexp[VName.vname])], Nat.nat,
                        Transition.transition_ext[Unit]](((a:
                     List[(Nat.nat, AExp.aexp[VName.vname])])
                    =>
                   Nat.Nata(a.par.length)),
                  ((a: Transition.transition_ext[Unit]) =>
                    Transition.Updates[Unit](a)))).apply(x),
              Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
                         AExp.aexp[VName.vname]](((a:
             (Nat.nat, AExp.aexp[VName.vname]))
            =>
           a._2),
          Transition.Updates[Unit](x)))),
           t1, t2)
        val minT: Transition.transition_ext[Unit] =
          (if (Transition.equal_transition_exta[Unit](maxT, t1)) t2 else t1)
        val newEFSMmax:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
          = Inference.replace_all(newa, (t1ID::((t2ID::Nil))), maxT);
        (if (check(Inference.tm(newEFSMmax)))
          Some[FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]](newEFSMmax)
          else {
                 val newEFSMmin:
                       FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]
                   = Inference.replace_all(newa, (t1ID::((t2ID::Nil))), minT);
                 (if (check(Inference.tm(newEFSMmin)))
                   Some[FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]](newEFSMmin)
                   else None)
               })
      }
      else None)
  }

} /* object Weak_Subsumption */

object Least_Upper_Bound {

def literal_args[A](x0: GExp.gexp[A]): Boolean = x0 match {
  case GExp.Bc(v) => false
  case GExp.Eq(AExp.V(uu), AExp.L(uv)) => true
  case GExp.In(uw, ux) => true
  case GExp.Eq(AExp.L(v), uz) => false
  case GExp.Eq(AExp.Plus(v, va), uz) => false
  case GExp.Eq(AExp.Minus(v, va), uz) => false
  case GExp.Eq(AExp.Times(v, va), uz) => false
  case GExp.Eq(AExp.Divide(v, va), uz) => false
  case GExp.Eq(uy, AExp.V(v)) => false
  case GExp.Eq(uy, AExp.Plus(v, va)) => false
  case GExp.Eq(uy, AExp.Minus(v, va)) => false
  case GExp.Eq(uy, AExp.Times(v, va)) => false
  case GExp.Eq(uy, AExp.Divide(v, va)) => false
  case GExp.Gt(va, v) => false
  case GExp.Nor(v, va) => (literal_args[A](v)) && (literal_args[A](va))
}

def all_literal_args[A](t: Transition.transition_ext[A]): Boolean =
  Lista.list_all[GExp.gexp[VName.vname]](((a: GExp.gexp[VName.vname]) =>
   literal_args[VName.vname](a)),
  Transition.Guards[A](t))

def merge_in_in(v: VName.vname, l: List[Value.value],
                 x2: List[GExp.gexp[VName.vname]]):
      List[GExp.gexp[VName.vname]]
  =
  (v, l, x2) match {
  case (v, l, Nil) => ((GExp.In[VName.vname](v, l))::Nil)
  case (va, la, ((GExp.Eq(AExp.V(v), AExp.L(l)))::t)) =>
    (if (VName.equal_vnamea(va, v))
      ((GExp.In[VName.vname](va, Lista.insert[Value.value](l, la)))::t)
      else ((GExp.Eq[VName.vname](AExp.V[VName.vname](v),
                                   AExp.L[VName.vname](l)))::(merge_in_in(va,
                                   la, t))))
  case (va, la, ((GExp.In(v, l))::t)) =>
    (if (VName.equal_vnamea(va, v))
      ((GExp.In[VName.vname](va, Lista.union[Value.value].apply(la).apply(l)))::t)
      else ((GExp.In[VName.vname](v, l))::(merge_in_in(va, la, t))))
  case (v, l, ((GExp.Bc(va))::t)) =>
    ((GExp.Bc[VName.vname](va))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.L(vc), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.L[VName.vname](vc),
                            vb))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.Plus(vc, vd), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.Plus[VName.vname](vc, vd),
                            vb))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.Minus(vc, vd), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.Minus[VName.vname](vc, vd),
                            vb))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.Times(vc, vd), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.Times[VName.vname](vc, vd),
                            vb))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.Divide(vc, vd), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.Divide[VName.vname](vc, vd),
                            vb))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(va, AExp.V(vc)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.V[VName.vname](vc)))::(merge_in_in(v, l,
                                t)))
  case (v, l, ((GExp.Eq(va, AExp.Plus(vc, vd)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.Plus[VName.vname](vc,
               vd)))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(va, AExp.Minus(vc, vd)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.Minus[VName.vname](vc,
                vd)))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(va, AExp.Times(vc, vd)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.Times[VName.vname](vc,
                vd)))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Eq(va, AExp.Divide(vc, vd)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.Divide[VName.vname](vc,
                 vd)))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Gt(va, vb))::t)) =>
    ((GExp.Gt[VName.vname](va, vb))::(merge_in_in(v, l, t)))
  case (v, l, ((GExp.Nor(va, vb))::t)) =>
    ((GExp.Nor[VName.vname](va, vb))::(merge_in_in(v, l, t)))
}

def merge_in_eq(v: VName.vname, l: Value.value,
                 x2: List[GExp.gexp[VName.vname]]):
      List[GExp.gexp[VName.vname]]
  =
  (v, l, x2) match {
  case (v, l, Nil) =>
    ((GExp.Eq[VName.vname](AExp.V[VName.vname](v),
                            AExp.L[VName.vname](l)))::Nil)
  case (va, la, ((GExp.Eq(AExp.V(v), AExp.L(l)))::t)) =>
    (if ((VName.equal_vnamea(va, v)) && (! (Value.equal_valuea(la, l))))
      ((GExp.In[VName.vname](va, (la::((l::Nil)))))::t)
      else ((GExp.Eq[VName.vname](AExp.V[VName.vname](v),
                                   AExp.L[VName.vname](l)))::(merge_in_eq(va,
                                   la, t))))
  case (va, la, ((GExp.In(v, l))::t)) =>
    (if (VName.equal_vnamea(va, v))
      ((GExp.In[VName.vname](va, ((la::l)).par.distinct.toList))::t)
      else ((GExp.In[VName.vname](v, l))::(merge_in_eq(va, la, t))))
  case (v, l, ((GExp.Bc(va))::t)) =>
    ((GExp.Bc[VName.vname](va))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.L(vc), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.L[VName.vname](vc),
                            vb))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.Plus(vc, vd), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.Plus[VName.vname](vc, vd),
                            vb))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.Minus(vc, vd), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.Minus[VName.vname](vc, vd),
                            vb))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.Times(vc, vd), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.Times[VName.vname](vc, vd),
                            vb))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(AExp.Divide(vc, vd), vb))::t)) =>
    ((GExp.Eq[VName.vname](AExp.Divide[VName.vname](vc, vd),
                            vb))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(va, AExp.V(vc)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.V[VName.vname](vc)))::(merge_in_eq(v, l,
                                t)))
  case (v, l, ((GExp.Eq(va, AExp.Plus(vc, vd)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.Plus[VName.vname](vc,
               vd)))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(va, AExp.Minus(vc, vd)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.Minus[VName.vname](vc,
                vd)))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(va, AExp.Times(vc, vd)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.Times[VName.vname](vc,
                vd)))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Eq(va, AExp.Divide(vc, vd)))::t)) =>
    ((GExp.Eq[VName.vname](va, AExp.Divide[VName.vname](vc,
                 vd)))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Gt(va, vb))::t)) =>
    ((GExp.Gt[VName.vname](va, vb))::(merge_in_eq(v, l, t)))
  case (v, l, ((GExp.Nor(va, vb))::t)) =>
    ((GExp.Nor[VName.vname](va, vb))::(merge_in_eq(v, l, t)))
}

def merge_guards(x0: List[GExp.gexp[VName.vname]],
                  g2: List[GExp.gexp[VName.vname]]):
      List[GExp.gexp[VName.vname]]
  =
  (x0, g2) match {
  case (Nil, g2) => g2
  case (((GExp.Eq(AExp.V(v), AExp.L(l)))::t), g2) =>
    merge_guards(t, merge_in_eq(v, l, g2))
  case (((GExp.In(v, l))::t), g2) => merge_guards(t, merge_in_in(v, l, g2))
  case (((GExp.Bc(v))::t), g2) =>
    ((GExp.Bc[VName.vname](v))::(merge_guards(t, g2)))
  case (((GExp.Eq(AExp.L(vb), va))::t), g2) =>
    ((GExp.Eq[VName.vname](AExp.L[VName.vname](vb), va))::(merge_guards(t, g2)))
  case (((GExp.Eq(AExp.Plus(vb, vc), va))::t), g2) =>
    ((GExp.Eq[VName.vname](AExp.Plus[VName.vname](vb, vc),
                            va))::(merge_guards(t, g2)))
  case (((GExp.Eq(AExp.Minus(vb, vc), va))::t), g2) =>
    ((GExp.Eq[VName.vname](AExp.Minus[VName.vname](vb, vc),
                            va))::(merge_guards(t, g2)))
  case (((GExp.Eq(AExp.Times(vb, vc), va))::t), g2) =>
    ((GExp.Eq[VName.vname](AExp.Times[VName.vname](vb, vc),
                            va))::(merge_guards(t, g2)))
  case (((GExp.Eq(AExp.Divide(vb, vc), va))::t), g2) =>
    ((GExp.Eq[VName.vname](AExp.Divide[VName.vname](vb, vc),
                            va))::(merge_guards(t, g2)))
  case (((GExp.Eq(v, AExp.V(vb)))::t), g2) =>
    ((GExp.Eq[VName.vname](v, AExp.V[VName.vname](vb)))::(merge_guards(t, g2)))
  case (((GExp.Eq(v, AExp.Plus(vb, vc)))::t), g2) =>
    ((GExp.Eq[VName.vname](v, AExp.Plus[VName.vname](vb,
              vc)))::(merge_guards(t, g2)))
  case (((GExp.Eq(v, AExp.Minus(vb, vc)))::t), g2) =>
    ((GExp.Eq[VName.vname](v, AExp.Minus[VName.vname](vb,
               vc)))::(merge_guards(t, g2)))
  case (((GExp.Eq(v, AExp.Times(vb, vc)))::t), g2) =>
    ((GExp.Eq[VName.vname](v, AExp.Times[VName.vname](vb,
               vc)))::(merge_guards(t, g2)))
  case (((GExp.Eq(v, AExp.Divide(vb, vc)))::t), g2) =>
    ((GExp.Eq[VName.vname](v, AExp.Divide[VName.vname](vb,
                vc)))::(merge_guards(t, g2)))
  case (((GExp.Gt(v, va))::t), g2) =>
    ((GExp.Gt[VName.vname](v, va))::(merge_guards(t, g2)))
  case (((GExp.Nor(v, va))::t), g2) =>
    ((GExp.Nor[VName.vname](v, va))::(merge_guards(t, g2)))
}

def lob_aux(t1: Transition.transition_ext[Unit],
             t2: Transition.transition_ext[Unit]):
      Option[Transition.transition_ext[Unit]]
  =
  (if ((Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t1),
           Transition.Outputs[Unit](t2))) && ((Lista.equal_lista[(Nat.nat,
                           AExp.aexp[VName.vname])](Transition.Updates[Unit](t1),
             Transition.Updates[Unit](t2))) && ((all_literal_args[Unit](t1)) && (all_literal_args[Unit](t2)))))
    Some[Transition.transition_ext[Unit]](Transition.transition_exta[Unit](Transition.Label[Unit](t1),
                                    Transition.Arity[Unit](t1),
                                    (merge_guards(Transition.Guards[Unit](t1),
           Transition.Guards[Unit](t2))).par.distinct.toList,
                                    Transition.Outputs[Unit](t1),
                                    Transition.Updates[Unit](t1), ()))
    else None)

def lob(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
         newa: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))],
         uu: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
         old: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
         uv: (FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit])]) =>
               Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t2ID);
    (lob_aux(t1, t2) match {
       case None => None
       case Some(lob_t) =>
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](Inference.replace_transitions(newa,
               ((t1ID, lob_t)::(((t2ID, lob_t)::Nil)))))
     })
  }

} /* object Least_Upper_Bound */

object PTA_Generalisation {

abstract sealed class value_type
final case class I() extends value_type
final case class R() extends value_type
final case class S() extends value_type

def equal_value_typea(x0: value_type, x1: value_type): Boolean = (x0, x1) match
  {
  case (R(), S()) => false
  case (S(), R()) => false
  case (I(), S()) => false
  case (S(), I()) => false
  case (I(), R()) => false
  case (R(), I()) => false
  case (S(), S()) => true
  case (R(), R()) => true
  case (I(), I()) => true
}

def less_value_type(x0: value_type, uw: value_type): Boolean = (x0, uw) match {
  case (I(), I()) => false
  case (I(), R()) => true
  case (I(), S()) => true
  case (R(), S()) => true
  case (R(), I()) => false
  case (R(), R()) => false
  case (S(), uw) => false
}

def less_eq_value_type(v1: value_type, v2: value_type): Boolean =
  (less_value_type(v1, v2)) || (equal_value_typea(v1, v2))

abstract sealed class generalisation
final case class Failed(a: Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])])
  extends generalisation
final case class Succeeded(a: (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                (List[List[Nat.nat]],
                                  (Map[((String,
 (List[value_type],
   List[value_type]))), (List[(AExp.aexp[VName.vname],
                                Map[VName.vname, value_type])])],
                                    Map[((String,
  (List[value_type],
    List[value_type]))), (List[(AExp.aexp[VName.vname],
                                 Map[VName.vname, value_type])])]))))
  extends generalisation

abstract sealed class output_generalisation
final case class Success(a: (FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                              (Map[((String,
                                     (List[value_type],
                                       List[value_type]))), (List[(AExp.aexp[VName.vname],
                            Map[VName.vname, value_type])])],
                                (Map[((String,
                                       (List[value_type],
 List[value_type]))), (List[(AExp.aexp[VName.vname],
                              Map[VName.vname, value_type])])],
                                  (List[AExp.aexp[VName.vname]],
                                    Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])])))))
  extends output_generalisation
final case class Failure(a: Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])])
  extends output_generalisation

def thisa(x: generalisation):
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
        (List[List[Nat.nat]],
          (Map[((String,
                 (List[value_type],
                   List[value_type]))), (List[(AExp.aexp[VName.vname],
        Map[VName.vname, value_type])])],
            Map[((String,
                  (List[value_type],
                    List[value_type]))), (List[(AExp.aexp[VName.vname],
         Map[VName.vname, value_type])])])))
  =
  {
    val (Succeeded(y)): generalisation = x;
    y
  }

def target_fold[A, B, C, D,
                 E](tRegs: Map[Nat.nat, Option[Value.value]],
                     ts: List[(A, (B, (Map[Nat.nat, Option[Value.value]],
(C, (D, E)))))],
                     b: List[(Map[Nat.nat, Option[Value.value]],
                               (A, (B, (Map[Nat.nat, Option[Value.value]],
 (C, (D, E))))))]):
      List[(Map[Nat.nat, Option[Value.value]],
             (A, (B, (Map[Nat.nat, Option[Value.value]], (C, (D, E))))))]
  =
  (Lista.fold[(A, (B, (Map[Nat.nat, Option[Value.value]], (C, (D, E))))),
               (List[(Map[Nat.nat, Option[Value.value]],
                       (A, (B, (Map[Nat.nat, Option[Value.value]],
                                 (C, (D, E))))))],
                 Map[Nat.nat, Option[Value.value]])](((a:
                 (A, (B, (Map[Nat.nat, Option[Value.value]], (C, (D, E))))))
                =>
               {
                 val (s, (oldregs, (regs, (inputs, (tid, ta))))):
                       (A, (B, (Map[Nat.nat, Option[Value.value]],
                                 (C, (D, E)))))
                   = a;
                 ((aa: (List[(Map[Nat.nat, Option[Value.value]],
                               (A, (B, (Map[Nat.nat, Option[Value.value]],
 (C, (D, E))))))],
                         Map[Nat.nat, Option[Value.value]]))
                    =>
                   {
                     val (acc, tRegsa):
                           (List[(Map[Nat.nat, Option[Value.value]],
                                   (A, (B,
 (Map[Nat.nat, Option[Value.value]], (C, (D, E))))))],
                             Map[Nat.nat, Option[Value.value]])
                       = aa
                     val ab: Map[Nat.nat, Option[Value.value]] =
                       (if ((regs.keySet.toList).isEmpty) tRegsa else regs);
                     (acc ++
                        ((tRegsa,
                           (s, (oldregs, (regs, (inputs, (tid, ta))))))::Nil),
                       ab)
                   })
               }),
              ts, (b.par.reverse.toList, tRegs)))._1

def target(tRegs: Map[Nat.nat, Option[Value.value]],
            ts: List[(Nat.nat,
                       (Map[Nat.nat, Option[Value.value]],
                         (Map[Nat.nat, Option[Value.value]],
                           (List[Value.value],
                             (List[Nat.nat],
                               Transition.transition_ext[Unit])))))]):
      List[(Map[Nat.nat, Option[Value.value]],
             (Nat.nat,
               (Map[Nat.nat, Option[Value.value]],
                 (Map[Nat.nat, Option[Value.value]],
                   (List[Value.value],
                     (List[Nat.nat], Transition.transition_ext[Unit]))))))]
  =
  target_fold[Nat.nat, Map[Nat.nat, Option[Value.value]], List[Value.value],
               List[Nat.nat], Transition.transition_ext[Unit]](tRegs, ts, Nil)

def cartProdN[A](as: List[List[A]]): List[List[A]] =
  Lista.foldr[List[A],
               List[List[A]]](((xs: List[A]) => (asa: List[List[A]]) =>
                                Lista.maps[A,
    List[A]](((x: A) =>
               Lista.map[List[A], List[A]](((a: List[A]) => (x::a)), asa)),
              xs)),
                               as, (Nil::Nil))

def correct_row(a: AExp.aexp[VName.vname], values: List[Value.value],
                 i: List[Value.value], r: Map[Nat.nat, Option[Value.value]],
                 expected: Value.value, known: List[Nat.nat],
                 allowLatent: Boolean):
      Boolean
  =
  {
    val latent_vars: List[Nat.nat] =
      (if (! allowLatent) Nil
        else Lista.filter[Nat.nat](((x: Nat.nat) => ! (known.contains(x))),
                                    Lista.sorted_list_of_set[Nat.nat](AExp.enumerate_regs(a))))
    val valuations: List[List[Value.value]] =
      cartProdN[Value.value](AExp.repeat[List[Value.value]](Nat.Nata(latent_vars.par.length),
                     values))
    val assignments: List[List[(Nat.nat, Value.value)]] =
      Lista.map[List[Value.value],
                 List[(Nat.nat,
                        Value.value)]](((aa: List[Value.value]) =>
 latent_vars.par.zip(aa).toList),
valuations)
    val update:
          (List[(Nat.nat, Value.value)]) =>
            Map[Nat.nat, Option[Value.value]] =>
              Map[Nat.nat, Option[Value.value]]
      = ((aa: List[(Nat.nat, Value.value)]) =>
          (b: Map[Nat.nat, Option[Value.value]]) =>
          Lista.fold[(Nat.nat, Value.value),
                      Map[Nat.nat, Option[Value.value]]](((ab:
                     (Nat.nat, Value.value))
                    =>
                   {
                     val (reg, vala): (Nat.nat, Value.value) = ab;
                     ((acc: Map[Nat.nat, Option[Value.value]]) =>
                       (acc + ((reg -> (Some[Value.value](vala))))))
                   }),
                  aa, b));
    Lista.list_ex[List[(Nat.nat,
                         Value.value)]](((assignment:
    List[(Nat.nat, Value.value)])
   =>
  Optiona.equal_optiona[Value.value](AExp.aval[VName.vname](a,
                     AExp.join_ir(i, (update(assignment))(r))),
                                      Some[Value.value](expected))),
 assignments)
  }

def correct(a: AExp.aexp[VName.vname], bad: Set.set[AExp.aexp[VName.vname]],
             values: List[Value.value],
             train:
               List[(List[Value.value],
                      (Map[Nat.nat, Option[Value.value]],
                        (Value.value, List[Nat.nat])))],
             allowLatent: Boolean):
      Boolean
  =
  (! (Set.member[AExp.aexp[VName.vname]](a,
  bad))) && (Lista.list_all[(List[Value.value],
                              (Map[Nat.nat, Option[Value.value]],
                                (Value.value,
                                  List[Nat.nat])))](((b:
                (List[Value.value],
                  (Map[Nat.nat, Option[Value.value]],
                    (Value.value, List[Nat.nat]))))
               =>
              {
                val (i, (r, (p, l))):
                      (List[Value.value],
                        (Map[Nat.nat, Option[Value.value]],
                          (Value.value, List[Nat.nat])))
                  = b;
                correct_row(a, values, i, r, p, l, allowLatent)
              }),
             train))

def unzip_4[A, B, C, D](x0: List[(A, (B, (C, D)))]):
      (List[A], (List[B], (List[C], List[D])))
  =
  x0 match {
  case Nil => (Nil, (Nil, (Nil, Nil)))
  case ((a, (b, (c, d)))::l) =>
    {
      val (as, (bs, (cs, ds))): (List[A], (List[B], (List[C], List[D]))) =
        unzip_4[A, B, C, D](l);
      ((a::as), ((b::bs), ((c::cs), (d::ds))))
    }
}

def transitions[A, B, C, D]: (FSet.fset[(A, ((B, C), D))]) => FSet.fset[(C, A)]
  =
  ((a: FSet.fset[(A, ((B, C), D))]) =>
    FSet.fimage[(A, ((B, C), D)),
                 (C, A)](((aa: (A, ((B, C), D))) =>
                           {
                             val (tids, ab): (A, ((B, C), D)) = aa
                             val (ac, b): ((B, C), D) = ab;
                             ({
                                val (_, to): (B, C) = ac;
                                ((_: D) => (to, tids))
                              })(b)
                           }),
                          a))

def outgoing_transitions(g: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                          v: Nat.nat):
      FSet.fset[(Nat.nat, List[Nat.nat])]
  =
  transitions[List[Nat.nat], Nat.nat, Nat.nat,
               Transition.transition_ext[Unit]].apply(FSet.ffilter[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))](((a:
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])))
                             =>
                            {
                              val (_, aa):
                                    (List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))
                                = a
                              val (ab, b):
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])
                                = aa;
                              ({
                                 val (from, _): (Nat.nat, Nat.nat) = ab;
                                 ((_: Transition.transition_ext[Unit]) =>
                                   Nat.equal_nata(from, v))
                               })(b)
                            }),
                           g))

def allRoutes(g: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))],
               v: Nat.nat, closed: List[List[Nat.nat]]):
      FSet.fset[List[List[Nat.nat]]]
  =
  (if (! (FSet.fmember[Nat.nat](v, Inference.nodes(g))))
    FSet.bot_fset[List[List[Nat.nat]]]
    else {
           val options: FSet.fset[(Nat.nat, List[Nat.nat])] =
             FSet.ffilter[(Nat.nat,
                            List[Nat.nat])](((a: (Nat.nat, List[Nat.nat])) =>
      {
        val (_, t): (Nat.nat, List[Nat.nat]) = a;
        ! (closed.contains(t))
      }),
     outgoing_transitions(g, v));
           (if (FSet.equal_fseta[(Nat.nat,
                                   List[Nat.nat])](options,
            FSet.bot_fset[(Nat.nat, List[Nat.nat])]))
             FSet.finsert[List[List[Nat.nat]]](Nil,
        FSet.bot_fset[List[List[Nat.nat]]])
             else FSet.sup_fset[List[List[Nat.nat]]](FSet.fimage[(Nat.nat,
                           List[Nat.nat]),
                          List[List[Nat.nat]]](((a: (Nat.nat, List[Nat.nat])) =>
         {
           val (_, t): (Nat.nat, List[Nat.nat]) = a;
           (t::Nil)
         }),
        options),
              FSet_Utils.fUnion[List[List[Nat.nat]]](FSet.fimage[(Nat.nat,
                           List[Nat.nat]),
                          FSet.fset[List[List[Nat.nat]]]](((a:
                      (Nat.nat, List[Nat.nat]))
                     =>
                    {
                      val (s, t): (Nat.nat, List[Nat.nat]) = a;
                      FSet.fimage[List[List[Nat.nat]],
                                   List[List[Nat.nat]]](((aa:
                    List[List[Nat.nat]])
                   =>
                  (t::aa)),
                 allRoutes(g, s, (t::closed)))
                    }),
                   options))))
         })

def enumerate_exec_values(vs: List[(String,
                                     (List[Value.value], List[Value.value]))]):
      List[Value.value]
  =
  Lista.fold[(String, (List[Value.value], List[Value.value])),
              List[Value.value]](((a: (String,
(List[Value.value], List[Value.value])))
                                    =>
                                   {
                                     val (_, (i, p)):
   (String, (List[Value.value], List[Value.value]))
                                       = a;
                                     Lista.union[Value.value].apply(Lista.union[Value.value].apply(i).apply(p))
                                   }),
                                  vs, Nil)

def enumerate_log_values(l: List[List[(String,
(List[Value.value], List[Value.value]))]]):
      List[Value.value]
  =
  Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
              List[Value.value]](((e: List[(String,
     (List[Value.value], List[Value.value]))])
                                    =>
                                   Lista.union[Value.value].apply(enumerate_exec_values(e))),
                                  l, Nil)

def insert_updates(t: Transition.transition_ext[Unit],
                    u: List[(Nat.nat, AExp.aexp[VName.vname])]):
      Transition.transition_ext[Unit]
  =
  {
    val necessary_updates: List[(Nat.nat, AExp.aexp[VName.vname])] =
      Lista.filter[(Nat.nat,
                     AExp.aexp[VName.vname])](((a:
          (Nat.nat, AExp.aexp[VName.vname]))
         =>
        {
          val (r, ua): (Nat.nat, AExp.aexp[VName.vname]) = a;
          ! (AExp.equal_aexpa[VName.vname](ua, AExp.V[VName.vname](VName.R(r))))
        }),
       u);
    Transition.Updates_update[Unit](((_:
List[(Nat.nat, AExp.aexp[VName.vname])])
                                       =>
                                      Lista.filter[(Nat.nat,
             AExp.aexp[VName.vname])](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
{
  val (r, _): (Nat.nat, AExp.aexp[VName.vname]) = a;
  ! ((Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
                 Nat.nat](((aa: (Nat.nat, AExp.aexp[VName.vname])) => aa._1),
                           u)).contains(r))
}),
                                       Transition.Updates[Unit](t)) ++
necessary_updates),
                                     t)
  }

def add_groupwise_updates_trace(x0: List[(String,
   (List[Value.value], List[Value.value]))],
                                 uu: List[(List[Nat.nat],
    List[(Nat.nat, AExp.aexp[VName.vname])])],
                                 e: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                 uv: Nat.nat,
                                 uw: Map[Nat.nat, Option[Value.value]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (x0, uu, e, uv, uw) match {
  case (Nil, uu, e, uv, uw) => e
  case (((l, (i, ux))::trace), funs, e, s, r) =>
    {
      val (id, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, l, i))
      val updated: Map[Nat.nat, Option[Value.value]] =
        (Transition.apply_updates(Transition.Updates[Unit](t),
                                   AExp.join_ir(i, r))).apply(r)
      val newUpdates: List[(Nat.nat, AExp.aexp[VName.vname])] =
        Lista.maps[(List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname])]),
                    (Nat.nat,
                      AExp.aexp[VName.vname])](((a:
           (List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname])]))
          =>
         a._2),
        Lista.filter[(List[Nat.nat],
                       List[(Nat.nat,
                              AExp.aexp[VName.vname])])](((a:
                     (List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname])]))
                    =>
                   {
                     val (tids, _):
                           (List[Nat.nat],
                             List[(Nat.nat, AExp.aexp[VName.vname])])
                       = a;
                     Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](id),
               Set.seta[Nat.nat](tids))
                   }),
                  funs))
      val ta: Transition.transition_ext[Unit] = insert_updates(t, newUpdates)
      val updateda: Map[Nat.nat, Option[Value.value]] =
        (Transition.apply_updates(Transition.Updates[Unit](ta),
                                   AExp.join_ir(i, r))).apply(r)
      val necessaryUpdates: List[(Nat.nat, AExp.aexp[VName.vname])] =
        Lista.filter[(Nat.nat,
                       AExp.aexp[VName.vname])](((a:
            (Nat.nat, AExp.aexp[VName.vname]))
           =>
          {
            val (ra, _): (Nat.nat, AExp.aexp[VName.vname]) = a;
            ! (Optiona.equal_optiona[Value.value](updated(ra), updateda(ra)))
          }),
         newUpdates)
      val tb: Transition.transition_ext[Unit] =
        insert_updates(t, necessaryUpdates)
      val ea: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
        = Inference.replace_transition(e, id, tb);
      add_groupwise_updates_trace(trace, funs, ea, sa, updateda)
    }
}

def add_groupwise_updates(log: List[List[(String,
   (List[Value.value], List[Value.value]))]],
                           funs: List[(List[Nat.nat],
List[(Nat.nat, AExp.aexp[VName.vname])])],
                           e: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((trace:
                            List[(String,
                                   (List[Value.value], List[Value.value]))])
                           =>
                          (acc: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                            =>
                          add_groupwise_updates_trace(trace, funs, acc,
               Nat.zero_nata,
               scala.collection.immutable.Map().withDefaultValue(None))),
                         log, e)

def registers_add(a: Map[Nat.nat, Option[Value.value]],
                   b: Map[Nat.nat, Option[Value.value]]):
      Map[Nat.nat, Option[Value.value]]
  =
  Lista.fold[Nat.nat,
              Map[Nat.nat, Option[Value.value]]](((k: Nat.nat) =>
           (f: Map[Nat.nat, Option[Value.value]]) => (f + ((k -> (b(k)))))),
          b.keySet.toList, a)

def target_registers(e: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      s: Nat.nat, r: Map[Nat.nat, Option[Value.value]],
                      x3: List[(String,
                                 (List[Value.value], List[Value.value]))],
                      types:
                        Map[(AExp.aexp[VName.vname]), (Map[VName.vname, value_type])]):
      List[(Nat.nat,
             (Map[Nat.nat, Option[Value.value]],
               (Map[Nat.nat, Option[Value.value]],
                 (List[Value.value],
                   (List[Nat.nat], Transition.transition_ext[Unit])))))]
  =
  (e, s, r, x3, types) match {
  case (e, s, r, Nil, types) => Nil
  case (e, s, r, ((l, (i, p))::es), types) =>
    {
      val (tids, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, l, i))
      val ra: Map[Nat.nat, Option[Value.value]] =
        (Transition.apply_updates(Transition.Updates[Unit](t),
                                   AExp.join_ir(i, r))).apply(r)
      val necessary_regs: Map[Nat.nat, Option[Value.value]] =
        Lista.fold[(Value.value, AExp.aexp[VName.vname]),
                    Map[Nat.nat, Option[Value.value]]](Fun.comp[Map[Nat.nat, Option[Value.value]],
                         Map[Nat.nat, Option[Value.value]] =>
                           Map[Nat.nat, Option[Value.value]],
                         (Value.value,
                           AExp.aexp[VName.vname])](((a:
                Map[Nat.nat, Option[Value.value]])
               =>
              (b: Map[Nat.nat, Option[Value.value]]) => registers_add(a, b)),
             ((a: (Value.value, AExp.aexp[VName.vname])) =>
               {
                 val (pa, f): (Value.value, AExp.aexp[VName.vname]) = a;
                 (if (((types(f)).keySet.toList).isEmpty)
                   scala.collection.immutable.Map().withDefaultValue(None)
                   else Dirties.getRegs(types(f), i, f, pa))
               })),
                p.par.zip(Transition.Outputs[Unit](t)).toList,
                scala.collection.immutable.Map().withDefaultValue(None));
      ((s, (r, (necessary_regs,
                 (i, (tids, t)))))::(target_registers(e, sa, ra, es, types)))
    }
}

def type_signature(x0: Value.value): value_type = x0 match {
  case Value.Str(uu) => S()
  case Value.Inta(uv) => I()
  case Value.Reala(uw) => R()
}

def type_signature_opt(x0: Option[Value.value]): value_type = x0 match {
  case Some(v) => type_signature(v)
}

def get_update(output_mem:
                 Map[((String,
                       (List[value_type],
                         List[value_type]))), (List[(AExp.aexp[VName.vname],
              Map[VName.vname, value_type])])],
                update_mem:
                  Map[((String,
                        (List[value_type],
                          List[value_type]))), (List[(AExp.aexp[VName.vname],
               Map[VName.vname, value_type])])],
                struct: (String, (List[value_type], List[value_type])),
                reg: Nat.nat, values: List[Value.value],
                train:
                  List[(List[Value.value],
                         (Map[Nat.nat, Option[Value.value]],
                           Map[Nat.nat, Option[Value.value]]))]):
      Option[(AExp.aexp[VName.vname], Map[VName.vname, value_type])]
  =
  (if (Lista.list_ex[(List[Value.value],
                       (Map[Nat.nat, Option[Value.value]],
                         Map[Nat.nat, Option[Value.value]]))](((a:
                          (List[Value.value],
                            (Map[Nat.nat, Option[Value.value]],
                              Map[Nat.nat, Option[Value.value]])))
                         =>
                        {
                          val (_, (_, pregs)):
                                (List[Value.value],
                                  (Map[Nat.nat, Option[Value.value]],
                                    Map[Nat.nat, Option[Value.value]]))
                            = a;
                          Optiona.is_none[Value.value](pregs(reg))
                        }),
                       train))
    None
    else {
           val ioPairs:
                 List[(List[Value.value],
                        (Map[Nat.nat, Option[Value.value]],
                          (Value.value, List[Nat.nat])))]
             = (Lista.map[(List[Value.value],
                            (Map[Nat.nat, Option[Value.value]],
                              Map[Nat.nat, Option[Value.value]])),
                           (List[Value.value],
                             (Map[Nat.nat, Option[Value.value]],
                               (Value.value,
                                 List[Nat.nat])))](((a:
               (List[Value.value],
                 (Map[Nat.nat, Option[Value.value]],
                   Map[Nat.nat, Option[Value.value]])))
              =>
             {
               val (inputs, (aregs, pregs)):
                     (List[Value.value],
                       (Map[Nat.nat, Option[Value.value]],
                         Map[Nat.nat, Option[Value.value]]))
                 = a
               val (Some(v)): Option[Value.value] = pregs(reg);
               (inputs,
                 ((scala.collection.immutable.Map().withDefaultValue(None) + ((reg -> (aregs(reg))))),
                   (v, Nil)))
             }),
            train)).par.distinct.toList;
           (Lista.find[(AExp.aexp[VName.vname],
                         Map[VName.vname, value_type])](((a:
                    (AExp.aexp[VName.vname], Map[VName.vname, value_type]))
                   =>
                  {
                    val (aa, _):
                          (AExp.aexp[VName.vname], Map[VName.vname, value_type])
                      = a;
                    correct(aa, Set.bot_set[AExp.aexp[VName.vname]], values,
                             ioPairs, false)
                  }),
                 output_mem(struct) ++ update_mem(struct))
              match {
              case None => Dirties.getUpdate(struct._1, reg, values, ioPairs)
              case Some((u, t)) =>
                Some[(AExp.aexp[VName.vname],
                       Map[VName.vname, value_type])]((u, t))
            })
         })

def get_updates_opt(output_mem:
                      Map[((String,
                            (List[value_type],
                              List[value_type]))), (List[(AExp.aexp[VName.vname],
                   Map[VName.vname, value_type])])],
                     update_mem:
                       Map[((String,
                             (List[value_type],
                               List[value_type]))), (List[(AExp.aexp[VName.vname],
                    Map[VName.vname, value_type])])],
                     l: (String, (List[value_type], List[value_type])),
                     values: List[Value.value],
                     train:
                       List[(List[Value.value],
                              (Map[Nat.nat, Option[Value.value]],
                                Map[Nat.nat, Option[Value.value]]))]):
      List[(Nat.nat,
             Option[(AExp.aexp[VName.vname], Map[VName.vname, value_type])])]
  =
  {
    val a: List[Nat.nat] =
      Lista.fold[(List[Value.value],
                   (Map[Nat.nat, Option[Value.value]],
                     Map[Nat.nat, Option[Value.value]])),
                  List[Nat.nat]](Fun.comp[List[Nat.nat],
   (List[Nat.nat]) => List[Nat.nat],
   (List[Value.value],
     (Map[Nat.nat, Option[Value.value]],
       Map[Nat.nat, Option[Value.value]]))](Lista.union[Nat.nat],
     Fun.comp[(Map[Nat.nat, Option[Value.value]],
                Map[Nat.nat, Option[Value.value]]),
               List[Nat.nat],
               (List[Value.value],
                 (Map[Nat.nat, Option[Value.value]],
                   Map[Nat.nat, Option[Value.value]]))](Fun.comp[Map[Nat.nat, Option[Value.value]],
                          List[Nat.nat],
                          (Map[Nat.nat, Option[Value.value]],
                            Map[Nat.nat, Option[Value.value]])](((a:
                            Map[Nat.nat, Option[Value.value]])
                           =>
                          a.keySet.toList),
                         ((a: (Map[Nat.nat, Option[Value.value]],
                                Map[Nat.nat, Option[Value.value]]))
                            =>
                           a._2)),
                 ((a: (List[Value.value],
                        (Map[Nat.nat, Option[Value.value]],
                          Map[Nat.nat, Option[Value.value]])))
                    =>
                   a._2))),
                                  train, Nil);
    Lista.map[Nat.nat,
               (Nat.nat,
                 Option[(AExp.aexp[VName.vname],
                          Map[VName.vname, value_type])])](((r: Nat.nat) =>
                     {
                       val targetValues: List[Option[Value.value]] =
                         (Lista.map[(List[Value.value],
                                      (Map[Nat.nat, Option[Value.value]],
Map[Nat.nat, Option[Value.value]])),
                                     Option[Value.value]](((aa:
                      (List[Value.value],
                        (Map[Nat.nat, Option[Value.value]],
                          Map[Nat.nat, Option[Value.value]])))
                     =>
                    {
                      val (_, (_, regs)):
                            (List[Value.value],
                              (Map[Nat.nat, Option[Value.value]],
                                Map[Nat.nat, Option[Value.value]]))
                        = aa;
                      regs(r)
                    }),
                   train)).par.distinct.toList;
                       (if (Lista.list_all[(List[Value.value],
     (Map[Nat.nat, Option[Value.value]],
       Map[Nat.nat, Option[Value.value]]))](((aa:
        (List[Value.value],
          (Map[Nat.nat, Option[Value.value]],
            Map[Nat.nat, Option[Value.value]])))
       =>
      {
        val (_, (anteriorRegs, posteriorRegs)):
              (List[Value.value],
                (Map[Nat.nat, Option[Value.value]],
                  Map[Nat.nat, Option[Value.value]]))
          = aa;
        Optiona.equal_optiona[Value.value](anteriorRegs(r), posteriorRegs(r))
      }),
     train))
                         (r, Some[(AExp.aexp[VName.vname],
                                    Map[VName.vname, value_type])]((AExp.V[VName.vname](VName.R(r)),
                             scala.collection.immutable.Map().withDefaultValue(type_signature_opt((((train.head)._2)._1)(r))))))
                         else (if ((Nat.equal_nata(Nat.Nata(targetValues.par.length),
            Nat.Nata((1)))) && (Lista.list_all[(List[Value.value],
         (Map[Nat.nat, Option[Value.value]],
           Map[Nat.nat, Option[Value.value]]))](((aa:
            (List[Value.value],
              (Map[Nat.nat, Option[Value.value]],
                Map[Nat.nat, Option[Value.value]])))
           =>
          {
            val (_, (anteriorRegs, _)):
                  (List[Value.value],
                    (Map[Nat.nat, Option[Value.value]],
                      Map[Nat.nat, Option[Value.value]]))
              = aa;
            (anteriorRegs.keySet.toList).isEmpty
          }),
         train)))
                                {
                                  val (Some(v)): Option[Value.value] =
                                    targetValues.head;
                                  (r, Some[(AExp.aexp[VName.vname],
     Map[VName.vname, value_type])]((AExp.L[VName.vname](v),
                                      scala.collection.immutable.Map().withDefaultValue(type_signature(v)))))
                                }
                                else (r, get_update(output_mem, update_mem, l,
             r, values, train))))
                     }),
                    a)
  }

def group_update(output_mem:
                   Map[((String,
                         (List[value_type],
                           List[value_type]))), (List[(AExp.aexp[VName.vname],
                Map[VName.vname, value_type])])],
                  update_mem:
                    Map[((String,
                          (List[value_type],
                            List[value_type]))), (List[(AExp.aexp[VName.vname],
                 Map[VName.vname, value_type])])],
                  struct: (String, (List[value_type], List[value_type])),
                  values: List[Value.value],
                  l: List[(Map[Nat.nat, Option[Value.value]],
                            (Nat.nat,
                              (Map[Nat.nat, Option[Value.value]],
                                (Map[Nat.nat, Option[Value.value]],
                                  (List[Value.value],
                                    (List[Nat.nat],
                                      Transition.transition_ext[Unit]))))))]):
      Option[(List[Nat.nat],
               List[(Nat.nat,
                      (AExp.aexp[VName.vname], Map[VName.vname, value_type]))])]
  =
  {
    val (_, (_, (_, (_, (_, (_, _)))))):
          (Map[Nat.nat, Option[Value.value]],
            (Nat.nat,
              (Map[Nat.nat, Option[Value.value]],
                (Map[Nat.nat, Option[Value.value]],
                  (List[Value.value],
                    (List[Nat.nat], Transition.transition_ext[Unit]))))))
      = l.head
    val targeted:
          List[(Map[Nat.nat, Option[Value.value]],
                 (Nat.nat,
                   (Map[Nat.nat, Option[Value.value]],
                     (Map[Nat.nat, Option[Value.value]],
                       (List[Value.value],
                         (List[Nat.nat], Transition.transition_ext[Unit]))))))]
      = Lista.filter[(Map[Nat.nat, Option[Value.value]],
                       (Nat.nat,
                         (Map[Nat.nat, Option[Value.value]],
                           (Map[Nat.nat, Option[Value.value]],
                             (List[Value.value],
                               (List[Nat.nat],
                                 Transition.transition_ext[Unit]))))))](((a:
                                    (Map[Nat.nat, Option[Value.value]],
                                      (Nat.nat,
(Map[Nat.nat, Option[Value.value]],
  (Map[Nat.nat, Option[Value.value]],
    (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit])))))))
                                   =>
                                  {
                                    val (regs, _):
  (Map[Nat.nat, Option[Value.value]],
    (Nat.nat,
      (Map[Nat.nat, Option[Value.value]],
        (Map[Nat.nat, Option[Value.value]],
          (List[Value.value],
            (List[Nat.nat], Transition.transition_ext[Unit]))))))
                                      = a;
                                    ! ((regs.keySet.toList).isEmpty)
                                  }),
                                 l)
    val maybe_updates:
          List[(Nat.nat,
                 Option[(AExp.aexp[VName.vname],
                          Map[VName.vname, value_type])])]
      = get_updates_opt(output_mem, update_mem, struct, values,
                         Lista.map[(Map[Nat.nat, Option[Value.value]],
                                     (Nat.nat,
                                       (Map[Nat.nat, Option[Value.value]],
 (Map[Nat.nat, Option[Value.value]],
   (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit])))))),
                                    (List[Value.value],
                                      (Map[Nat.nat, Option[Value.value]],
Map[Nat.nat, Option[Value.value]]))](((a:
 (Map[Nat.nat, Option[Value.value]],
   (Nat.nat,
     (Map[Nat.nat, Option[Value.value]],
       (Map[Nat.nat, Option[Value.value]],
         (List[Value.value],
           (List[Nat.nat], Transition.transition_ext[Unit])))))))
=>
                                       {
 val (tRegs, (_, (oldRegs, (regs, (inputs, (_, _)))))):
       (Map[Nat.nat, Option[Value.value]],
         (Nat.nat,
           (Map[Nat.nat, Option[Value.value]],
             (Map[Nat.nat, Option[Value.value]],
               (List[Value.value],
                 (List[Nat.nat], Transition.transition_ext[Unit]))))))
   = a;
 (inputs, (registers_add(oldRegs, regs), tRegs))
                                       }),
                                      targeted));
    (if (Lista.list_ex[(Nat.nat,
                         Option[(AExp.aexp[VName.vname],
                                  Map[VName.vname, value_type])])](((a:
                               (Nat.nat,
                                 Option[(AExp.aexp[VName.vname],
  Map[VName.vname, value_type])]))
                              =>
                             {
                               val (_, aa):
                                     (Nat.nat,
                                       Option[(AExp.aexp[VName.vname],
        Map[VName.vname, value_type])])
                                 = a;
                               Optiona.is_none[(AExp.aexp[VName.vname],
         Map[VName.vname, value_type])](aa)
                             }),
                            maybe_updates))
      None
      else {
             val the_update_functions:
                   List[(Nat.nat,
                          (AExp.aexp[VName.vname],
                            Map[VName.vname, value_type]))]
               = Lista.map[(Nat.nat,
                             Option[(AExp.aexp[VName.vname],
                                      Map[VName.vname, value_type])]),
                            (Nat.nat,
                              (AExp.aexp[VName.vname],
                                Map[VName.vname, value_type]))](((a:
                            (Nat.nat,
                              Option[(AExp.aexp[VName.vname],
                                       Map[VName.vname, value_type])]))
                           =>
                          {
                            val (r, f_o):
                                  (Nat.nat,
                                    Option[(AExp.aexp[VName.vname],
     Map[VName.vname, value_type])])
                              = a;
                            (r, Optiona.the[(AExp.aexp[VName.vname],
      Map[VName.vname, value_type])](f_o))
                          }),
                         maybe_updates);
             (if (Lista.list_all[(Nat.nat,
                                   (AExp.aexp[VName.vname],
                                     Map[VName.vname, value_type]))](((a:
                                 (Nat.nat,
                                   (AExp.aexp[VName.vname],
                                     Map[VName.vname, value_type])))
                                =>
                               {
                                 val (_, (fun, _)):
                                       (Nat.nat,
 (AExp.aexp[VName.vname], Map[VName.vname, value_type]))
                                   = a;
                                 AExp.is_lit[VName.vname](fun)
                               }),
                              the_update_functions))
               Some[(List[Nat.nat],
                      List[(Nat.nat,
                             (AExp.aexp[VName.vname],
                               Map[VName.vname, value_type]))])]((Lista.fold[(Map[Nat.nat, Option[Value.value]],
                                       (Nat.nat,
 (Map[Nat.nat, Option[Value.value]],
   (Map[Nat.nat, Option[Value.value]],
     (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit])))))),
                                      List[Nat.nat]](Fun.comp[List[Nat.nat],
                       (List[Nat.nat]) => List[Nat.nat],
                       (Map[Nat.nat, Option[Value.value]],
                         (Nat.nat,
                           (Map[Nat.nat, Option[Value.value]],
                             (Map[Nat.nat, Option[Value.value]],
                               (List[Value.value],
                                 (List[Nat.nat],
                                   Transition.transition_ext[Unit]))))))](Lista.union[Nat.nat],
                                   ((a: (Map[Nat.nat, Option[Value.value]],
  (Nat.nat,
    (Map[Nat.nat, Option[Value.value]],
      (Map[Nat.nat, Option[Value.value]],
        (List[Value.value],
          (List[Nat.nat], Transition.transition_ext[Unit])))))))
                                      =>
                                     {
                                       val
 (_, (_, (_, (_, (_, (tid, _)))))):
   (Map[Nat.nat, Option[Value.value]],
     (Nat.nat,
       (Map[Nat.nat, Option[Value.value]],
         (Map[Nat.nat, Option[Value.value]],
           (List[Value.value],
             (List[Nat.nat], Transition.transition_ext[Unit]))))))
 = a;
                                       tid
                                     })),
              targeted, Nil),
                           the_update_functions))
               else Some[(List[Nat.nat],
                           List[(Nat.nat,
                                  (AExp.aexp[VName.vname],
                                    Map[VName.vname, value_type]))])]((Lista.fold[(Map[Nat.nat, Option[Value.value]],
    (Nat.nat,
      (Map[Nat.nat, Option[Value.value]],
        (Map[Nat.nat, Option[Value.value]],
          (List[Value.value],
            (List[Nat.nat], Transition.transition_ext[Unit])))))),
   List[Nat.nat]](Fun.comp[List[Nat.nat], (List[Nat.nat]) => List[Nat.nat],
                            (Map[Nat.nat, Option[Value.value]],
                              (Nat.nat,
                                (Map[Nat.nat, Option[Value.value]],
                                  (Map[Nat.nat, Option[Value.value]],
                                    (List[Value.value],
                                      (List[Nat.nat],
Transition.transition_ext[Unit]))))))](Lista.union[Nat.nat],
((a: (Map[Nat.nat, Option[Value.value]],
       (Nat.nat,
         (Map[Nat.nat, Option[Value.value]],
           (Map[Nat.nat, Option[Value.value]],
             (List[Value.value],
               (List[Nat.nat], Transition.transition_ext[Unit])))))))
   =>
  {
    val (_, (_, (_, (_, (_, (tid, _)))))):
          (Map[Nat.nat, Option[Value.value]],
            (Nat.nat,
              (Map[Nat.nat, Option[Value.value]],
                (Map[Nat.nat, Option[Value.value]],
                  (List[Value.value],
                    (List[Nat.nat], Transition.transition_ext[Unit]))))))
      = a;
    tid
  })),
                   l, Nil),
                                the_update_functions)))
           })
  }

def infer_updates(output_mem:
                    Map[((String,
                          (List[value_type],
                            List[value_type]))), (List[(AExp.aexp[VName.vname],
                 Map[VName.vname, value_type])])],
                   update_mem:
                     Map[((String,
                           (List[value_type],
                             List[value_type]))), (List[(AExp.aexp[VName.vname],
                  Map[VName.vname, value_type])])],
                   e: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                   l: List[List[(String,
                                  (List[Value.value], List[Value.value]))]],
                   x4: ((String, (List[value_type], List[value_type])),
                         List[(List[Nat.nat],
                                Transition.transition_ext[Unit])]),
                   types:
                     Map[(AExp.aexp[VName.vname]), (Map[VName.vname, value_type])]):
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
        Map[((String,
              (List[value_type],
                List[value_type]))), (List[(AExp.aexp[VName.vname],
     Map[VName.vname, value_type])])])
  =
  (output_mem, update_mem, e, l, x4, types) match {
  case (output_mem, update_mem, e, l, (struct, gp), types) =>
    {
      val values: List[Value.value] = enumerate_log_values(l)
      val group_ids: Set.set[List[Nat.nat]] =
        Set.seta[List[Nat.nat]](Lista.map[(List[Nat.nat],
    Transition.transition_ext[Unit]),
   List[Nat.nat]](((a: (List[Nat.nat], Transition.transition_ext[Unit])) =>
                    a._1),
                   gp))
      val targeted:
            List[List[(Map[Nat.nat, Option[Value.value]],
                        (Nat.nat,
                          (Map[Nat.nat, Option[Value.value]],
                            (Map[Nat.nat, Option[Value.value]],
                              (List[Value.value],
                                (List[Nat.nat],
                                  Transition.transition_ext[Unit]))))))]]
        = Lista.map[List[(String, (List[Value.value], List[Value.value]))],
                     List[(Map[Nat.nat, Option[Value.value]],
                            (Nat.nat,
                              (Map[Nat.nat, Option[Value.value]],
                                (Map[Nat.nat, Option[Value.value]],
                                  (List[Value.value],
                                    (List[Nat.nat],
                                      Transition.transition_ext[Unit]))))))]](((trace:
  List[(String, (List[Value.value], List[Value.value]))])
 =>
(target(scala.collection.immutable.Map().withDefaultValue(None),
         (target_registers(e, Nat.zero_nata,
                            scala.collection.immutable.Map().withDefaultValue(None),
                            trace,
                            types)).par.reverse.toList)).par.reverse.toList),
                                       l)
      val relevant:
            List[(Map[Nat.nat, Option[Value.value]],
                   (Nat.nat,
                     (Map[Nat.nat, Option[Value.value]],
                       (Map[Nat.nat, Option[Value.value]],
                         (List[Value.value],
                           (List[Nat.nat],
                             Transition.transition_ext[Unit]))))))]
        = Lista.fold[List[(Map[Nat.nat, Option[Value.value]],
                            (Nat.nat,
                              (Map[Nat.nat, Option[Value.value]],
                                (Map[Nat.nat, Option[Value.value]],
                                  (List[Value.value],
                                    (List[Nat.nat],
                                      Transition.transition_ext[Unit]))))))],
                      List[(Map[Nat.nat, Option[Value.value]],
                             (Nat.nat,
                               (Map[Nat.nat, Option[Value.value]],
                                 (Map[Nat.nat, Option[Value.value]],
                                   (List[Value.value],
                                     (List[Nat.nat],
                                       Transition.transition_ext[Unit]))))))]](Fun.comp[List[(Map[Nat.nat, Option[Value.value]],
               (Nat.nat,
                 (Map[Nat.nat, Option[Value.value]],
                   (Map[Nat.nat, Option[Value.value]],
                     (List[Value.value],
                       (List[Nat.nat], Transition.transition_ext[Unit]))))))],
         (List[(Map[Nat.nat, Option[Value.value]],
                 (Nat.nat,
                   (Map[Nat.nat, Option[Value.value]],
                     (Map[Nat.nat, Option[Value.value]],
                       (List[Value.value],
                         (List[Nat.nat],
                           Transition.transition_ext[Unit]))))))]) =>
           List[(Map[Nat.nat, Option[Value.value]],
                  (Nat.nat,
                    (Map[Nat.nat, Option[Value.value]],
                      (Map[Nat.nat, Option[Value.value]],
                        (List[Value.value],
                          (List[Nat.nat],
                            Transition.transition_ext[Unit]))))))],
         List[(Map[Nat.nat, Option[Value.value]],
                (Nat.nat,
                  (Map[Nat.nat, Option[Value.value]],
                    (Map[Nat.nat, Option[Value.value]],
                      (List[Value.value],
                        (List[Nat.nat],
                          Transition.transition_ext[Unit]))))))]](Lista.union[(Map[Nat.nat, Option[Value.value]],
(Nat.nat,
  (Map[Nat.nat, Option[Value.value]],
    (Map[Nat.nat, Option[Value.value]],
      (List[Value.value],
        (List[Nat.nat], Transition.transition_ext[Unit]))))))],
                           ((a: List[(Map[Nat.nat, Option[Value.value]],
                                       (Nat.nat,
 (Map[Nat.nat, Option[Value.value]],
   (Map[Nat.nat, Option[Value.value]],
     (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit]))))))])
                              =>
                             Lista.filter[(Map[Nat.nat, Option[Value.value]],
    (Nat.nat,
      (Map[Nat.nat, Option[Value.value]],
        (Map[Nat.nat, Option[Value.value]],
          (List[Value.value],
            (List[Nat.nat],
              Transition.transition_ext[Unit]))))))](((aa:
                 (Map[Nat.nat, Option[Value.value]],
                   (Nat.nat,
                     (Map[Nat.nat, Option[Value.value]],
                       (Map[Nat.nat, Option[Value.value]],
                         (List[Value.value],
                           (List[Nat.nat],
                             Transition.transition_ext[Unit])))))))
                =>
               {
                 val (_, (_, (_, (_, (_, (tids, _)))))):
                       (Map[Nat.nat, Option[Value.value]],
                         (Nat.nat,
                           (Map[Nat.nat, Option[Value.value]],
                             (Map[Nat.nat, Option[Value.value]],
                               (List[Value.value],
                                 (List[Nat.nat],
                                   Transition.transition_ext[Unit]))))))
                   = aa;
                 Set.member[List[Nat.nat]](tids, group_ids)
               }),
              a))),
targeted, Nil);
      (group_update(output_mem, update_mem, struct, values, relevant) match {
         case None =>
           (e, scala.collection.immutable.Map().withDefaultValue(Nil))
         case Some((tids, typed_updates)) =>
           {
             val untyped_updates:
                   (List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname])])
               = (tids,
                   Lista.map[(Nat.nat,
                               (AExp.aexp[VName.vname],
                                 Map[VName.vname, value_type])),
                              (Nat.nat,
                                AExp.aexp[VName.vname])](((a:
                     (Nat.nat,
                       (AExp.aexp[VName.vname], Map[VName.vname, value_type])))
                    =>
                   {
                     val (r, ft):
                           (Nat.nat,
                             (AExp.aexp[VName.vname],
                               Map[VName.vname, value_type]))
                       = a;
                     (r, ft._1)
                   }),
                  typed_updates))
             val a: Map[((String,
                          (List[value_type],
                            List[value_type]))), (List[(AExp.aexp[VName.vname],
                 Map[VName.vname, value_type])])]
               = ((scala.collection.immutable.Map().withDefaultValue(Nil)) + ((struct -> (Lista.map[(Nat.nat,
                      (AExp.aexp[VName.vname], Map[VName.vname, value_type])),
                     (AExp.aexp[VName.vname],
                       Map[VName.vname, value_type])](((a:
                  (Nat.nat,
                    (AExp.aexp[VName.vname], Map[VName.vname, value_type])))
                 =>
                a._2),
               typed_updates)))));
             (Inference.make_distinct(add_groupwise_updates(l,
                     (untyped_updates::Nil), e)),
               a)
           }
       })
    }
}

def funmem_union[A : HOL.equal : Orderings.linorder,
                  B](bada: Map[A, (List[B])], bad: Map[A, (List[B])]):
      Map[A, (List[B])]
  =
  Lista.fold[A, Map[A, (List[B])]](((k: A) => (acc: Map[A, (List[B])]) =>
                                     (acc + ((k -> ((bada(k) ++
              bad(k)).par.distinct.toList))))),
                                    (bada.keySet.toList ++
                                      bad.keySet.toList).par.distinct.toList,
                                    scala.collection.immutable.Map().withDefaultValue(Nil))

def groupwise_infer_updates(output_mem:
                              Map[((String,
                                    (List[value_type],
                                      List[value_type]))), (List[(AExp.aexp[VName.vname],
                           Map[VName.vname, value_type])])],
                             update_mem:
                               Map[((String,
                                     (List[value_type],
                                       List[value_type]))), (List[(AExp.aexp[VName.vname],
                            Map[VName.vname, value_type])])],
                             log: List[List[(String,
      (List[Value.value], List[Value.value]))]],
                             e: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                             x4: List[((String,
 (List[value_type], List[value_type])),
List[(List[Nat.nat], Transition.transition_ext[Unit])])],
                             types:
                               Map[(AExp.aexp[VName.vname]), (Map[VName.vname, value_type])]):
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
        Map[((String,
              (List[value_type],
                List[value_type]))), (List[(AExp.aexp[VName.vname],
     Map[VName.vname, value_type])])])
  =
  (output_mem, update_mem, log, e, x4, types) match {
  case (output_mem, update_mem, log, e, Nil, types) => (e, update_mem)
  case (output_mem, update_mem, log, e, (gp::gps), types) =>
    (if (EFSM.accepts_log(Set.seta[List[(String,
  (List[Value.value], List[Value.value]))]](log),
                           Inference.tm(e)))
      (e, update_mem)
      else {
             val (updates, update_mema):
                   (FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))],
                     Map[((String,
                           (List[value_type],
                             List[value_type]))), (List[(AExp.aexp[VName.vname],
                  Map[VName.vname, value_type])])])
               = infer_updates(output_mem, update_mem, e, log, gp, types);
             groupwise_infer_updates(output_mem,
                                      funmem_union[(String,
             (List[value_type], List[value_type])),
            (AExp.aexp[VName.vname],
              Map[VName.vname, value_type])](update_mem, update_mema),
                                      log, updates, gps, types)
           })
}

def appears_in_order[A : HOL.equal](x0: List[A], uu: List[A]): Boolean =
  (x0, uu) match {
  case (Nil, uu) => true
  case ((a::uv), Nil) => false
  case ((ha::ta), (h::t)) =>
    (if (HOL.eq[A](ha, h)) appears_in_order[A](ta, t)
      else appears_in_order[A]((ha::ta), t))
}

def get_output(struct: (String, (List[value_type], List[value_type])),
                tids: List[Nat.nat], maxReg: Nat.nat, values: List[Value.value],
                bad: Set.set[AExp.aexp[VName.vname]],
                train:
                  List[(List[Value.value],
                         (Map[Nat.nat, Option[Value.value]],
                           (Value.value, List[Nat.nat])))],
                output_mem:
                  Map[((String,
                        (List[value_type],
                          List[value_type]))), (List[(AExp.aexp[VName.vname],
               Map[VName.vname, value_type])])],
                update_mem:
                  Map[((String,
                        (List[value_type],
                          List[value_type]))), (List[(AExp.aexp[VName.vname],
               Map[VName.vname, value_type])])]):
      Option[(AExp.aexp[VName.vname], Map[VName.vname, value_type])]
  =
  (Lista.find[(AExp.aexp[VName.vname],
                Map[VName.vname, value_type])](((a:
           (AExp.aexp[VName.vname], Map[VName.vname, value_type]))
          =>
         {
           val (fun, _): (AExp.aexp[VName.vname], Map[VName.vname, value_type])
             = a;
           (! (Set.member[AExp.aexp[VName.vname]](fun,
           bad))) && (correct(fun, bad, values, train, true))
         }),
        output_mem(struct) ++ update_mem(struct))
     match {
     case None => Dirties.getOutput(struct._1, tids, maxReg, values, bad, train)
     case Some((fun, types)) =>
       Some[(AExp.aexp[VName.vname],
              Map[VName.vname, value_type])]((fun, types))
   })

def output_and_update(bad: Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])],
                       good: List[AExp.aexp[VName.vname]],
                       output_mem:
                         Map[((String,
                               (List[value_type],
                                 List[value_type]))), (List[(AExp.aexp[VName.vname],
                      Map[VName.vname, value_type])])],
                       update_mem:
                         Map[((String,
                               (List[value_type],
                                 List[value_type]))), (List[(AExp.aexp[VName.vname],
                      Map[VName.vname, value_type])])],
                       uu: Nat.nat, uv: Nat.nat,
                       e: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                       uw: List[List[(String,
                                       (List[Value.value],
 List[Value.value]))]],
                       ux: List[((String, (List[value_type], List[value_type])),
                                  List[(List[Nat.nat],
 Transition.transition_ext[Unit])])],
                       uy: ((String, (List[value_type], List[value_type])),
                             List[(List[Nat.nat],
                                    Transition.transition_ext[Unit])]),
                       uz: List[Value.value], va: List[List[Value.value]],
                       vb: List[Map[Nat.nat, Option[Value.value]]],
                       x13: List[(Nat.nat, (Nat.nat, List[Value.value]))],
                       vc: List[List[Nat.nat]]):
      output_generalisation
  =
  (bad, good, output_mem, update_mem, uu, uv, e, uw, ux, uy, uz, va, vb, x13,
    vc)
  match {
  case (bad, good, output_mem, update_mem, uu, uv, e, uw, ux, uy, uz, va, vb,
         Nil, vc)
    => Success((e, (output_mem, (update_mem, (good.par.reverse.toList, bad)))))
  case (bad, good, output_mem, update_mem, max_attempts, attempts, e, log, gps,
         (struct, gp), values, is, r, ((inx, (maxReg, ps))::pss), latent)
    => {
         val (rep_id, rep): (List[Nat.nat], Transition.transition_ext[Unit]) =
           gp.head;
         Transition.Label[Unit](rep);
         (get_output(struct, (gp.head)._1, maxReg, values,
                      Set.seta[AExp.aexp[VName.vname]](bad(rep_id)),
                      is.par.zip(r.par.zip(ps.par.zip(latent).toList).toList).toList,
                      output_mem, update_mem)
            match {
            case None =>
              Failure((bad + ((rep_id -> ((good ++
    bad(rep_id)).par.distinct.toList)))))
            case Some((fun, types)) =>
              {
                val ea: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]
                  = FSet.fimage[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])),
                                 (List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))](((a:
                                    (List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])))
                                   =>
                                  {
                                    val (tids, (tf, t)):
  (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                      = a;
                                    (if ((Lista.map[(List[Nat.nat],
              Transition.transition_ext[Unit]),
             List[Nat.nat]](((aa: (List[Nat.nat],
                                    Transition.transition_ext[Unit]))
                               =>
                              aa._1),
                             gp)).contains(tids))
                                      (tids,
(tf, Transition.Outputs_update[Unit](((_: List[AExp.aexp[VName.vname]]) =>
                                       Lista.list_update[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t),
  inx, fun)),
                                      t)))
                                      else (tids, (tf, t)))
                                  }),
                                 e)
                val unknown: Map[VName.vname, value_type] =
                  scala.collection.immutable.Map().withDefaultValue(I())
                val routes: FSet.fset[List[List[Nat.nat]]] =
                  allRoutes(e, Nat.zero_nata, Nil)
                val output_mema:
                      Map[((String,
                            (List[value_type],
                              List[value_type]))), (List[(AExp.aexp[VName.vname],
                   Map[VName.vname, value_type])])]
                  = (output_mem + ((struct -> (((fun,
          types)::(output_mem(struct)))))));
                (if (EFSM.accepts_log(Set.seta[List[(String,
              (List[Value.value], List[Value.value]))]](log),
                                       Inference.tm(ea)))
                  output_and_update(bad, (fun::good), output_mema, update_mem,
                                     max_attempts, attempts, ea, log, gps,
                                     (struct, gp), values, is, r, pss, latent)
                  else {
                         val group_ids:
                               (List[(List[Nat.nat],
                                       Transition.transition_ext[Unit])]) =>
                                 Set.set[List[Nat.nat]]
                           = ((g: List[(List[Nat.nat],
 Transition.transition_ext[Unit])])
                                =>
                               Set.seta[List[Nat.nat]](Lista.map[(List[Nat.nat],
                           Transition.transition_ext[Unit]),
                          List[Nat.nat]](((a:
     (List[Nat.nat], Transition.transition_ext[Unit]))
    =>
   a._1),
  g)))
                         val gp_ids: Set.set[List[Nat.nat]] = group_ids(gp)
                         val possible_gps:
                               List[((String,
                                       (List[value_type], List[value_type])),
                                      List[(List[Nat.nat],
     Transition.transition_ext[Unit])])]
                           = Lista.filter[((String,
     (List[value_type], List[value_type])),
    List[(List[Nat.nat],
           Transition.transition_ext[Unit])])](((a:
           ((String, (List[value_type], List[value_type])),
             List[(List[Nat.nat], Transition.transition_ext[Unit])]))
          =>
         {
           val (_, g):
                 ((String, (List[value_type], List[value_type])),
                   List[(List[Nat.nat], Transition.transition_ext[Unit])])
             = a;
           FSet.fBex[List[List[Nat.nat]]](routes,
   ((ra: List[List[Nat.nat]]) =>
     Set.Bex[List[Nat.nat]](group_ids(g),
                             ((id: List[Nat.nat]) =>
                               Set.Bex[List[Nat.nat]](gp_ids,
               ((ida: List[Nat.nat]) =>
                 appears_in_order[List[Nat.nat]]((id::((ida::Nil))), ra)))))))
         }),
        gps)
                         val (eaa, update_mema):
                               (FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                 Map[((String,
                                       (List[value_type],
 List[value_type]))), (List[(AExp.aexp[VName.vname],
                              Map[VName.vname, value_type])])])
                           = groupwise_infer_updates(output_mema, update_mem,
              log, ea, possible_gps,
              ((scala.collection.immutable.Map().withDefaultValue(unknown)) + ((fun -> types))));
                         (if (EFSM.accepts_log(Set.seta[List[(String,
                       (List[Value.value], List[Value.value]))]](log),
        Inference.tm(eaa)))
                           output_and_update(bad, (fun::good), output_mema,
      update_mema, max_attempts, attempts, eaa, log, gps, (struct, gp), values,
      is, r, pss, latent)
                           else (if (Nat.less_nat(Nat.zero_nata, attempts))
                                  output_and_update((bad + ((rep_id -> (Lista.insert[AExp.aexp[VName.vname]](fun,
                              bad(rep_id)))))),
             good, output_mem, update_mema, max_attempts,
             Nat.minus_nat(attempts, Nat.Nata((1))), e, log, gps, (struct, gp),
             values, is, r, ((inx, (maxReg, ps))::pss), latent)
                                  else Failure((bad + ((rep_id -> (((fun::(good ++
                                    bad(rep_id)))).par.distinct.toList)))))))
                       })
              }
          })
       }
}

def trace_group_training_set(uu: ((String,
                                    (List[value_type], List[value_type])),
                                   List[(List[Nat.nat],
  Transition.transition_ext[Unit])]),
                              uv: FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                              uw: Nat.nat,
                              ux: Map[Nat.nat, Option[Value.value]],
                              uy: Transition.transition_ext[Unit],
                              x5: List[(String,
 (List[Value.value], List[Value.value]))],
                              train:
                                List[(List[Value.value],
                                       (Map[Nat.nat, Option[Value.value]],
 (List[Value.value], List[Nat.nat])))]):
      List[(List[Value.value],
             (Map[Nat.nat, Option[Value.value]],
               (List[Value.value], List[Nat.nat])))]
  =
  (uu, uv, uw, ux, uy, x5, train) match {
  case (uu, uv, uw, ux, uy, Nil, train) => train
  case (gp, e, s, r, last_tran, ((l, (i, p))::t), train) =>
    {
      val (ids, (sa, transition)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, l, i))
      val last_updated: List[Nat.nat] =
        Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
                   Nat.nat](((a: (Nat.nat, AExp.aexp[VName.vname])) => a._1),
                             Transition.Updates[Unit](last_tran));
      (if (Lista.list_ex[(List[Nat.nat],
                           Transition.transition_ext[Unit])](((a:
                         (List[Nat.nat], Transition.transition_ext[Unit]))
                        =>
                       {
                         val (idsa, _):
                               (List[Nat.nat], Transition.transition_ext[Unit])
                           = a;
                         Lista.equal_lista[Nat.nat](idsa, ids)
                       }),
                      gp._2))
        trace_group_training_set(gp, e, sa,
                                  (Transition.apply_updates(Transition.Updates[Unit](transition),
                     AExp.join_ir(i, r))).apply(r),
                                  transition, t,
                                  ((i, (r, (p, last_updated)))::train))
        else trace_group_training_set(gp, e, sa,
                                       (Transition.apply_updates(Transition.Updates[Unit](transition),
                          AExp.join_ir(i, r))).apply(r),
                                       transition, t, train))
    }
}

def make_training_set(e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       l: List[List[(String,
                                      (List[Value.value], List[Value.value]))]],
                       gp: ((String, (List[value_type], List[value_type])),
                             List[(List[Nat.nat],
                                    Transition.transition_ext[Unit])])):
      List[(List[Value.value],
             (Map[Nat.nat, Option[Value.value]],
               (List[Value.value], List[Nat.nat])))]
  =
  Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
              List[(List[Value.value],
                     (Map[Nat.nat, Option[Value.value]],
                       (List[Value.value],
                         List[Nat.nat])))]](((a:
        List[(String, (List[Value.value], List[Value.value]))])
       =>
      (b: List[(List[Value.value],
                 (Map[Nat.nat, Option[Value.value]],
                   (List[Value.value], List[Nat.nat])))])
        =>
      trace_group_training_set(gp, e, Nat.zero_nata,
                                scala.collection.immutable.Map().withDefaultValue(None),
                                Transition.transition_exta[Unit]("",
                          Nat.zero_nata, Nil, Nil, Nil, ()),
                                a, b)),
     l, Nil)

def generalise_and_update(level: Nat.nat, attempts: Nat.nat,
                           bad: Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])],
                           log: List[List[(String,
    (List[Value.value], List[Value.value]))]],
                           e: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                           gp: ((String, (List[value_type], List[value_type])),
                                 List[(List[Nat.nat],
Transition.transition_ext[Unit])]),
                           gps: List[((String,
(List[value_type], List[value_type])),
                                       List[(List[Nat.nat],
      Transition.transition_ext[Unit])])],
                           output_mem:
                             Map[((String,
                                   (List[value_type],
                                     List[value_type]))), (List[(AExp.aexp[VName.vname],
                          Map[VName.vname, value_type])])]):
      output_generalisation
  =
  {
    val values: List[Value.value] = enumerate_log_values(log)
    val new_gp_ts:
          List[(List[Value.value],
                 (Map[Nat.nat, Option[Value.value]],
                   (List[Value.value], List[Nat.nat])))]
      = make_training_set(e, log, gp)
    val (i, (r, (p, l))):
          (List[List[Value.value]],
            (List[Map[Nat.nat, Option[Value.value]]],
              (List[List[Value.value]], List[List[Nat.nat]])))
      = unzip_4[List[Value.value], Map[Nat.nat, Option[Value.value]],
                 List[Value.value], List[Nat.nat]](new_gp_ts)
    val max_reg: Nat.nat = Inference.max_reg_total(e)
    val outputs_to_infer: List[(Nat.nat, (Nat.nat, List[Value.value]))] =
      Lista.enumerate[(Nat.nat,
                        List[Value.value])](Nat.zero_nata,
     Lista.enumerate[List[Value.value]](max_reg,
 Lista.transpose[Value.value](p)));
    output_and_update(bad, Nil, output_mem,
                       scala.collection.immutable.Map().withDefaultValue(Nil),
                       attempts, attempts, e, log, gps, gp, values, i, r,
                       outputs_to_infer, l)
  }

def take_maximum_updates(ts: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat], Transition.transition_ext[Unit])]
  =
  Lista.fold[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
              FSet.fset[(List[Nat.nat],
                          Transition.transition_ext[Unit])]](((a:
                         (List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])))
                        =>
                       {
                         val (tids, (_, t)):
                               (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))
                           = a;
                         ((acc: FSet.fset[(List[Nat.nat],
    Transition.transition_ext[Unit])])
                            =>
                           (if (FSet.fBex[(List[Nat.nat],
    Transition.transition_ext[Unit])](acc, ((aa:
       (List[Nat.nat], Transition.transition_ext[Unit]))
      =>
     {
       val (_, h): (List[Nat.nat], Transition.transition_ext[Unit]) = aa;
       (Transition.Label[Unit](t) ==
         Transition.Label[Unit](h)) && ((Nat.equal_nata(Transition.Arity[Unit](t),
                 Transition.Arity[Unit](h))) && ((Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t),
             Transition.Outputs[Unit](h))) && (Set.less_set[(Nat.nat,
                      AExp.aexp[VName.vname])](Set.seta[(Nat.nat,
                  AExp.aexp[VName.vname])](Transition.Updates[Unit](t)),
        Set.seta[(Nat.nat,
                   AExp.aexp[VName.vname])](Transition.Updates[Unit](h))))))
     })))
                             acc else FSet.finsert[(List[Nat.nat],
             Transition.transition_ext[Unit])]((tids, t), acc)))
                       }),
                      FSet.sorted_list_of_fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](ts),
                      FSet.bot_fset[(List[Nat.nat],
                                      Transition.transition_ext[Unit])])

def wipe_futures(bad: Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])],
                  tids: List[Nat.nat]):
      Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])]
  =
  Lista.fold[List[Nat.nat],
              Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])]](((k:
                                List[Nat.nat])
                               =>
                              (acc: Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])])
                                =>
                              (if (Nat.less_nat(Lattices_Big.Max[Nat.nat](Set.seta[Nat.nat](tids)),
         Lattices_Big.Max[Nat.nat](Set.seta[Nat.nat](k))))
                                (acc + ((k -> Nil))) else acc)),
                             bad.keySet.toList, bad)

def funmem_add[A : HOL.equal, B](bad: Map[A, (List[B])], k: A, v: List[B]):
      Map[A, (List[B])]
  =
  (bad + ((k -> ((bad(k) ++ v).par.distinct.toList))))

def groupwise_generalise_and_update(bad: Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])],
                                     maybe_bad:
                                       Map[(List[Nat.nat]), (List[AExp.aexp[VName.vname]])],
                                     max_attempts: Nat.nat, attempts: Nat.nat,
                                     can_fail: Boolean,
                                     transition_repeats: Nat.nat,
                                     uu: List[List[(String,
             (List[Value.value], List[Value.value]))]],
                                     e: FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                     x8: List[((String,
         (List[value_type], List[value_type])),
        List[(List[Nat.nat], Transition.transition_ext[Unit])])],
                                     update_groups:
                                       List[((String,
       (List[value_type], List[value_type])),
      List[(List[Nat.nat], Transition.transition_ext[Unit])])],
                                     structure:
                                       (List[Nat.nat]) =>
 (String, (List[value_type], List[value_type])),
                                     funs: Map[((String,
         (List[value_type],
           List[value_type]))), Option[(List[AExp.aexp[VName.vname]],
 List[(Nat.nat, AExp.aexp[VName.vname])])]],
                                     to_derestrict: List[List[Nat.nat]],
                                     output_mem:
                                       Map[((String,
     (List[value_type],
       List[value_type]))), (List[(AExp.aexp[VName.vname],
                                    Map[VName.vname, value_type])])],
                                     update_mem:
                                       Map[((String,
     (List[value_type],
       List[value_type]))), (List[(AExp.aexp[VName.vname],
                                    Map[VName.vname, value_type])])]):
      generalisation
  =
  (bad, maybe_bad, max_attempts, attempts, can_fail, transition_repeats, uu, e,
    x8, update_groups, structure, funs, to_derestrict, output_mem, update_mem)
  match {
  case (bad, maybe_bad, max_attempts, attempts, can_fail, transition_repeats,
         uu, e, Nil, update_groups, structure, funs, to_derestrict, output_mem,
         update_mem)
    => Succeeded((e, (to_derestrict, (output_mem, update_mem))))
  case (bad, maybe_bad, max_attempts, attempts, can_fail, transition_repeats,
         log, e, (gp::t), update_groups, structure, funsb, to_derestrict,
         output_mem, update_mem)
    => (generalise_and_update(transition_repeats, transition_repeats, bad, log,
                               e, gp, update_groups, output_mem)
          match {
          case Success((ea, (_, (update_mema, (output_funs, bada))))) =>
            {
              val checkpoint: Boolean = ! ((update_mema.keySet.toList).isEmpty)
              val update_memb:
                    Map[((String,
                          (List[value_type],
                            List[value_type]))), (List[(AExp.aexp[VName.vname],
                 Map[VName.vname, value_type])])]
                = funmem_union[(String, (List[value_type], List[value_type])),
                                (AExp.aexp[VName.vname],
                                  Map[VName.vname, value_type])](update_mem,
                          update_mema)
              val reg_bad: List[AExp.aexp[VName.vname]] =
                Lista.filter[AExp.aexp[VName.vname]](((a:
                 AExp.aexp[VName.vname])
                =>
               ! (Code_Cardinality.eq_set[Nat.nat](AExp.enumerate_regs(a),
            Set.bot_set[Nat.nat]))),
              output_funs)
              val (rep_id, _): (List[Nat.nat], Transition.transition_ext[Unit])
                = (gp._2).head
              val different:
                    FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]
                = FSet.ffilter[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))](((a:
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])))
                                 =>
                                {
                                  val (id, (_, ta)):
(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                    = a;
                                  ! (Transition.equal_transition_exta[Unit](ta,
                                     Inference.get_by_ids(e, id)))
                                }),
                               ea)
              val funs: Map[((String,
                              (List[value_type],
                                List[value_type]))), Option[(List[AExp.aexp[VName.vname]],
                      List[(Nat.nat, AExp.aexp[VName.vname])])]]
                = Lista.fold[(List[Nat.nat], Transition.transition_ext[Unit]),
                              Map[((String,
                                    (List[value_type],
                                      List[value_type]))), Option[(List[AExp.aexp[VName.vname]],
                            List[(Nat.nat,
                                   AExp.aexp[VName.vname])])]]](((a:
                            (List[Nat.nat], Transition.transition_ext[Unit]))
                           =>
                          {
                            val (id, ta):
                                  (List[Nat.nat],
                                    Transition.transition_ext[Unit])
                              = a;
                            ((acc: Map[((String,
 (List[value_type],
   List[value_type]))), Option[(List[AExp.aexp[VName.vname]],
                                 List[(Nat.nat, AExp.aexp[VName.vname])])]])
                               =>
                              (acc + (((structure(id)) -> (Some[(List[AExp.aexp[VName.vname]],
                          List[(Nat.nat,
                                 AExp.aexp[VName.vname])])]((Transition.Outputs[Unit](ta),
                      Transition.Updates[Unit](ta))))))))
                          }),
                         FSet.sorted_list_of_fset[(List[Nat.nat],
            Transition.transition_ext[Unit])](take_maximum_updates(different)),
                         funsb);
              FSet.fimage[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])),
                           (List[Nat.nat],
                             Transition.transition_ext[Unit])](((a:
                           (List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit])))
                          =>
                         {
                           val (i, aa):
                                 (List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))
                             = a
                           val (_, ab):
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])
                             = aa;
                           (i, ab)
                         }),
                        FSet.ffilter[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))](((a:
(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                                       =>
                                      {
val (i, (_, _)):
      (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
  = a;
Product_Type.equal_proda[String,
                          (List[value_type],
                            List[value_type])](structure(i), structure(rep_id))
                                      }),
                                     ea))
              val new_outputs:
                    (List[Nat.nat]) =>
                      (Transition.transition_ext[Unit]) =>
                        List[AExp.aexp[VName.vname]]
                = ((tid: List[Nat.nat]) =>
                    (ta: Transition.transition_ext[Unit]) =>
                    (funs(structure(tid)) match {
                       case None => Transition.Outputs[Unit](ta)
                       case Some((outputs, _)) => outputs
                     }))
              val new_updates:
                    (List[Nat.nat]) =>
                      (Transition.transition_ext[Unit]) =>
                        List[(Nat.nat, AExp.aexp[VName.vname])]
                = ((tid: List[Nat.nat]) =>
                    (ta: Transition.transition_ext[Unit]) =>
                    (funs(structure(tid)) match {
                       case None => Transition.Updates[Unit](ta)
                       case Some((_, updates)) => updates
                     }))
              val pre_standardised:
                    FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]
                = FSet.fimage[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])),
                               (List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))](((a:
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])))
                                 =>
                                {
                                  val (tida, (tfa, tra)):
(List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                    = a;
                                  (tida,
                                    (tfa, Transition.Updates_update[Unit](((_:
                                      List[(Nat.nat, AExp.aexp[VName.vname])])
                                     =>
                                    (new_updates(tida))(tra)),
                                   Transition.Outputs_update[Unit](((_:
                               List[AExp.aexp[VName.vname]])
                              =>
                             (new_outputs(tida))(tra)),
                            tra))))
                                }),
                               ea)
              val pre_standardised_good: Boolean =
                EFSM.accepts_log(Set.seta[List[(String,
         (List[Value.value], List[Value.value]))]](log),
                                  Inference.tm(pre_standardised))
              val standardised:
                    FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]
                = (if (pre_standardised_good) pre_standardised else ea)
              val more_to_derestrict: List[List[Nat.nat]] =
                FSet.sorted_list_of_fset[List[Nat.nat]](FSet.fimage[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])),
                             List[Nat.nat]](((a:
        (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
       =>
      a._1),
     FSet.ffilter[(List[Nat.nat],
                    ((Nat.nat, Nat.nat),
                      Transition.transition_ext[Unit]))](((a:
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                    =>
                   {
                     val (id, (_, tran)):
                           (List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))
                       = a;
                     ! (Transition.equal_transition_exta[Unit](tran,
                        Inference.get_by_ids(e, id)))
                   }),
                  standardised)))
              val a: generalisation =
                (if (pre_standardised_good)
                  groupwise_generalise_and_update(wipe_futures(bad, rep_id),
           funmem_union[List[Nat.nat], AExp.aexp[VName.vname]](maybe_bad, bada),
           max_attempts, attempts, true, transition_repeats, log,
           Same_Register.merge_regs(standardised,
                                     ((a:
 FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])])
=>
                                       EFSM.accepts_log(Set.seta[List[(String,
                                (List[Value.value], List[Value.value]))]](log),
                 a))),
           Lista.filter[((String, (List[value_type], List[value_type])),
                          List[(List[Nat.nat],
                                 Transition.transition_ext[Unit])])](((g:
                                 ((String,
                                    (List[value_type], List[value_type])),
                                   List[(List[Nat.nat],
  Transition.transition_ext[Unit])]))
                                =>
                               ! ((funs.keySet.toList).contains(g._1))),
                              t),
           update_groups, structure, funs, to_derestrict ++ more_to_derestrict,
           output_mem, update_memb)
                  else groupwise_generalise_and_update(wipe_futures(bad,
                             rep_id),
                funmem_add[List[Nat.nat],
                            AExp.aexp[VName.vname]](funmem_union[List[Nat.nat],
                          AExp.aexp[VName.vname]](maybe_bad, bada),
             rep_id, reg_bad),
                max_attempts, attempts, true, transition_repeats, log,
                Same_Register.merge_regs(standardised,
  ((a: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
    EFSM.accepts_log(Set.seta[List[(String,
                                     (List[Value.value],
                                       List[Value.value]))]](log),
                      a))),
                t, update_groups, structure, funs,
                to_derestrict ++ more_to_derestrict, output_mem, update_memb));
              (a match {
                 case Failed(badb) =>
                   (if (Nat.less_nat(Nat.zero_nata, attempts))
                     (if (checkpoint)
                       groupwise_generalise_and_update(wipe_futures(funmem_add[List[Nat.nat],
AExp.aexp[VName.vname]](funmem_union[List[Nat.nat],
                                      AExp.aexp[VName.vname]](maybe_bad, badb),
                         rep_id, reg_bad),
                             rep_id),
                scala.collection.immutable.Map().withDefaultValue(Nil),
                max_attempts, Nat.minus_nat(attempts, Nat.Nata((1))), true,
                transition_repeats, log, e, (gp::t), update_groups, structure,
                funsb, to_derestrict, output_mem, update_memb)
                       else groupwise_generalise_and_update(badb,
                     scala.collection.immutable.Map().withDefaultValue(Nil),
                     max_attempts, max_attempts, can_fail, transition_repeats,
                     log, e, t, update_groups, structure, funsb, to_derestrict,
                     output_mem, update_memb))
                     else groupwise_generalise_and_update(funmem_add[List[Nat.nat],
                              AExp.aexp[VName.vname]](badb, rep_id, reg_bad),
                   scala.collection.immutable.Map().withDefaultValue(Nil),
                   max_attempts, max_attempts, false, transition_repeats, log,
                   e, t, update_groups, structure, funsb, to_derestrict,
                   output_mem, update_memb))
                 case Succeeded(aa) => Succeeded(aa)
               })
            }
          case Failure(bada) =>
            (if (can_fail)
              Failed(funmem_union[List[Nat.nat],
                                   AExp.aexp[VName.vname]](bad, bada))
              else groupwise_generalise_and_update(funmem_union[List[Nat.nat],
                         AExp.aexp[VName.vname]](bad, bada),
            scala.collection.immutable.Map().withDefaultValue(Nil),
            max_attempts, max_attempts, false, transition_repeats, log, e, t,
            update_groups, structure, funsb, to_derestrict, output_mem,
            update_mem))
        })
}

def drop_selected_guards(e: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                          ids: List[List[Nat.nat]],
                          pta: FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                          log: List[List[(String,
   (List[Value.value], List[Value.value]))]],
                          m: (List[Nat.nat]) =>
                               (List[Nat.nat]) =>
                                 Nat.nat =>
                                   (FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                     (FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                       (FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
 ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
   Boolean) =>
   Option[FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                          np: (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat),
      ((Transition.transition_ext[Unit], List[Nat.nat]),
        (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val derestricted:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))](((a:
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])))
                       =>
                      {
                        val (id, (tf, tran)):
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))
                          = a;
                        (id, (tf, (if (ids.contains(id))
                                    Transition.Guards_update[Unit](((_:
                               List[GExp.gexp[VName.vname]])
                              =>
                             Nil),
                            tran)
                                    else tran)))
                      }),
                     e)
    val nondeterministic_pairs:
          List[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (Transition.transition_ext[Unit], List[Nat.nat]))))]
      = FSet.sorted_list_of_fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     ((Transition.transition_ext[Unit],
List[Nat.nat]),
                                       (Transition.transition_ext[Unit],
 List[Nat.nat]))))](np(derestricted));
    (Inference.resolve_nondeterminism(Set.bot_set[(Nat.nat, Nat.nat)],
                                       nondeterministic_pairs, pta,
                                       derestricted, m,
                                       ((a:
   FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])])
  =>
 EFSM.accepts_log(Set.seta[List[(String,
                                  (List[Value.value],
                                    List[Value.value]))]](log),
                   a)),
                                       np)
       match {
       case (None, _) => pta
       case (Some(resolved), _) => resolved
     })
  }

def event_structure(e: (String, (List[Value.value], List[Value.value]))):
      (String, (List[value_type], List[value_type]))
  =
  {
    val (l, (i, p)): (String, (List[Value.value], List[Value.value])) = e;
    (l, (Lista.map[Value.value,
                    value_type](((a: Value.value) => type_signature(a)), i),
          Lista.map[Value.value,
                     value_type](((a: Value.value) => type_signature(a)), p)))
  }

def events_transitions(uu: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))],
                        uv: Nat.nat, uw: Map[Nat.nat, Option[Value.value]],
                        x3: List[(String,
                                   (List[Value.value], List[Value.value]))],
                        tt: List[(List[Nat.nat],
                                   (String,
                                     (List[value_type], List[value_type])))]):
      List[(List[Nat.nat], (String, (List[value_type], List[value_type])))]
  =
  (uu, uv, uw, x3, tt) match {
  case (uu, uv, uw, Nil, tt) => tt.par.reverse.toList
  case (e, s, r, ((l, (i, p))::trace), tt) =>
    {
      val (id, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, l, i))
      val ra: Map[Nat.nat, Option[Value.value]] =
        (Transition.apply_updates(Transition.Updates[Unit](t),
                                   AExp.join_ir(i, r))).apply(r);
      events_transitions(e, sa, ra, trace,
                          ((id, event_structure((l, (i, p))))::tt))
    }
}

def get_structures(e: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                    log: List[List[(String,
                                     (List[Value.value], List[Value.value]))]]):
      (List[Nat.nat]) => (String, (List[value_type], List[value_type]))
  =
  {
    val observed:
          List[(List[Nat.nat], (String, (List[value_type], List[value_type])))]
      = Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
                    List[(List[Nat.nat],
                           (String,
                             (List[value_type],
                               List[value_type])))]](Fun.comp[List[(List[Nat.nat],
                             (String, (List[value_type], List[value_type])))],
                       (List[(List[Nat.nat],
                               (String,
                                 (List[value_type], List[value_type])))]) =>
                         List[(List[Nat.nat],
                                (String,
                                  (List[value_type], List[value_type])))],
                       List[(String,
                              (List[Value.value],
                                List[Value.value]))]](((a:
                  List[(List[Nat.nat],
                         (String, (List[value_type], List[value_type])))])
                 =>
                (b: List[(List[Nat.nat],
                           (String, (List[value_type], List[value_type])))])
                  =>
                a ++ b),
               ((t: List[(String, (List[Value.value], List[Value.value]))]) =>
                 events_transitions(e, Nat.zero_nata,
                                     scala.collection.immutable.Map().withDefaultValue(None),
                                     t, Nil))),
              log, Nil);
    Lista.fold[(List[Nat.nat], (String, (List[value_type], List[value_type]))),
                (List[Nat.nat]) =>
                  (String,
                    (List[value_type],
                      List[value_type]))](((a:
      (List[Nat.nat], (String, (List[value_type], List[value_type]))))
     =>
    {
      val (tids, abs):
            (List[Nat.nat], (String, (List[value_type], List[value_type])))
        = a;
      ((acc: (List[Nat.nat]) => (String, (List[value_type], List[value_type])))
         =>
        (tt: List[Nat.nat]) =>
        (if ((Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](tt),
        Set.seta[Nat.nat](tids))) || (Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](tids),
                                Set.seta[Nat.nat](tt))))
          abs else acc(tt)))
    }),
   observed, ((_: List[Nat.nat]) => ("UNKNOWN", (Nil, Nil))))
  }

def tidy_updates[A, B](x0: List[(A, B)]): List[(A, B)] = x0 match {
  case Nil => Nil
  case ((a, b)::t) =>
    (if ((Lista.map[(A, B), A](((aa: (A, B)) => aa._1), t)).contains(a))
      tidy_updates[A, B](t) else ((a, b)::(tidy_updates[A, B](t))))
}

def derestrict(groups:
                 List[((String, (List[value_type], List[value_type])),
                        List[(List[Nat.nat],
                               Transition.transition_ext[Unit])])],
                tree_repeats: Nat.nat, transition_repeats: Nat.nat,
                pta: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                log: List[List[(String,
                                 (List[Value.value], List[Value.value]))]],
                m: (List[Nat.nat]) =>
                     (List[Nat.nat]) =>
                       Nat.nat =>
                         (FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]) =>
                           (FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                             (FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                               ((FSet.fset[((Nat.nat, Nat.nat),
     Transition.transition_ext[Unit])]) =>
                                 Boolean) =>
                                 Option[FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                np: (FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    ((Transition.transition_ext[Unit],
                                       List[Nat.nat]),
                                      (Transition.transition_ext[Unit],
List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val output_groups:
          List[((String, (List[value_type], List[value_type])),
                 List[(List[Nat.nat], Transition.transition_ext[Unit])])]
      = Lista.filter[((String, (List[value_type], List[value_type])),
                       List[(List[Nat.nat],
                              Transition.transition_ext[Unit])])](((a:
                              ((String, (List[value_type], List[value_type])),
                                List[(List[Nat.nat],
                                       Transition.transition_ext[Unit])]))
                             =>
                            {
                              val (_, g):
                                    ((String,
                                       (List[value_type], List[value_type])),
                                      List[(List[Nat.nat],
     Transition.transition_ext[Unit])])
                                = a;
                              ! ((Transition.Outputs[Unit]((g.head)._2)).isEmpty)
                            }),
                           groups)
    val (normalised, (to_derestrict, (_, _))):
          (FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
            (List[List[Nat.nat]],
              (Map[((String,
                     (List[value_type],
                       List[value_type]))), (List[(AExp.aexp[VName.vname],
            Map[VName.vname, value_type])])],
                Map[((String,
                      (List[value_type],
                        List[value_type]))), (List[(AExp.aexp[VName.vname],
             Map[VName.vname, value_type])])])))
      = thisa(groupwise_generalise_and_update(scala.collection.immutable.Map().withDefaultValue(Nil),
       scala.collection.immutable.Map().withDefaultValue(Nil), tree_repeats,
       tree_repeats, false, transition_repeats, log, pta, output_groups, groups,
       get_structures(pta, log),
       scala.collection.immutable.Map().withDefaultValue(None), Nil,
       scala.collection.immutable.Map().withDefaultValue(Nil),
       scala.collection.immutable.Map().withDefaultValue(Nil)))
    val tidied:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))](((a:
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])))
                       =>
                      {
                        val (id, (tf, t)):
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))
                          = a;
                        (id, (tf, Transition.Updates_update[Unit](((_:
                              List[(Nat.nat, AExp.aexp[VName.vname])])
                             =>
                            tidy_updates[Nat.nat,
  AExp.aexp[VName.vname]](Transition.Updates[Unit](t))),
                           t)))
                      }),
                     normalised);
    drop_selected_guards(tidied, to_derestrict, pta, log, m, np)
  }

def remove_consecutive_duplicates[A : HOL.equal](x0: List[A], acc: List[A]):
      List[A]
  =
  (x0, acc) match {
  case (Nil, acc) => acc.par.reverse.toList
  case ((h::t), Nil) => remove_consecutive_duplicates[A](t, (h::Nil))
  case ((ha::ta), (h::t)) =>
    (if (HOL.eq[A](ha, h)) remove_consecutive_duplicates[A](ta, (h::t))
      else remove_consecutive_duplicates[A](ta, (ha::((h::t)))))
}

def trace_history(l: List[(List[Nat.nat],
                            (String, (List[value_type], List[value_type])))]):
      List[(List[Nat.nat],
             ((String, (List[value_type], List[value_type])),
               List[(String, (List[value_type], List[value_type]))]))]
  =
  {
    val transition_ids: List[List[Nat.nat]] =
      Lista.map[(List[Nat.nat], (String, (List[value_type], List[value_type]))),
                 List[Nat.nat]](((a: (List[Nat.nat],
                                       (String,
 (List[value_type], List[value_type]))))
                                   =>
                                  a._1),
                                 l)
    val abstract_events: List[(String, (List[value_type], List[value_type]))] =
      Lista.map[(List[Nat.nat], (String, (List[value_type], List[value_type]))),
                 (String,
                   (List[value_type],
                     List[value_type]))](((a:
     (List[Nat.nat], (String, (List[value_type], List[value_type]))))
    =>
   a._2),
  l)
    val groups: List[List[(String, (List[value_type], List[value_type]))]] =
      Group_By.group_by[(String,
                          (List[value_type],
                            List[value_type]))](((a:
            (String, (List[value_type], List[value_type])))
           =>
          (b: (String, (List[value_type], List[value_type]))) =>
          Product_Type.equal_proda[String,
                                    (List[value_type],
                                      List[value_type])](a, b)),
         abstract_events)
    val group_histories:
          List[List[(String, (List[value_type], List[value_type]))]]
      = Sublist.prefixes[(String,
                           (List[value_type],
                             List[value_type]))](remove_consecutive_duplicates[(String,
 (List[value_type], List[value_type]))](abstract_events, Nil))
    val group_lengths: List[Nat.nat] =
      Lista.map[List[(String, (List[value_type], List[value_type]))],
                 Nat.nat](((a: List[(String,
                                      (List[value_type], List[value_type]))])
                             =>
                            Nat.Nata(a.par.length)),
                           groups)
    val repeats: List[List[(String, (List[value_type], List[value_type]))]] =
      Lista.foldr[(Nat.nat,
                    List[(String, (List[value_type], List[value_type]))]),
                   List[List[(String,
                               (List[value_type],
                                 List[value_type]))]]](Fun.comp[List[List[(String,
                                    (List[value_type], List[value_type]))]],
                         (List[List[(String,
                                      (List[value_type],
List[value_type]))]]) =>
                           List[List[(String,
                                       (List[value_type], List[value_type]))]],
                         (Nat.nat,
                           List[(String,
                                  (List[value_type],
                                    List[value_type]))])](((a:
                      List[List[(String,
                                  (List[value_type], List[value_type]))]])
                     =>
                    (b: List[List[(String,
                                    (List[value_type], List[value_type]))]])
                      =>
                    a ++ b),
                   ((a: (Nat.nat,
                          List[(String, (List[value_type], List[value_type]))]))
                      =>
                     {
                       val (aa, b):
                             (Nat.nat,
                               List[(String,
                                      (List[value_type], List[value_type]))])
                         = a;
                       AExp.repeat[List[(String,
  (List[value_type], List[value_type]))]](aa, b)
                     })),
                group_lengths.par.zip(group_histories).toList, Nil);
    transition_ids.par.zip(abstract_events.par.zip(repeats).toList).toList
  }

def all_known_regs[A, B](train:
                           List[(A, (Map[Nat.nat, Option[Value.value]], B))]):
      Set.set[Nat.nat]
  =
  Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(A,
                                    (Map[Nat.nat, Option[Value.value]], B)),
                                   Set.set[Nat.nat]](((a:
                 (A, (Map[Nat.nat, Option[Value.value]], B)))
                =>
               {
                 val (_, (r, _)): (A, (Map[Nat.nat, Option[Value.value]], B)) =
                   a;
                 Set.seta[Nat.nat](r.keySet.toList)
               }),
              train)))

def drop_all_guards(e: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                     pta: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                     log: List[List[(String,
                                      (List[Value.value], List[Value.value]))]],
                     m: (List[Nat.nat]) =>
                          (List[Nat.nat]) =>
                            Nat.nat =>
                              (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                (FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                  (FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                    ((FSet.fset[((Nat.nat, Nat.nat),
          Transition.transition_ext[Unit])]) =>
                                      Boolean) =>
                                      Option[FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                     np: (FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]) =>
                           FSet.fset[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 ((Transition.transition_ext[Unit], List[Nat.nat]),
   (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    val derestricted:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = FSet.fimage[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                     (List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))](((a:
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])))
                       =>
                      {
                        val (id, (tf, tran)):
                              (List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))
                          = a;
                        (id, (tf, Transition.Guards_update[Unit](((_:
                             List[GExp.gexp[VName.vname]])
                            =>
                           Nil),
                          tran)))
                      }),
                     e)
    val nondeterministic_pairs:
          List[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], List[Nat.nat]),
                     (Transition.transition_ext[Unit], List[Nat.nat]))))]
      = FSet.sorted_list_of_fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     ((Transition.transition_ext[Unit],
List[Nat.nat]),
                                       (Transition.transition_ext[Unit],
 List[Nat.nat]))))](np(derestricted));
    (Inference.resolve_nondeterminism(Set.bot_set[(Nat.nat, Nat.nat)],
                                       nondeterministic_pairs, pta,
                                       derestricted, m,
                                       ((a:
   FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])])
  =>
 EFSM.accepts_log(Set.seta[List[(String,
                                  (List[Value.value],
                                    List[Value.value]))]](log),
                   a)),
                                       np)
       match {
       case (None, _) => pta
       case (Some(resolved), _) => resolved
     })
  }

def drop_pta_guards(pta: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                     log: List[List[(String,
                                      (List[Value.value], List[Value.value]))]],
                     m: (List[Nat.nat]) =>
                          (List[Nat.nat]) =>
                            Nat.nat =>
                              (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                (FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                  (FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                    ((FSet.fset[((Nat.nat, Nat.nat),
          Transition.transition_ext[Unit])]) =>
                                      Boolean) =>
                                      Option[FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                     np: (FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]) =>
                           FSet.fset[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 ((Transition.transition_ext[Unit], List[Nat.nat]),
   (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  drop_all_guards(pta, pta, log, m, np)

def historical_groups(e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       log: List[List[(String,
(List[Value.value], List[Value.value]))]]):
      List[((String, (List[value_type], List[value_type])),
             List[(List[Nat.nat], Transition.transition_ext[Unit])])]
  =
  {
    val observed:
          List[List[(List[Nat.nat],
                      (String, (List[value_type], List[value_type])))]]
      = Lista.map[List[(String, (List[Value.value], List[Value.value]))],
                   List[(List[Nat.nat],
                          (String,
                            (List[value_type],
                              List[value_type])))]](((t:
                List[(String, (List[Value.value], List[Value.value]))])
               =>
              events_transitions(e, Nat.zero_nata,
                                  scala.collection.immutable.Map().withDefaultValue(None),
                                  t, Nil)),
             log)
    val histories:
          List[List[(List[Nat.nat],
                      ((String, (List[value_type], List[value_type])),
                        List[(String, (List[value_type], List[value_type]))]))]]
      = Lista.map[List[(List[Nat.nat],
                         (String, (List[value_type], List[value_type])))],
                   List[(List[Nat.nat],
                          ((String, (List[value_type], List[value_type])),
                            List[(String,
                                   (List[value_type],
                                     List[value_type]))]))]](((a:
                         List[(List[Nat.nat],
                                (String,
                                  (List[value_type], List[value_type])))])
                        =>
                       trace_history(a)),
                      observed)
    val flat: List[(List[Nat.nat],
                     ((String, (List[value_type], List[value_type])),
                       List[(String, (List[value_type], List[value_type]))]))]
      = Lista.fold[List[(List[Nat.nat],
                          ((String, (List[value_type], List[value_type])),
                            List[(String,
                                   (List[value_type], List[value_type]))]))],
                    List[(List[Nat.nat],
                           ((String, (List[value_type], List[value_type])),
                             List[(String,
                                    (List[value_type],
                                      List[value_type]))]))]](((a:
                          List[(List[Nat.nat],
                                 ((String,
                                    (List[value_type], List[value_type])),
                                   List[(String,
  (List[value_type], List[value_type]))]))])
                         =>
                        (b: List[(List[Nat.nat],
                                   ((String,
                                      (List[value_type], List[value_type])),
                                     List[(String,
    (List[value_type], List[value_type]))]))])
                          =>
                        a ++ b),
                       histories, Nil)
    val groups_fun:
          Map[(((String, (List[value_type], List[value_type])),
                List[(String,
                       (List[value_type],
                         List[value_type]))])), (List[List[Nat.nat]])]
      = Lista.fold[(List[Nat.nat],
                     ((String, (List[value_type], List[value_type])),
                       List[(String, (List[value_type], List[value_type]))])),
                    Map[(((String, (List[value_type], List[value_type])),
                          List[(String,
                                 (List[value_type],
                                   List[value_type]))])), (List[List[Nat.nat]])]](((a:
      (List[Nat.nat],
        ((String, (List[value_type], List[value_type])),
          List[(String, (List[value_type], List[value_type]))])))
     =>
    {
      val (id, (structure, history)):
            (List[Nat.nat],
              ((String, (List[value_type], List[value_type])),
                List[(String, (List[value_type], List[value_type]))]))
        = a;
      ((gps: Map[(((String, (List[value_type], List[value_type])),
                   List[(String,
                          (List[value_type],
                            List[value_type]))])), (List[List[Nat.nat]])])
         =>
        (gps + (((structure, history) -> ((id::(gps((structure, history)))))))))
    }),
   flat, scala.collection.immutable.Map().withDefaultValue(Nil))
    val groups:
          List[(Nat.nat,
                 (List[(String, (List[value_type], List[value_type]))],
                   List[List[Nat.nat]]))]
      = Lista.sort_key[(Nat.nat,
                         (List[(String, (List[value_type], List[value_type]))],
                           List[List[Nat.nat]])),
                        (Nat.nat,
                          (List[(String, (List[value_type], List[value_type]))],
                            List[List[Nat.nat]]))](((x:
               (Nat.nat,
                 (List[(String, (List[value_type], List[value_type]))],
                   List[List[Nat.nat]])))
              =>
             x),
            Lista.map[((String, (List[value_type], List[value_type])),
                        List[(String, (List[value_type], List[value_type]))]),
                       (Nat.nat,
                         (List[(String, (List[value_type], List[value_type]))],
                           List[List[Nat.nat]]))](((k:
              ((String, (List[value_type], List[value_type])),
                List[(String, (List[value_type], List[value_type]))]))
             =>
            {
              val (_, history):
                    ((String, (List[value_type], List[value_type])),
                      List[(String, (List[value_type], List[value_type]))])
                = k;
              (Nat.Nata(history.par.length), (history, groups_fun(k)))
            }),
           groups_fun.keySet.toList))
    val structure:
          (List[Nat.nat]) => (String, (List[value_type], List[value_type]))
      = get_structures(e, log);
    Lista.map[List[(List[Nat.nat], Transition.transition_ext[Unit])],
               ((String, (List[value_type], List[value_type])),
                 List[(List[Nat.nat],
                        Transition.transition_ext[Unit])])](((x:
                        List[(List[Nat.nat], Transition.transition_ext[Unit])])
                       =>
                      (structure((x.head)._1), x)),
                     Lista.sort_key[List[(List[Nat.nat],
   Transition.transition_ext[Unit])],
                                     List[(List[Nat.nat],
    Transition.transition_ext[Unit])]](((x:
   List[(List[Nat.nat], Transition.transition_ext[Unit])])
  =>
 x),
Lista.map[List[(List[Nat.nat], Transition.transition_ext[Unit])],
           List[(List[Nat.nat],
                  Transition.transition_ext[Unit])]](((a:
                 List[(List[Nat.nat], Transition.transition_ext[Unit])])
                =>
               Lista.sort_key[(List[Nat.nat], Transition.transition_ext[Unit]),
                               (List[Nat.nat],
                                 Transition.transition_ext[Unit])](((x:
                               (List[Nat.nat], Transition.transition_ext[Unit]))
                              =>
                             x),
                            a)),
              Lista.map[List[(List[Nat.nat], Transition.transition_ext[Unit])],
                         List[(List[Nat.nat],
                                Transition.transition_ext[Unit])]](((a:
                               List[(List[Nat.nat],
                                      Transition.transition_ext[Unit])])
                              =>
                             a.par.distinct.toList),
                            Lista.map[(Nat.nat,
(List[(String, (List[value_type], List[value_type]))], List[List[Nat.nat]])),
                                       List[(List[Nat.nat],
      Transition.transition_ext[Unit])]](((a:
     (Nat.nat,
       (List[(String, (List[value_type], List[value_type]))],
         List[List[Nat.nat]])))
    =>
   {
     val (_, aa):
           (Nat.nat,
             (List[(String, (List[value_type], List[value_type]))],
               List[List[Nat.nat]]))
       = a
     val (_, ab):
           (List[(String, (List[value_type], List[value_type]))],
             List[List[Nat.nat]])
       = aa;
     Lista.map[List[Nat.nat],
                (List[Nat.nat],
                  Transition.transition_ext[Unit])](((id: List[Nat.nat]) =>
              (id, Inference.get_by_ids(e, id))),
             ab)
   }),
  groups)))))
  }

def needs_latent_code(train:
                        List[(List[Value.value],
                               (Map[Nat.nat, Option[Value.value]],
                                 (Value.value, List[Nat.nat])))]):
      Boolean
  =
  {
    val regs: Set.set[Nat.nat] =
      all_known_regs[List[Value.value], (Value.value, List[Nat.nat])](train);
    Lista.list_ex[(List[Value.value],
                    (Map[Nat.nat, Option[Value.value]],
                      (Value.value,
                        List[Nat.nat])))](((a:
      (List[Value.value],
        (Map[Nat.nat, Option[Value.value]], (Value.value, List[Nat.nat]))))
     =>
    {
      val (i, (r, (p, known))):
            (List[Value.value],
              (Map[Nat.nat, Option[Value.value]], (Value.value, List[Nat.nat])))
        = a;
      Set.Bex[(List[Value.value],
                (Map[Nat.nat, Option[Value.value]],
                  (Value.value,
                    List[Nat.nat])))](Set.remove[(List[Value.value],
           (Map[Nat.nat, Option[Value.value]],
             (Value.value,
               List[Nat.nat])))]((i, (r, (p, known))),
                                  Set.seta[(List[Value.value],
     (Map[Nat.nat, Option[Value.value]],
       (Value.value, List[Nat.nat])))](train)),
                                       ((aa:
   (List[Value.value],
     (Map[Nat.nat, Option[Value.value]], (Value.value, List[Nat.nat]))))
  =>
 {
   val (ia, (ra, (pa, knowna))):
         (List[Value.value],
           (Map[Nat.nat, Option[Value.value]], (Value.value, List[Nat.nat])))
     = aa;
   (Lista.equal_lista[Value.value](i, ia)) && ((r ==
         ra) && ((! (Value.equal_valuea(p,
 pa))) && ((Code_Cardinality.subset[Nat.nat](regs,
      Set.seta[Nat.nat](known))) && ((Code_Cardinality.subset[Nat.nat](regs,
                                Set.seta[Nat.nat](knowna))) && ((Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](known),
                   Set.seta[Nat.nat](r.keySet.toList))) && ((Code_Cardinality.subset[Nat.nat](Set.seta[Nat.nat](knowna),
               Set.seta[Nat.nat](ra.keySet.toList))) && (Code_Cardinality.eq_set[Nat.nat](Set.seta[Nat.nat](knowna),
           Set.seta[Nat.nat](known)))))))))
 }))
    }),
   train)
  }

def historical_derestrict(tree_repeats: Nat.nat, transition_repeats: Nat.nat,
                           pta: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                           log: List[List[(String,
    (List[Value.value], List[Value.value]))]],
                           m: (List[Nat.nat]) =>
                                (List[Nat.nat]) =>
                                  Nat.nat =>
                                    (FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                      (FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
(FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
  ((FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
    Boolean) =>
    Option[FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                           np: (FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat),
       ((Transition.transition_ext[Unit], List[Nat.nat]),
         (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    derestrict(historical_groups(pta, log), tree_repeats, transition_repeats, pta,
              log, m, np)}

} /* object PTA_Generalisation */

object Distinguishing_Guards {

def add_guard(t: Transition.transition_ext[Unit], g: GExp.gexp[VName.vname]):
      Transition.transition_ext[Unit]
  =
  Transition.Guards_update[Unit](((_: List[GExp.gexp[VName.vname]]) =>
                                   Lista.insert[GExp.gexp[VName.vname]](g,
                                 Transition.Guards[Unit](t))),
                                  t)

def trace_collect_training_sets(x0: List[(String,
   (List[Value.value], List[Value.value]))],
                                 uPTA: FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                 s: Nat.nat,
                                 registers: Map[Nat.nat, Option[Value.value]],
                                 t1: List[Nat.nat], t2: List[Nat.nat],
                                 g1: List[(List[Value.value],
    Map[Nat.nat, Option[Value.value]])],
                                 g2: List[(List[Value.value],
    Map[Nat.nat, Option[Value.value]])]):
      (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])],
        List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])
  =
  (x0, uPTA, s, registers, t1, t2, g1, g2) match {
  case (Nil, uPTA, s, registers, t1, t2, g1, g2) => (g1, g2)
  case (((label, (inputs, outputs))::t), uPTA, s, registers, t1, t2, g1, g2) =>
    {
      val (uids, (sa, tran)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](FSet.ffilter[(List[Nat.nat],
                                       (Nat.nat,
 Transition.transition_ext[Unit]))](((a:
(List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit])))
                                       =>
                                      {
val (_, (_, tran)): (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
  = a;
Lista.equal_lista[Option[Value.value]](Transition.apply_outputs[VName.vname](Transition.Outputs[Unit](tran),
                                      AExp.join_ir(inputs, registers)),
Lista.map[Value.value,
           Option[Value.value]](((aa: Value.value) => Some[Value.value](aa)),
                                 outputs))
                                      }),
                                     Inference.i_possible_steps(uPTA, s,
                         registers, label, inputs)))
      val updated: Map[Nat.nat, Option[Value.value]] =
        (Transition.apply_updates(Transition.Updates[Unit](tran),
                                   AExp.join_ir(inputs,
         registers))).apply(registers);
      (if (t1.contains(uids.head))
        trace_collect_training_sets(t, uPTA, sa, updated, t1, t2,
                                     ((inputs, registers)::g1), g2)
        else (if (t2.contains(uids.head))
               trace_collect_training_sets(t, uPTA, sa, updated, t1, t2, g1,
    ((inputs, registers)::g2))
               else trace_collect_training_sets(t, uPTA, sa, updated, t1, t2,
         g1, g2)))
    }
}

def collect_training_sets(x0: List[List[(String,
  (List[Value.value], List[Value.value]))]],
                           uPTA: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                           t1: List[Nat.nat], t2: List[Nat.nat],
                           g1: List[(List[Value.value],
                                      Map[Nat.nat, Option[Value.value]])],
                           g2: List[(List[Value.value],
                                      Map[Nat.nat, Option[Value.value]])]):
      (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])],
        List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])
  =
  (x0, uPTA, t1, t2, g1, g2) match {
  case (Nil, uPTA, t1, t2, g1, g2) => (g1, g2)
  case ((h::t), uPTA, t1, t2, g1, g2) =>
    {
      val (g1a, g2a):
            (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])],
              List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])
        = trace_collect_training_sets(h, uPTA, Nat.zero_nata,
                                       scala.collection.immutable.Map().withDefaultValue(None),
                                       t1, t2, Nil, Nil);
      collect_training_sets(t, uPTA, t1, t2,
                             Lista.union[(List[Value.value],
   Map[Nat.nat, Option[Value.value]])].apply(g1).apply(g1a),
                             Lista.union[(List[Value.value],
   Map[Nat.nat, Option[Value.value]])].apply(g2).apply(g2a))
    }
}

def put_updates(uids: List[Nat.nat],
                 updates: List[(Nat.nat, AExp.aexp[VName.vname])],
                 iefsm:
                   FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, (fromTo, tran)):
                        (List[Nat.nat],
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a
                  val ((u::Nil)): List[Nat.nat] = uid;
                  (if (uids.contains(u))
                    (uid, (fromTo,
                            Transition.transition_exta[Unit](Transition.Label[Unit](tran),
                      Transition.Arity[Unit](tran),
                      Transition.Guards[Unit](tran),
                      Transition.Outputs[Unit](tran),
                      Transition.Updates[Unit](tran) ++ updates, ())))
                    else (uid, (fromTo, tran)))
                }),
               iefsm)

def transfer_updates(e: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      pta: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((a:
                            (List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])))
                           =>
                          {
                            val (tids, aa):
                                  (List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))
                              = a
                            val (ab, b):
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])
                              = aa;
                            ({
                               val (_, _): (Nat.nat, Nat.nat) = ab;
                               ((tran: Transition.transition_ext[Unit]) =>
                                 ((ac: FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                                    =>
                                   put_updates(tids,
        Transition.Updates[Unit](tran), ac)))
                             })(b)
                          }),
                         FSet.sorted_list_of_fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](e),
                         pta)

def distinguish(pta: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                 log: List[List[(String,
                                  (List[Value.value], List[Value.value]))]],
                 t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                 destMerge:
                   FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                 preDestMerge:
                   FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                 old: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                 check:
                   (FSet.fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])]) =>
                     Boolean):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] =
      Inference.get_by_ids(destMerge, t1ID)
    val t2: Transition.transition_ext[Unit] =
      Inference.get_by_ids(destMerge, t2ID)
    val uPTA: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
      = transfer_updates(destMerge, pta)
    val (g1, g2):
          (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])],
            List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])
      = collect_training_sets(log, uPTA, t1ID, t2ID, Nil, Nil);
    (Dirties.findDistinguishingGuards(g1, g2) match {
       case None => None
       case Some((g1a, g2a)) =>
         {
           val rep: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]
             = Inference.replace_transitions(preDestMerge,
      ((t1ID, add_guard(t1, g1a))::(((t2ID, add_guard(t2, g2a))::Nil))));
           (if (check(Inference.tm(rep)))
             Some[FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]](rep)
             else None)
         }
     })
  }

} /* object Distinguishing_Guards */
