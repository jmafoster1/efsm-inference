object HOL {

trait equal[A] {
  val `HOL.equal`: (A, A) => Boolean
}
def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)
object equal {
  implicit def
    `Transition.equal_transition_ext`[A : equal]:
      equal[Transition.transition_ext[A]]
    = new equal[Transition.transition_ext[A]] {
    val `HOL.equal` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition.equal_transition_exta[A](a, b)
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
  implicit def `AExp.equal_aexp`[A : equal]: equal[AExp.aexp[A]] = new
    equal[AExp.aexp[A]] {
    val `HOL.equal` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      AExp.equal_aexpa[A](a, b)
  }
  implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
    val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
  }
  implicit def `Int.equal_int`: equal[Int.int] = new equal[Int.int] {
    val `HOL.equal` = (a: Int.int, b: Int.int) => Int.equal_inta(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Fun {

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
    `Transition_Ordering.ord_transition_ext`[A : HOL.equal : linorder]:
      ord[Transition.transition_ext[A]]
    = new ord[Transition.transition_ext[A]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Ordering.less_eq_transition_ext[A](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Ordering.less_transition_ext[A](a, b)
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
  implicit def `Value.ord_value`: ord[Value.value] = new ord[Value.value] {
    val `Orderings.less_eq` = (a: Value.value, b: Value.value) =>
      Value.less_eq_value(a, b)
    val `Orderings.less` = (a: Value.value, b: Value.value) =>
      Value.less_value(a, b)
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
    `GExp_Orderings.ord_gexp`[A : HOL.equal : linorder]: ord[GExp.gexp[A]] = new
    ord[GExp.gexp[A]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Orderings.less_eq_gexp[A](a, b)
    val `Orderings.less` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Orderings.less_gexp[A](a, b)
  }
  implicit def
    `GExp_Orderings.ord_aexp`[A : HOL.equal : linorder]: ord[AExp.aexp[A]] = new
    ord[AExp.aexp[A]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      GExp_Orderings.less_eq_aexp[A](a, b)
    val `Orderings.less` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      GExp_Orderings.less_aexp[A](a, b)
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
    `Transition_Ordering.preorder_transition_ext`[A : HOL.equal : linorder]:
      preorder[Transition.transition_ext[A]]
    = new preorder[Transition.transition_ext[A]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Ordering.less_eq_transition_ext[A](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Ordering.less_transition_ext[A](a, b)
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
  implicit def `Option_ord.preorder_option`[A : preorder]: preorder[Option[A]] =
    new preorder[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_option[A](a, b)
  }
  implicit def `Value.preorder_value`: preorder[Value.value] = new
    preorder[Value.value] {
    val `Orderings.less_eq` = (a: Value.value, b: Value.value) =>
      Value.less_eq_value(a, b)
    val `Orderings.less` = (a: Value.value, b: Value.value) =>
      Value.less_value(a, b)
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
    `GExp_Orderings.preorder_gexp`[A : HOL.equal : linorder]:
      preorder[GExp.gexp[A]]
    = new preorder[GExp.gexp[A]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Orderings.less_eq_gexp[A](a, b)
    val `Orderings.less` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Orderings.less_gexp[A](a, b)
  }
  implicit def
    `GExp_Orderings.preorder_aexp`[A : HOL.equal : linorder]:
      preorder[AExp.aexp[A]]
    = new preorder[AExp.aexp[A]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      GExp_Orderings.less_eq_aexp[A](a, b)
    val `Orderings.less` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      GExp_Orderings.less_aexp[A](a, b)
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
    `Transition_Ordering.order_transition_ext`[A : HOL.equal : linorder]:
      order[Transition.transition_ext[A]]
    = new order[Transition.transition_ext[A]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Ordering.less_eq_transition_ext[A](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Ordering.less_transition_ext[A](a, b)
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
  implicit def `Option_ord.order_option`[A : order]: order[Option[A]] = new
    order[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_ord.less_option[A](a, b)
  }
  implicit def `Value.order_value`: order[Value.value] = new order[Value.value]
    {
    val `Orderings.less_eq` = (a: Value.value, b: Value.value) =>
      Value.less_eq_value(a, b)
    val `Orderings.less` = (a: Value.value, b: Value.value) =>
      Value.less_value(a, b)
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
    `GExp_Orderings.order_gexp`[A : HOL.equal : linorder]: order[GExp.gexp[A]] =
    new order[GExp.gexp[A]] {
    val `Orderings.less_eq` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Orderings.less_eq_gexp[A](a, b)
    val `Orderings.less` = (a: GExp.gexp[A], b: GExp.gexp[A]) =>
      GExp_Orderings.less_gexp[A](a, b)
  }
  implicit def
    `GExp_Orderings.order_aexp`[A : HOL.equal : linorder]: order[AExp.aexp[A]] =
    new order[AExp.aexp[A]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      GExp_Orderings.less_eq_aexp[A](a, b)
    val `Orderings.less` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      GExp_Orderings.less_aexp[A](a, b)
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
    `Transition_Ordering.linorder_transition_ext`[A : HOL.equal : linorder]:
      linorder[Transition.transition_ext[A]]
    = new linorder[Transition.transition_ext[A]] {
    val `Orderings.less_eq` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Ordering.less_eq_transition_ext[A](a, b)
    val `Orderings.less` =
      (a: Transition.transition_ext[A], b: Transition.transition_ext[A]) =>
      Transition_Ordering.less_transition_ext[A](a, b)
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
    `GExp_Orderings.linorder_aexp`[A : HOL.equal : linorder]:
      linorder[AExp.aexp[A]]
    = new linorder[AExp.aexp[A]] {
    val `Orderings.less_eq` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      GExp_Orderings.less_eq_aexp[A](a, b)
    val `Orderings.less` = (a: AExp.aexp[A], b: AExp.aexp[A]) =>
      GExp_Orderings.less_aexp[A](a, b)
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
  implicit def `Code_Numeral.zero_integer`: zero[BigInt] = new zero[BigInt] {
    val `Groups.zero` = BigInt(0)
  }
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

trait one[A] {
  val `Groups.one`: A
}
def one[A](implicit A: one[A]): A = A.`Groups.one`
object one {
  implicit def `Code_Numeral.one_integer`: one[BigInt] = new one[BigInt] {
    val `Groups.one` = Code_Numeral.one_integera
  }
}

} /* object Groups */

object Rings {

trait zero_neq_one[A] extends Groups.one[A] with Groups.zero[A] {
}
object zero_neq_one {
  implicit def `Code_Numeral.zero_neq_one_integer`: zero_neq_one[BigInt] = new
    zero_neq_one[BigInt] {
    val `Groups.zero` = BigInt(0)
    val `Groups.one` = Code_Numeral.one_integera
  }
}

def of_bool[A : zero_neq_one](x0: Boolean): A = x0 match {
  case true => Groups.one[A]
  case false => Groups.zero[A]
}

} /* object Rings */

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

} /* object Num */

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

def one_integera: BigInt = BigInt(1)

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

def equal_inta(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

def less_eq_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) <= Code_Numeral.integer_of_int(l)

def less_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) < Code_Numeral.integer_of_int(l)

def one_int: int = int_of_integer(BigInt(1))

def plus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) +
                   Code_Numeral.integer_of_int(l))

def zero_int: int = int_of_integer(BigInt(0))

def minus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) -
                   Code_Numeral.integer_of_int(l))

def times_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) *
                   Code_Numeral.integer_of_int(l))

} /* object Int */

object Code_Target_List {

def upt_tailrec(i: Nat.nat, j: Nat.nat, l: List[Nat.nat]): List[Nat.nat] =
  (if (Nat.equal_nata(j, Nat.zero_nata)) l
    else (if (Nat.less_eq_nat(i, Nat.minus_nat(j, Nat.Nata((1)))))
           upt_tailrec(i, Nat.minus_nat(j, Nat.Nata((1))),
                        List(Nat.minus_nat(j, Nat.Nata((1)))) ++ l)
           else l))

} /* object Code_Target_List */

object Product_Type {

def equal_proda[A : HOL.equal, B : HOL.equal](x0: (A, B), x1: (A, B)): Boolean =
  (x0, x1) match {
  case ((x1, x2), (y1, y2)) => (HOL.eq[A](x1, y1)) && (HOL.eq[B](x2, y2))
}

def equal_unita(u: Unit, v: Unit): Boolean = true

def less_eq_unit(uu: Unit, uv: Unit): Boolean = true

def less_unit(uu: Unit, uv: Unit): Boolean = false

} /* object Product_Type */

object Lista {

def list_all[A](f: A => Boolean, l: List[A]): Boolean = l.forall(f)

def equal_lista[A : HOL.equal](xs: List[A], ys: List[A]): Boolean =
  (Nat.equal_nata(Nat.Nata(xs.length),
                   Nat.Nata(ys.length))) && (list_all[(A,
                A)](((a: (A, A)) => {
                                      val (aa, b): (A, A) = a;
                                      HOL.eq[A](aa, b)
                                    }),
                     (xs zip ys)))

def upt(i: Nat.nat, j: Nat.nat): List[Nat.nat] =
  Code_Target_List.upt_tailrec(i, j, Nil)

def fold[A, B](f: A => B => B, xs: List[A], s: B): B =
  Dirties.foldl[B, A](((x: B) => (sa: A) => (f(sa))(x)), s, xs)

def maps[A, B](f: A => List[B], l: List[A]): List[B] = l.flatMap(f)

def upto_aux(i: Int.int, j: Int.int, js: List[Int.int]): List[Int.int] =
  (if (Int.less_int(j, i)) js
    else upto_aux(i, Int.minus_int(j, Int.one_int), j :: js))

def upto(i: Int.int, j: Int.int): List[Int.int] = upto_aux(i, j, Nil)

def foldr[A, B](f: A => B => B, xs: List[A], a: B): B =
  Dirties.foldl[B, A](((x: B) => (y: A) => (f(y))(x)), a, xs.reverse)

def insert[A](x: A, xs: List[A]): List[A] = (if (xs contains x) xs else x :: xs)

def union[A]: (List[A]) => (List[A]) => List[A] =
  ((a: List[A]) => (b: List[A]) =>
    fold[A, List[A]](((aa: A) => (ba: List[A]) => insert[A](aa, ba)), a, b))

def filter[A](l: A => Boolean, f: List[A]): List[A] = f.filter(l)

def list_ex[A](f: A => Boolean, l: List[A]): Boolean = l.exists(f)

def map[A, B](f: A => B, l: List[A]): List[B] = l.map(f)

def product[A, B](xs: List[A], ys: List[B]): List[(A, B)] =
  maps[A, (A, B)](((x: A) => map[B, (A, B)](((a: B) => (x, a)), ys)), xs)

def enumerate[A](n: Nat.nat, xs: List[A]): List[(Nat.nat, A)] =
  ((upt(n, Nat.plus_nata(n, Nat.Nata(xs.length)))) zip xs)

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
  case Set.seta(xs) => sort_key[A, A](((x: A) => x), xs.distinct)
}

} /* object Lista */

object Set {

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]

def Ball[A](x0: set[A], p: A => Boolean): Boolean = (x0, p) match {
  case (seta(xs), p) => Lista.list_all[A](p, xs)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](Lista.map[A, B](f, xs))
}

def insert[A](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, seta(s)) => (if (s contains x) seta[A](s) else seta[A](x :: s))
}

def member[A](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, seta(xs)) => xs contains x
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
  case (Numa(x1), Numa(y1)) => Int.equal_inta(x1, y1)
}

def less_eq_value(x0: value, x1: value): Boolean = (x0, x1) match {
  case (Numa(n), Str(s)) => true
  case (Str(s), Numa(n)) => false
  case (Str(n), Str(s)) => n <= s
  case (Numa(n), Numa(s)) => Int.less_eq_int(n, s)
}

def less_value(x0: value, x1: value): Boolean = (x0, x1) match {
  case (Numa(n), Str(s)) => true
  case (Str(s), Numa(n)) => false
  case (Str(n), Str(s)) => n < s
  case (Numa(n), Numa(s)) => Int.less_int(n, s)
}

def value_eq(a: Option[value], b: Option[value]): Trilean.trilean =
  (if (Optiona.equal_optiona[value](a, b)) Trilean.truea()
    else Trilean.falsea())

def MaybeBoolInt(f: Int.int => Int.int => Boolean, uv: Option[value],
                  uw: Option[value]):
      Trilean.trilean
  =
  (f, uv, uw) match {
  case (f, Some(Numa(a)), Some(Numa(b))) =>
    (if ((f(a))(b)) Trilean.truea() else Trilean.falsea())
  case (uu, None, uw) => Trilean.invalid()
  case (uu, Some(Str(va)), uw) => Trilean.invalid()
  case (uu, uv, None) => Trilean.invalid()
  case (uu, uv, Some(Str(va))) => Trilean.invalid()
}

def value_gt(a: Option[value], b: Option[value]): Trilean.trilean =
  MaybeBoolInt(((x: Int.int) => (y: Int.int) => Int.less_int(y, x)), a, b)

def MaybeArithInt(f: Int.int => Int.int => Int.int, uv: Option[value],
                   uw: Option[value]):
      Option[value]
  =
  (f, uv, uw) match {
  case (f, Some(Numa(x)), Some(Numa(y))) => Some[value](Numa((f(x))(y)))
  case (uu, None, uw) => None
  case (uu, Some(Str(va)), uw) => None
  case (uu, uv, None) => None
  case (uu, uv, Some(Str(va))) => None
}

def value_plus: Option[value] => Option[value] => Option[value] =
  ((a: Option[value]) => (b: Option[value]) =>
    MaybeArithInt(((aa: Int.int) => (ba: Int.int) => Int.plus_int(aa, ba)), a,
                   b))

def value_minus: Option[value] => Option[value] => Option[value] =
  ((a: Option[value]) => (b: Option[value]) =>
    MaybeArithInt(((aa: Int.int) => (ba: Int.int) => Int.minus_int(aa, ba)), a,
                   b))

def value_times: Option[value] => Option[value] => Option[value] =
  ((a: Option[value]) => (b: Option[value]) =>
    MaybeArithInt(((aa: Int.int) => (ba: Int.int) => Int.times_int(aa, ba)), a,
                   b))

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

def less_eq_vname(x0: vname, x1: vname): Boolean = (x0, x1) match {
  case (I(n1), R(n2)) => true
  case (R(n1), I(n2)) => false
  case (I(n1), I(n2)) => Nat.less_eq_nat(n1, n2)
  case (R(n1), R(n2)) => Nat.less_eq_nat(n1, n2)
}

def less_vname(x0: vname, x1: vname): Boolean = (x0, x1) match {
  case (I(n1), R(n2)) => true
  case (R(n1), I(n2)) => false
  case (I(n1), I(n2)) => Nat.less_nat(n1, n2)
  case (R(n1), R(n2)) => Nat.less_nat(n1, n2)
}

} /* object VName */

object AExp {

abstract sealed class aexp[A]
final case class L[A](a: Value.value) extends aexp[A]
final case class V[A](a: A) extends aexp[A]
final case class Plus[A](a: aexp[A], b: aexp[A]) extends aexp[A]
final case class Minus[A](a: aexp[A], b: aexp[A]) extends aexp[A]
final case class Times[A](a: aexp[A], b: aexp[A]) extends aexp[A]

def equal_aexpa[A : HOL.equal](x0: aexp[A], x1: aexp[A]): Boolean = (x0, x1)
  match {
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
  case (Plus(a_1, a_2), s) =>
    Value.value_plus.apply(aval[A](a_1, s)).apply(aval[A](a_2, s))
  case (Minus(a_1, a_2), s) =>
    Value.value_minus.apply(aval[A](a_1, s)).apply(aval[A](a_2, s))
  case (Times(a_1, a_2), s) =>
    Value.value_times.apply(aval[A](a_1, s)).apply(aval[A](a_2, s))
}

def is_lit[A](x0: aexp[A]): Boolean = x0 match {
  case L(uu) => true
  case V(v) => false
  case Plus(v, va) => false
  case Minus(v, va) => false
  case Times(v, va) => false
}

def input2state(n: List[Value.value]): Map[Nat.nat, Option[Value.value]] =
  Lista.fold[(Nat.nat, Value.value),
              Map[Nat.nat, Option[Value.value]]](((a: (Nat.nat, Value.value)) =>
           {
             val (k, v): (Nat.nat, Value.value) = a;
             ((f: Map[Nat.nat, Option[Value.value]]) =>
               f + (k -> (Some[Value.value](v))))
           }),
          Lista.enumerate[Value.value](Nat.zero_nata, n),
          Map().withDefaultValue(None))

def join_ir(i: List[Value.value], r: Map[Nat.nat, Option[Value.value]]):
      VName.vname => Option[Value.value]
  =
  ((a: VName.vname) => (a match {
                          case VName.I(aa) => (input2state(i))(aa)
                          case VName.R(aa) => r(aa)
                        }))

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
}

def enumerate_aexp_regs(x0: aexp[VName.vname]): Set.set[Nat.nat] = x0 match {
  case L(uu) => Set.bot_set[Nat.nat]
  case V(VName.R(n)) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case V(VName.I(uv)) => Set.bot_set[Nat.nat]
  case Plus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
  case Minus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
  case Times(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
}

def enumerate_vars(a: aexp[VName.vname]): Set.set[VName.vname] =
  Set.sup_set[VName.vname](Set.image[Nat.nat,
                                      VName.vname](((aa: Nat.nat) =>
             VName.I(aa)),
            enumerate_aexp_inputs(a)),
                            Set.image[Nat.nat,
                                       VName.vname](((aa: Nat.nat) =>
              VName.R(aa)),
             enumerate_aexp_regs(a)))

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
}

def enumerate_aexp_ints[A](x0: aexp[A]): Set.set[Int.int] = x0 match {
  case L(Value.Str(s)) => Set.bot_set[Int.int]
  case L(Value.Numa(s)) => Set.insert[Int.int](s, Set.bot_set[Int.int])
  case V(uu) => Set.bot_set[Int.int]
  case Plus(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A](a1), enumerate_aexp_ints[A](a2))
  case Minus(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints[A](a1), enumerate_aexp_ints[A](a2))
  case Times(a1, a2) =>
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

object Lattices_Big {

def Max[A : Orderings.linorder](x0: Set.set[A]): A = x0 match {
  case Set.seta(x :: xs) =>
    Lista.fold[A, A](((a: A) => (b: A) => Orderings.max[A](a, b)), xs, x)
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
    (Lista.list_all[A](((a: A) => ys contains a),
                        xs)) && (Lista.list_all[A](((a: A) => xs contains a),
            ys))
}

def subset[A : card_UNIV](x0: Set.set[A], x1: Set.set[A]): Boolean = (x0, x1)
  match {
  case (Set.seta(l1), Set.seta(l2)) =>
    Lista.list_all[A](((a: A) => l2 contains a), l1)
}

} /* object Cardinality */

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
  case (Gt(a_1, a_2), s) =>
    Value.value_gt(AExp.aval[A](a_1, s), AExp.aval[A](a_2, s))
  case (Eq(a_1, a_2), s) =>
    Value.value_eq(AExp.aval[A](a_1, s), AExp.aval[A](a_2, s))
  case (In(v, l), s) =>
    (if ((Lista.map[Value.value,
                     Option[Value.value]](((a: Value.value) =>
    Some[Value.value](a)),
   l)) contains (s(v)))
      Trilean.truea() else Trilean.falsea())
  case (Nor(a_1, a_2), s) =>
    Trilean.maybe_not(Trilean.plus_trilean(gval[A](a_1, s), gval[A](a_2, s)))
}

def fold_In[A](uu: A, x1: List[Value.value]): gexp[A] = (uu, x1) match {
  case (uu, Nil) => Bc[A](false)
  case (v, List(l)) => Eq[A](AExp.V[A](v), AExp.L[A](l))
  case (v, l :: va :: vb) =>
    Lista.fold[Value.value,
                gexp[A]](Fun.comp[gexp[A], (gexp[A]) => gexp[A],
                                   Value.value](((a: gexp[A]) => (b: gexp[A]) =>
          gOr[A](a, b)),
         ((x: Value.value) => Eq[A](AExp.V[A](v), AExp.L[A](x)))),
                          va :: vb, Eq[A](AExp.V[A](v), AExp.L[A](l)))
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

def enumerate_gexp_regs(x0: gexp[VName.vname]): Set.set[Nat.nat] = x0 match {
  case Bc(uu) => Set.bot_set[Nat.nat]
  case Eq(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_regs(v),
                          AExp.enumerate_aexp_regs(va))
  case Gt(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_regs(v),
                          AExp.enumerate_aexp_regs(va))
  case In(v, va) => AExp.enumerate_aexp_regs(AExp.V[VName.vname](v))
  case Nor(v, va) =>
    Set.sup_set[Nat.nat](enumerate_gexp_regs(v), enumerate_gexp_regs(va))
}

def enumerate_vars(g: gexp[VName.vname]): List[VName.vname] =
  Lista.sorted_list_of_set[VName.vname](Set.sup_set[VName.vname](Set.image[Nat.nat,
                                    VName.vname](((a: Nat.nat) => VName.R(a)),
          enumerate_gexp_regs(g)),
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
                                       case Value.Numa(n) =>
 Set.insert[Int.int](n, acc)
                                       case Value.Str(_) => acc
                                     })),
                                   l, Set.bot_set[Int.int])
  case Nor(g1, g2) =>
    Set.sup_set[Int.int](enumerate_gexp_ints[A](g1), enumerate_gexp_ints[A](g2))
}

} /* object GExp */

object Transition {

abstract sealed class transition_ext[A]
final case class
  transition_exta[A](a: String, b: Nat.nat, c: List[GExp.gexp[VName.vname]],
                      d: List[AExp.aexp[VName.vname]],
                      e: List[(Nat.nat, AExp.aexp[VName.vname])], f: A)
  extends transition_ext[A]

def equal_transition_exta[A : HOL.equal](x0: transition_ext[A],
  x1: transition_ext[A]):
      Boolean
  =
  (x0, x1) match {
  case (transition_exta(labela, aritya, guarda, outputsa, updatesa, morea),
         transition_exta(label, arity, guard, outputs, updates, more))
    => (labela ==
         label) && ((Nat.equal_nata(aritya,
                                     arity)) && ((Lista.equal_lista[GExp.gexp[VName.vname]](guarda,
             guard)) && ((Lista.equal_lista[AExp.aexp[VName.vname]](outputsa,
                             outputs)) && ((Lista.equal_lista[(Nat.nat,
                        AExp.aexp[VName.vname])](updatesa,
          updates)) && (HOL.eq[A](morea, more))))))
}

def Updates[A](x0: transition_ext[A]): List[(Nat.nat, AExp.aexp[VName.vname])] =
  x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => updates
}

def Outputs[A](x0: transition_ext[A]): List[AExp.aexp[VName.vname]] = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => outputs
}

def Guard[A](x0: transition_ext[A]): List[GExp.gexp[VName.vname]] = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => guard
}

def enumerate_registers(t: transition_ext[Unit]): Set.set[Nat.nat] =
  Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[GExp.gexp[VName.vname],
                  Set.set[Nat.nat]](((a: GExp.gexp[VName.vname]) =>
                                      GExp.enumerate_gexp_regs(a)),
                                     Guard[Unit](t)))),
                          Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[AExp.aexp[VName.vname],
                   Set.set[Nat.nat]](((a: AExp.aexp[VName.vname]) =>
                                       AExp.enumerate_aexp_regs(a)),
                                      Outputs[Unit](t))))),
     Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                                       AExp.aexp[VName.vname]),
                                      Set.set[Nat.nat]](((a:
                    (Nat.nat, AExp.aexp[VName.vname]))
                   =>
                  {
                    val (_, aa): (Nat.nat, AExp.aexp[VName.vname]) = a;
                    AExp.enumerate_aexp_regs(aa)
                  }),
                 Updates[Unit](t))))),
                        Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                  AExp.aexp[VName.vname]),
                 Set.set[Nat.nat]](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
                                     {
                                       val
 (r, _): (Nat.nat, AExp.aexp[VName.vname]) = a;
                                       AExp.enumerate_aexp_regs(AExp.V[VName.vname](VName.R(r)))
                                     }),
                                    Updates[Unit](t)))))

def max_reg(t: transition_ext[Unit]): Option[Nat.nat] =
  (if (Cardinality.eq_set[Nat.nat](enumerate_registers(t),
                                    Set.bot_set[Nat.nat]))
    None else Some[Nat.nat](Lattices_Big.Max[Nat.nat](enumerate_registers(t))))

def enumerate_ints(t: transition_ext[Unit]): Set.set[Int.int] =
  Set.sup_set[Int.int](Set.sup_set[Int.int](Set.sup_set[Int.int](Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[GExp.gexp[VName.vname],
                  Set.set[Int.int]](((a: GExp.gexp[VName.vname]) =>
                                      GExp.enumerate_gexp_ints[VName.vname](a)),
                                     Guard[Unit](t)))),
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
  case transition_exta(label, arity, guard, outputs, updates, more) => label
}

def Arity[A](x0: transition_ext[A]): Nat.nat = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => arity
}

def same_structure(t1: transition_ext[Unit], t2: transition_ext[Unit]): Boolean
  =
  (Label[Unit](t1) ==
    Label[Unit](t2)) && ((Nat.equal_nata(Arity[Unit](t1),
  Arity[Unit](t2))) && (Nat.equal_nata(Nat.Nata((Outputs[Unit](t1)).length),
Nat.Nata((Outputs[Unit](t2)).length))))

def more[A](x0: transition_ext[A]): A = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => more
}

def Guard_update[A](guarda:
                      (List[GExp.gexp[VName.vname]]) =>
                        List[GExp.gexp[VName.vname]],
                     x1: transition_ext[A]):
      transition_ext[A]
  =
  (guarda, x1) match {
  case (guarda, transition_exta(label, arity, guard, outputs, updates, more)) =>
    transition_exta[A](label, arity, guarda(guard), outputs, updates, more)
}

def Outputs_update[A](outputsa:
                        (List[AExp.aexp[VName.vname]]) =>
                          List[AExp.aexp[VName.vname]],
                       x1: transition_ext[A]):
      transition_ext[A]
  =
  (outputsa, x1) match {
  case (outputsa, transition_exta(label, arity, guard, outputs, updates, more))
    => transition_exta[A](label, arity, guard, outputsa(outputs), updates, more)
}

def Updates_update[A](updatesa:
                        (List[(Nat.nat, AExp.aexp[VName.vname])]) =>
                          List[(Nat.nat, AExp.aexp[VName.vname])],
                       x1: transition_ext[A]):
      transition_ext[A]
  =
  (updatesa, x1) match {
  case (updatesa, transition_exta(label, arity, guard, outputs, updates, more))
    => transition_exta[A](label, arity, guard, outputs, updatesa(updates), more)
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

object GExp_Orderings {

def less_aexp[A : HOL.equal : Orderings.linorder](x0: AExp.aexp[A],
           x1: AExp.aexp[A]):
      Boolean
  =
  (x0, x1) match {
  case (AExp.L(l1), AExp.L(l2)) => Value.less_value(l1, l2)
  case (AExp.L(l1), AExp.V(v2)) => true
  case (AExp.L(l1), AExp.Plus(e1, e2)) => true
  case (AExp.L(l1), AExp.Minus(e1, e2)) => true
  case (AExp.L(l1), AExp.Times(e1, e2)) => true
  case (AExp.V(v1), AExp.L(l1)) => false
  case (AExp.V(v1), AExp.V(v2)) => Orderings.less[A](v1, v2)
  case (AExp.V(v1), AExp.Plus(e1, e2)) => true
  case (AExp.V(v1), AExp.Minus(e1, e2)) => true
  case (AExp.V(v1), AExp.Times(e1, e2)) => true
  case (AExp.Plus(e1, e2), AExp.L(l2)) => false
  case (AExp.Plus(e1, e2), AExp.V(v2)) => false
  case (AExp.Plus(e1a, e2a), AExp.Plus(e1, e2)) =>
    (less_aexp[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
              e1)) && (less_aexp[A](e2a, e2)))
  case (AExp.Plus(e1a, e2a), AExp.Minus(e1, e2)) => true
  case (AExp.Plus(e1a, e2a), AExp.Times(e1, e2)) => true
  case (AExp.Minus(e1, e2), AExp.L(l2)) => false
  case (AExp.Minus(e1, e2), AExp.V(v2)) => false
  case (AExp.Minus(e1a, e2a), AExp.Plus(e1, e2)) => false
  case (AExp.Minus(e1a, e2a), AExp.Minus(e1, e2)) =>
    (less_aexp[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
              e1)) && (less_aexp[A](e2a, e2)))
  case (AExp.Minus(e1a, e2a), AExp.Times(e1, e2)) => true
  case (AExp.Times(e1, e2), AExp.L(l2)) => false
  case (AExp.Times(e1, e2), AExp.V(v2)) => false
  case (AExp.Times(e1a, e2a), AExp.Plus(e1, e2)) => false
  case (AExp.Times(e1a, e2a), AExp.Minus(e1, e2)) => false
  case (AExp.Times(e1a, e2a), AExp.Times(e1, e2)) =>
    (less_aexp[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
              e1)) && (less_aexp[A](e2a, e2)))
}

def less_eq_aexp[A : HOL.equal : Orderings.linorder](e1: AExp.aexp[A],
              e2: AExp.aexp[A]):
      Boolean
  =
  (less_aexp[A](e1, e2)) || (AExp.equal_aexpa[A](e1, e2))

def less_gexp[A : HOL.equal : Orderings.linorder](x0: GExp.gexp[A],
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
    (less_aexp[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
              e1)) && (less_aexp[A](e2a, e2)))
  case (GExp.Eq(e1, e2), GExp.Gt(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.In(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.Nor(v, va)) => true
  case (GExp.Gt(e1, e2), GExp.Bc(b2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Eq(e1, e2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Gt(e1, e2)) =>
    (less_aexp[A](e1a, e1)) || ((AExp.equal_aexpa[A](e1a,
              e1)) && (less_aexp[A](e2a, e2)))
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
    (less_gexp[A](g1a, g1)) || ((GExp.equal_gexpa[A](g1a,
              g1)) && (less_gexp[A](g2a, g2)))
  case (GExp.Nor(g1, g2), GExp.Bc(v)) => false
  case (GExp.Nor(g1, g2), GExp.Eq(v, va)) => false
  case (GExp.Nor(g1, g2), GExp.Gt(v, va)) => false
  case (GExp.Nor(g1, g2), GExp.In(v, va)) => false
}

def less_eq_gexp[A : HOL.equal : Orderings.linorder](e1: GExp.gexp[A],
              e2: GExp.gexp[A]):
      Boolean
  =
  (less_gexp[A](e1, e2)) || (GExp.equal_gexpa[A](e1, e2))

} /* object GExp_Orderings */

object String {

abstract sealed class char
final case class
  Char(a: Boolean, b: Boolean, c: Boolean, d: Boolean, e: Boolean, f: Boolean,
        g: Boolean, h: Boolean)
  extends char

def integer_of_char(x0: char): BigInt = x0 match {
  case Char(b0, b1, b2, b3, b4, b5, b6, b7) =>
    ((((((Rings.of_bool[BigInt](b7) * BigInt(2) + Rings.of_bool[BigInt](b6)) *
           BigInt(2) +
          Rings.of_bool[BigInt](b5)) *
          BigInt(2) +
         Rings.of_bool[BigInt](b4)) *
         BigInt(2) +
        Rings.of_bool[BigInt](b3)) *
        BigInt(2) +
       Rings.of_bool[BigInt](b2)) *
       BigInt(2) +
      Rings.of_bool[BigInt](b1)) *
      BigInt(2) +
      Rings.of_bool[BigInt](b0)
}

def implode(cs: List[char]): String =
  "" ++ (Lista.map[char,
                    BigInt](((a: char) => integer_of_char(a)),
                             cs)).map((k: BigInt) => if (BigInt(0) <= k && k < BigInt(128)) k.charValue else sys.error("Non-ASCII character in literal"))

} /* object String */

object Transition_Ordering {

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
         (Transition.Guard[A](t1),
           (Transition.Outputs[A](t1),
             (Transition.Updates[A](t1), Transition.more[A](t1)))))),
      (Transition.Label[A](t2),
        (Transition.Arity[A](t2),
          (Transition.Guard[A](t2),
            (Transition.Outputs[A](t2),
              (Transition.Updates[A](t2), Transition.more[A](t2)))))))

def less_eq_transition_ext[A : HOL.equal : Orderings.linorder](t1:
                         Transition.transition_ext[A],
                        t2: Transition.transition_ext[A]):
      Boolean
  =
  (less_transition_ext[A](t1, t2)) || (Transition.equal_transition_exta[A](t1,
                                    t2))

} /* object Transition_Ordering */

object FSet {

abstract sealed class fset[A]
final case class fset_of_list[A](a: List[A]) extends fset[A]

def fBex[A](x0: fset[A], f: A => Boolean): Boolean = (x0, f) match {
  case (fset_of_list(l), f) => Lista.list_ex[A](f, l)
}

def fBall[A](x0: fset[A], f: A => Boolean): Boolean = (x0, f) match {
  case (fset_of_list(l), f) => Lista.list_all[A](f, l)
}

def fimage[A, B](f: A => B, x1: fset[A]): fset[B] = (f, x1) match {
  case (f, fset_of_list(as)) => fset_of_list[B](Lista.map[A, B](f, as.distinct))
}

def sup_fset[A](x0: fset[A], x1: fset[A]): fset[A] = (x0, x1) match {
  case (fset_of_list(f1), fset_of_list(f2)) =>
    fset_of_list[A]((f1 ++ f2).distinct)
}

def bot_fset[A]: fset[A] = fset_of_list[A](Nil)

def ffUnion[A](x0: fset[fset[A]]): fset[A] = x0 match {
  case fset_of_list(as) =>
    Lista.fold[fset[A],
                fset[A]](((a: fset[A]) => (b: fset[A]) => sup_fset[A](a, b)),
                          as, bot_fset[A])
}

def ffilter[A](f: A => Boolean, x1: fset[A]): fset[A] = (f, x1) match {
  case (f, fset_of_list(as)) => fset_of_list[A](Lista.filter[A](f, as.distinct))
}

def finsert[A](a: A, x1: fset[A]): fset[A] = (a, x1) match {
  case (a, fset_of_list(as)) => fset_of_list[A](Lista.insert[A](a, as))
}

def fmember[A](a: A, x1: fset[A]): Boolean = (a, x1) match {
  case (a, fset_of_list(as)) => as contains a
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
  case fset_of_list(a :: as) =>
    Lista.fold[A, A](((aa: A) => (b: A) => Orderings.max[A](aa, b)), as, a)
}

def sorted_list_of_fset[A : Orderings.linorder](x0: fset[A]): List[A] = x0 match
  {
  case fset_of_list(l) => (l.distinct).sortWith((Orderings.less))
}

def less_eq_fset[A](x0: fset[A], a: fset[A]): Boolean = (x0, a) match {
  case (fset_of_list(l), a) =>
    Lista.list_all[A](((x: A) => fmember[A](x, a)), l)
}

def size_fset[A](x0: fset[A]): Nat.nat = x0 match {
  case fset_of_list(as) => Nat.Nata((as.distinct).length)
}

def less_fset[A](sa: fset[A], s: fset[A]): Boolean =
  (less_eq_fset[A](sa, s)) && (Nat.less_nat(size_fset[A](sa), size_fset[A](s)))

def equal_fset[A : HOL.equal](x: fset[A], xa1: fset[A]): Boolean = (x, xa1)
  match {
  case (x, fset_of_list(y)) =>
    (Nat.equal_nata(size_fset[A](x),
                     Nat.Nata((y.distinct).length))) && (fBall[A](x,
                           ((a: A) => y contains a)))
}

def minus_fset[A](x0: fset[A], xs: fset[A]): fset[A] = (x0, xs) match {
  case (fset_of_list(a), xs) =>
    fset_of_list[A]((Lista.filter[A](((x: A) => ! (fmember[A](x, xs))),
                                      a)).distinct)
}

} /* object FSet */

object FSet_Utils {

def fSum[A : Groups.comm_monoid_add](x0: FSet.fset[A]): A = x0 match {
  case FSet.fset_of_list(l) =>
    Lista.fold[A, A](((a: A) => (b: A) => Groups.plus[A](a, b)), l.distinct,
                      Groups.zero[A])
}

def fprod[A, B](x0: FSet.fset[A], x1: FSet.fset[B]): FSet.fset[(A, B)] =
  (x0, x1) match {
  case (FSet.fset_of_list(xs), FSet.fset_of_list(ys)) =>
    FSet.fset_of_list[(A, B)]((Lista.maps[A,
   (A, B)](((x: A) => Lista.map[B, (A, B)](((a: B) => (x, a)), ys)),
            xs)).distinct)
}

def fremove[A : HOL.equal](aa: A, x1: FSet.fset[A]): FSet.fset[A] = (aa, x1)
  match {
  case (aa, FSet.fset_of_list(a)) =>
    FSet.fset_of_list[A](Lista.filter[A](((x: A) => ! (HOL.eq[A](x, aa))), a))
}

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

def And[A]: (GExp.gexp[A]) => (GExp.gexp[A]) => GExp.gexp[A] =
  ((a: GExp.gexp[A]) => (b: GExp.gexp[A]) => GExp.gAnd[A](a, b))

def mutex[A : HOL.equal](uu: GExp.gexp[A], uv: GExp.gexp[A]): Boolean = (uu, uv)
  match {
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.Eq(AExp.V(v), AExp.L(l))) =>
    (if (HOL.eq[A](va, v)) ! (Value.equal_valuea(la, l)) else false)
  case (GExp.In(va, la), GExp.Eq(AExp.V(v), AExp.L(l))) =>
    (HOL.eq[A](va, v)) && (! (la contains l))
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.In(v, l)) =>
    (HOL.eq[A](v, va)) && (! (l contains la))
  case (GExp.In(va, la), GExp.In(v, l)) =>
    (HOL.eq[A](va, v)) && (Set.equal_set[Value.value](Set.inf_set[Value.value](Set.seta[Value.value](la),
Set.seta[Value.value](l)),
               Set.bot_set[Value.value]))
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
                        GExp.gexp[VName.vname]](Transition.Guard[Unit](t1),
         Transition.Guard[Unit](t2))))
    false
    else (if (Lista.equal_lista[GExp.gexp[VName.vname]](Transition.Guard[Unit](t1),
                 Transition.Guard[Unit](t2)))
           Dirties.satisfiable(Lista.foldr[GExp.gexp[VName.vname],
    GExp.gexp[VName.vname]](((a: GExp.gexp[VName.vname]) =>
                              (b: GExp.gexp[VName.vname]) =>
                              GExp.gAnd[VName.vname](a, b)),
                             Transition.Guard[Unit](t1),
                             GExp.Bc[VName.vname](true)))
           else Dirties.satisfiable(Lista.foldr[GExp.gexp[VName.vname],
         GExp.gexp[VName.vname]](((a: GExp.gexp[VName.vname]) =>
                                   (b: GExp.gexp[VName.vname]) =>
                                   GExp.gAnd[VName.vname](a, b)),
                                  Transition.Guard[Unit](t1) ++
                                    Transition.Guard[Unit](t2),
                                  GExp.Bc[VName.vname](true)))))

def infer_with_log(stepNo: Nat.nat, k: Nat.nat,
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
                                   ((FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                     FSet.fset[(Nat.nat,
         ((Nat.nat, Nat.nat),
           ((Transition.transition_ext[Unit], List[Nat.nat]),
             (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
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
  (Inference.inference_step(e, FSet.sorted_list_of_fset[Inference.score_ext[Unit]](Inference.k_score(k,
                      e, r)),
                             m, check, np)
     match {
     case None => e
     case Some(newa) =>
       {
         PrettyPrinter.iEFSM2dot(newa, stepNo);
         Log.logStates((FSet.size_fset[Nat.nat](Inference.S(newa))), (FSet.size_fset[Nat.nat](Inference.S(e))));
         (if (FSet.less_fset[Nat.nat](Inference.S(newa), Inference.S(e)))
           infer_with_log(Nat.plus_nata(stepNo, Nat.Nata((1))), k, newa, r, m,
                           check, np)
           else e)
       }
   })

def guardMatch_code(uu: List[GExp.gexp[VName.vname]],
                     uv: List[GExp.gexp[VName.vname]]):
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

def outputMatch_code(uu: List[AExp.aexp[VName.vname]],
                      uv: List[AExp.aexp[VName.vname]]):
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

def mismatched_updates(t1: Transition.transition_ext[Unit],
                        t2: Transition.transition_ext[Unit]):
      Boolean
  =
  Lista.list_ex[Nat.nat](((r: Nat.nat) =>
                           ! ((Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
  Nat.nat](((a: (Nat.nat, AExp.aexp[VName.vname])) => a._1),
            Transition.Updates[Unit](t2))) contains r)),
                          Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
                                     Nat.nat](((a:
          (Nat.nat, AExp.aexp[VName.vname]))
         =>
        a._1),
       Transition.Updates[Unit](t1)))

def input_updates_register_aux(x0: List[(Nat.nat, AExp.aexp[VName.vname])]):
      Option[Nat.nat]
  =
  x0 match {
  case (na, AExp.V(VName.I(n))) :: uu => Some[Nat.nat](n)
  case (v, AExp.L(vb)) :: t => input_updates_register_aux(t)
  case (v, AExp.V(VName.R(vc))) :: t => input_updates_register_aux(t)
  case (v, AExp.Plus(vb, vc)) :: t => input_updates_register_aux(t)
  case (v, AExp.Minus(vb, vc)) :: t => input_updates_register_aux(t)
  case (v, AExp.Times(vb, vc)) :: t => input_updates_register_aux(t)
  case Nil => None
}

def input_updates_register(e: FSet.fset[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])]):
      (Nat.nat, String)
  =
  {
    val (_, t): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
      FSet.fthe_elem[((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit])](FSet.ffilter[((Nat.nat,
                                 Nat.nat),
                                Transition.transition_ext[Unit])](((a:
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))
                             =>
                            {
                              val (_, t):
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])
                                = a;
                              ! (Optiona.is_none[Nat.nat](input_updates_register_aux(Transition.Updates[Unit](t))))
                            }),
                           e))
    val (Some(n)): Option[Nat.nat] =
      input_updates_register_aux(Transition.Updates[Unit](t));
    (n, Transition.Label[Unit](t))
  }

} /* object Code_Generation */

object Inference {

abstract sealed class score_ext[A]
final case class score_exta[A](a: Nat.nat, b: Nat.nat, c: Nat.nat, d: A) extends
  score_ext[A]

def equal_score_ext[A : HOL.equal](x0: score_ext[A], x1: score_ext[A]): Boolean
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
  (less_score_ext[A](s1, s2)) || (equal_score_ext[A](s1, s2))

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
                                 Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                      Set.seta[Nat.nat](x._1))),
                                t)))._2)._1)._2

def uids(e: FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))]):
      FSet.fset[Nat.nat]
  =
  FSet.ffUnion[Nat.nat](FSet.fimage[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])),
                                     FSet.fset[Nat.nat]](Fun.comp[List[Nat.nat],
                           FSet.fset[Nat.nat],
                           (List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))](((a:
                              List[Nat.nat])
                             =>
                            FSet.fset_of_list[Nat.nat](a)),
                           ((a: (List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])))
                              =>
                             a._1)),
                  e))

def infer:
      Nat.nat =>
        (FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
          ((List[Nat.nat]) =>
            (List[Nat.nat]) =>
              (FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                Nat.nat) =>
            ((List[Nat.nat]) =>
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
                        ((FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], List[Nat.nat]),
  (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
                          Option[FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]) =>
              ((FSet.fset[((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])]) =>
                Boolean) =>
                ((FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit],
                                   List[Nat.nat]),
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat]))))]) =>
                  FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]
  =
  ((a: Nat.nat) =>
    (b: FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (c: (List[Nat.nat]) =>
          (List[Nat.nat]) =>
            (FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              Nat.nat)
      =>
    (d: (List[Nat.nat]) =>
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
                    ((FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]) =>
                      FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    ((Transition.transition_ext[Unit],
                                       List[Nat.nat]),
                                      (Transition.transition_ext[Unit],
List[Nat.nat]))))]) =>
                      Option[FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]])
      =>
    (e: (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
          Boolean)
      =>
    (f: (FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
          FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        ((Transition.transition_ext[Unit], List[Nat.nat]),
                          (Transition.transition_ext[Unit], List[Nat.nat]))))])
      =>
    Code_Generation.infer_with_log(Nat.zero_nata, a, b, c, d, e, f))

def satisfies_trace_prim(uu: FSet.fset[((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit])],
                          uv: Nat.nat, uw: Map[Nat.nat, Option[Value.value]],
                          x3: List[(String,
                                     (List[Value.value], List[Value.value]))]):
      Boolean
  =
  (uu, uv, uw, x3) match {
  case (uu, uv, uw, Nil) => true
  case (e, s, d, (l, (i, p)) :: t) =>
    {
      val poss_steps: FSet.fset[(Nat.nat, Transition.transition_ext[Unit])] =
        EFSM.possible_steps(e, s, d, l, i);
      (if (FSet_Utils.fis_singleton[(Nat.nat,
                                      Transition.transition_ext[Unit])](poss_steps))
        {
          val (sa, ta): (Nat.nat, Transition.transition_ext[Unit]) =
            FSet.fthe_elem[(Nat.nat,
                             Transition.transition_ext[Unit])](poss_steps);
          (if (Lista.equal_lista[Option[Value.value]](EFSM.apply_outputs[VName.vname](Transition.Outputs[Unit](ta),
       AExp.join_ir(i, d)),
               Lista.map[Value.value,
                          Option[Value.value]](((a: Value.value) =>
         Some[Value.value](a)),
        p)))
            satisfies_trace_prim(e, sa,
                                  EFSM.apply_updates(Transition.Updates[Unit](ta),
              AExp.join_ir(i, d), d),
                                  t)
            else false)
        }
        else FSet.fBex[(Nat.nat,
                         Transition.transition_ext[Unit])](poss_steps,
                    ((a: (Nat.nat, Transition.transition_ext[Unit])) =>
                      {
                        val (sa, ta): (Nat.nat, Transition.transition_ext[Unit])
                          = a;
                        (Lista.equal_lista[Option[Value.value]](EFSM.apply_outputs[VName.vname](Transition.Outputs[Unit](ta),
                 AExp.join_ir(i, d)),
                         Lista.map[Value.value,
                                    Option[Value.value]](((aa: Value.value) =>
                   Some[Value.value](aa)),
                  p))) && (satisfies_trace_prim(e, sa,
         EFSM.apply_updates(Transition.Updates[Unit](ta), AExp.join_ir(i, d),
                             d),
         t))
                      })))
    }
}

def satisfies_trace(e: FSet.fset[((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])],
                     s: Nat.nat, d: Map[Nat.nat, Option[Value.value]],
                     l: List[(String, (List[Value.value], List[Value.value]))]):
      Boolean
  =
  satisfies_trace_prim(e, s, d, l)

def satisfies(t: Set.set[List[(String,
                                (List[Value.value], List[Value.value]))]],
               e: FSet.fset[((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])]):
      Boolean
  =
  Set.Ball[List[(String,
                  (List[Value.value],
                    List[Value.value]))]](t,
   ((a: List[(String, (List[Value.value], List[Value.value]))]) =>
     satisfies_trace(e, Nat.zero_nata, Map().withDefaultValue(None), a)))

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
                          ((FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                            FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat),
  ((Transition.transition_ext[Unit], List[Nat.nat]),
    (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
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
          satisfies(Set.seta[List[(String,
                                    (List[Value.value],
                                      List[Value.value]))]](l),
                     a));
    infer.apply(n).apply(pta).apply(r).apply(m).apply(check).apply(np)
  }

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
       froma)) && ((Nat.equal_nata(to, toa)) && (Transition.equal_transition_exta[Unit](t,
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
 toa)) && (Transition.equal_transition_exta[Unit](t, ta))))
                                (Lista.union[Nat.nat].apply(uida).apply(uid),
                                  ((froma, toa), ta))
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
                               val (ac, ba): (Nat.nat, Nat.nat) = ab;
                               ((c: Transition.transition_ext[Unit]) =>
                                 (d: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                                   =>
                                 insert_transition(uid, ac, ba, c, d))
                             })(b)
                          }),
                         FSet.sorted_list_of_fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](e),
                         FSet.bot_fset[(List[Nat.nat],
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

def directly_subsumes:
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
        (FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
          Nat.nat =>
            Nat.nat =>
              (Transition.transition_ext[Unit]) =>
                (Transition.transition_ext[Unit]) => Boolean
  =
  ((a: FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
     =>
    (b: FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (c: Nat.nat) => (d: Nat.nat) => (e: Transition.transition_ext[Unit]) =>
    (f: Transition.transition_ext[Unit]) =>
    Dirties.scalaDirectlySubsumes(a, b, c, d, e, f))

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
                                 Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                      Set.seta[Nat.nat](x._1))),
                                t)))._2)._1)._1

def merge_transitions(oldEFSM:
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
                       t_1: Transition.transition_ext[Unit], u_1: List[Nat.nat],
                       t_2: Transition.transition_ext[Unit], u_2: List[Nat.nat],
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
                                     ((FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                       FSet.fset[(Nat.nat,
           ((Nat.nat, Nat.nat),
             ((Transition.transition_ext[Unit], List[Nat.nat]),
               (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
                                       Option[FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                       np: (FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                             FSet.fset[(Nat.nat,
 ((Nat.nat, Nat.nat),
   ((Transition.transition_ext[Unit], List[Nat.nat]),
     (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (Lista.list_all[Nat.nat](((id: Nat.nat) =>
                                 directly_subsumes.apply(oldEFSM).apply(destMerge).apply(origin(List(id),
                 oldEFSM)).apply(origin(u_1, destMerge)).apply(t_2).apply(t_1)),
                                u_1))
    Some[FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit]))]](merge_transitions_aux(destMerge,
  u_1, u_2))
    else (if (Lista.list_all[Nat.nat](((id: Nat.nat) =>
directly_subsumes.apply(oldEFSM).apply(destMerge).apply(origin(List(id),
                        oldEFSM)).apply(origin(u_2,
        destMerge)).apply(t_1).apply(t_2)),
                                       u_2))
           Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](merge_transitions_aux(destMerge,
         u_2, u_1))
           else (((((((modifier(u_1))(u_2))(origin(u_1,
            destMerge)))(destMerge))(preDestMerge))(oldEFSM))(np)
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
  FSet.equal_fset[(Nat.nat,
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
  (if (Nat.less_nat(y, x)) merge_states_aux(x, y, t)
    else merge_states_aux(y, x, t))

def resolve_nondeterminism(uu: List[(Nat.nat, Nat.nat)],
                            x1: List[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 ((Transition.transition_ext[Unit], List[Nat.nat]),
   (Transition.transition_ext[Unit], List[Nat.nat]))))],
                            uv: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            newa: FSet.fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            uw: (List[Nat.nat]) =>
                                  (List[Nat.nat]) =>
                                    Nat.nat =>
                                      (FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
(FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
  (FSet.fset[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
    ((FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], List[Nat.nat]),
                      (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
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
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (uu, x1, uv, newa, uw, check, np) match {
  case (uu, Nil, uv, newa, uw, check, np) =>
    (if ((deterministic(newa, np)) && (check(tm(newa))))
      Some[FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](newa)
      else None)
  case (closed, (from, ((dest_1, dest_2), ((t_1, u_1), (t_2, u_2)))) :: ss,
         oldEFSM, newEFSM, m, check, np)
    => (if (closed contains (dest_1, dest_2)) None
         else {
                val destMerge:
                      FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]
                  = merge_states(dest_1, dest_2, newEFSM);
                (merge_transitions(oldEFSM, newEFSM, destMerge, t_1, u_1, t_2,
                                    u_2, m, np)
                   match {
                   case None =>
                     resolve_nondeterminism((dest_1, dest_2) :: closed, ss,
     oldEFSM, newEFSM, m, check, np)
                   case Some(newa) =>
                     {
                       val newScores:
                             List[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      ((Transition.transition_ext[Unit],
 List[Nat.nat]),
(Transition.transition_ext[Unit], List[Nat.nat]))))]
                         = FSet.sorted_list_of_fset[(Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (Transition.transition_ext[Unit],
                    List[Nat.nat]))))](np(newa));
                       (if (Product_Lexorder.less_prod[Nat.nat,
                (Nat.nat,
                  Nat.nat)]((FSet.size_fset[(List[Nat.nat],
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](newa),
                              (FSet.size_fset[Nat.nat](S(newa)),
                                Nat.Nata(newScores.length))),
                             (FSet.size_fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](newEFSM),
                               (FSet.size_fset[Nat.nat](S(newEFSM)),
                                 Nat.Nata(ss.length)))))
                         (resolve_nondeterminism(closed, newScores, oldEFSM,
          newa, m, check, np)
                            match {
                            case None =>
                              resolve_nondeterminism((dest_1, dest_2) :: closed,
              ss, oldEFSM, newEFSM, m, check, np)
                            case Some(a) =>
                              Some[FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]](a)
                          })
                         else None)
                     }
                 })
              })
}

def merge(e: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
           s_1: Nat.nat, s_2: Nat.nat,
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
                          ((FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                            FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat),
  ((Transition.transition_ext[Unit], List[Nat.nat]),
    (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
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
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (Nat.equal_nata(s_1, s_2)) None
    else {
           val ea: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]
             = make_distinct(merge_states(s_1, s_2, e));
           resolve_nondeterminism(Nil, FSet.sorted_list_of_fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            ((Transition.transition_ext[Unit], List[Nat.nat]),
                              (Transition.transition_ext[Unit],
                                List[Nat.nat]))))](np(ea)),
                                   e, ea, m, check, np)
         })

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
       (aa zip b)
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
            id :: aa),
           paths_of_length(Nat.minus_nat(m, Nat.Nata((1))), uu, d))
              }),
             outgoing));
           FSet.ffilter[List[List[Nat.nat]]](((l: List[List[Nat.nat]]) =>
       Nat.equal_nata(Nat.Nata(l.length),
                       Nat.Suc(Nat.minus_nat(m, Nat.Nata((1)))))),
      a)
         })

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
score_exta[Unit](score_from_list(p1, p2, e, strat), s1, s2, ())
                                      }),
                                     paths);
    FSet.ffilter[score_ext[Unit]](((x: score_ext[Unit]) =>
                                    Nat.less_nat(Nat.zero_nata,
          Score[Unit](x))),
                                   a)
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

def max_uid(e: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Option[Nat.nat]
  =
  {
    val uidsa: FSet.fset[Nat.nat] = uids(e);
    (if (FSet.equal_fset[Nat.nat](uidsa, FSet.bot_fset[Nat.nat])) None
      else Some[Nat.nat](FSet.fMax[Nat.nat](uidsa)))
  }

def all_regs(e: FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]):
      Set.set[Nat.nat]
  =
  EFSM.all_regs(tm(e))

def max_uid_total(e: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  (max_uid(e) match {
     case None => Nat.zero_nata
     case Some(u) => u
   })

def make_outputs(x0: List[Value.value]): List[AExp.aexp[VName.vname]] = x0 match
  {
  case Nil => Nil
  case h :: t => AExp.L[VName.vname](h) :: make_outputs(t)
}

def make_guard(x0: List[Value.value], uu: Nat.nat): List[GExp.gexp[VName.vname]]
  =
  (x0, uu) match {
  case (Nil, uu) => Nil
  case (h :: t, n) =>
    GExp.Eq[VName.vname](AExp.V[VName.vname](VName.I(n)),
                          AExp.L[VName.vname](h)) ::
      make_guard(t, Nat.plus_nata(n, Nat.Nata((1))))
}

def add_transition(e: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                    s: Nat.nat, label: String, inputs: List[Value.value],
                    outputs: List[Value.value]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.finsert[(List[Nat.nat],
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))]((List(Nat.plus_nata(max_uid_total(e),
                                   Nat.Nata((1)))),
                ((s, Nat.plus_nata(EFSM.maxS(tm(e)), Nat.Nata((1)))),
                  Transition.transition_exta[Unit](label,
            Nat.Nata(inputs.length), make_guard(inputs, Nat.zero_nata),
            make_outputs(outputs), Nil, ()))),
               e)

def make_branch(e: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                 uu: Nat.nat, uv: Map[Nat.nat, Option[Value.value]],
                 x3: List[(String, (List[Value.value], List[Value.value]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (e, uu, uv, x3) match {
  case (e, uu, uv, Nil) => e
  case (e, s, r, (label, (inputs, outputs)) :: t) =>
    (EFSM.step(tm(e), s, r, label, inputs) match {
       case None =>
         make_branch(add_transition(e, s, label, inputs, outputs),
                      Nat.plus_nata(EFSM.maxS(tm(e)), Nat.Nata((1))), r, t)
       case Some((_, (sa, (outputsa, updated)))) =>
         (if (Lista.equal_lista[Option[Value.value]](outputsa,
              Lista.map[Value.value,
                         Option[Value.value]](((a: Value.value) =>
        Some[Value.value](a)),
       outputs)))
           make_branch(e, sa, updated, t)
           else make_branch(add_transition(e, s, label, inputs, outputs),
                             Nat.plus_nata(EFSM.maxS(tm(e)), Nat.Nata((1))), r,
                             t))
     })
}

def make_pta_aux(l: List[List[(String,
                                (List[Value.value], List[Value.value]))]],
                  e: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((h:
                            List[(String,
                                   (List[Value.value], List[Value.value]))])
                           =>
                          (ea: FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                            =>
                          make_branch(ea, Nat.zero_nata,
                                       Map().withDefaultValue(None), h)),
                         l, e)

def make_pta(log: List[List[(String, (List[Value.value], List[Value.value]))]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  make_pta_aux(log, FSet.bot_fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))])

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
                   Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
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
                       (if (Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
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

def literal_args[A](x0: GExp.gexp[A]): Boolean = x0 match {
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
  case GExp.Nor(v, va) => (literal_args[A](v)) && (literal_args[A](va))
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

def null_modifier(uu: List[Nat.nat], uv: List[Nat.nat], uw: Nat.nat,
                   ux: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   uy: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   uz: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   va: (FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
                         FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       ((Transition.transition_ext[Unit],
  List[Nat.nat]),
 (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  None

def inference_step(uu: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                    x1: List[score_ext[Unit]],
                    uv: (List[Nat.nat]) =>
                          (List[Nat.nat]) =>
                            Nat.nat =>
                              (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                (FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                  (FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                    ((FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                      FSet.fset[(Nat.nat,
          ((Nat.nat, Nat.nat),
            ((Transition.transition_ext[Unit], List[Nat.nat]),
              (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
                                      Option[FSet.fset[(List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                    uw: (FSet.fset[((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])]) =>
                          Boolean,
                    ux: (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], List[Nat.nat]),
  (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (uu, x1, uv, uw, ux) match {
  case (uu, Nil, uv, uw, ux) => None
  case (e, h :: t, m, check, np) =>
    (merge(e, S1[Unit](h), S2[Unit](h), m, check, np) match {
       case None => inference_step(e, t, m, check, np)
       case Some(a) =>
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](a)
     })
}

def try_heuristics(x0: List[(List[Nat.nat]) =>
                              (List[Nat.nat]) =>
                                Nat.nat =>
                                  (FSet.fset[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                    (FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                      (FSet.fset[(List[Nat.nat],
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
((FSet.fset[(List[Nat.nat],
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
  FSet.fset[(Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[Unit], List[Nat.nat]),
                  (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
  Option[FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]],
                    uu: (FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], List[Nat.nat]),
  (Transition.transition_ext[Unit], List[Nat.nat]))))]):
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
                  ((FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]) =>
                    FSet.fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  ((Transition.transition_ext[Unit],
                                     List[Nat.nat]),
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat]))))]) =>
                    Option[FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]]
  =
  (x0, uu) match {
  case (Nil, uu) =>
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
      (g: (FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]) =>
            FSet.fset[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          ((Transition.transition_ext[Unit], List[Nat.nat]),
                            (Transition.transition_ext[Unit],
                              List[Nat.nat]))))])
        =>
      null_modifier(a, b, c, d, e, f, g))
  case (h :: t, np) =>
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
      (npa: (FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            ((Transition.transition_ext[Unit], List[Nat.nat]),
                              (Transition.transition_ext[Unit],
                                List[Nat.nat]))))])
        =>
      (((((((h(a))(b))(c))(d))(e))(f))(npa) match {
         case None =>
           (try_heuristics(t, npa)).apply(a).apply(b).apply(c).apply(d).apply(e).apply(f).apply(npa)
         case Some(aa) =>
           Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](aa)
       }))
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
                       l) && ((Nat.equal_nata(Nat.Nata(i.length),
       Transition.Arity[Unit](t))) && (GExp.apply_guards(Transition.Guard[Unit](t),
                  AExp.join_ir(i, r))))))
                                })(b)
                             }),
                            e))

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
       ((FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
         FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       ((Transition.transition_ext[Unit], List[Nat.nat]),
                         (Transition.transition_ext[Unit],
                           List[Nat.nat]))))]) =>
         Option[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]]],
                          uv: (FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat),
      ((Transition.transition_ext[Unit], List[Nat.nat]),
        (Transition.transition_ext[Unit], List[Nat.nat]))))]):
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
                  ((FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]) =>
                    FSet.fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  ((Transition.transition_ext[Unit],
                                     List[Nat.nat]),
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat]))))]) =>
                    Option[FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]]
  =
  (uu, x1, uv) match {
  case (uu, Nil, uv) =>
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
      (g: (FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]) =>
            FSet.fset[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          ((Transition.transition_ext[Unit], List[Nat.nat]),
                            (Transition.transition_ext[Unit],
                              List[Nat.nat]))))])
        =>
      null_modifier(a, b, c, d, e, f, g))
  case (check, h :: t, np) =>
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
      (npa: (FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            ((Transition.transition_ext[Unit], List[Nat.nat]),
                              (Transition.transition_ext[Unit],
                                List[Nat.nat]))))])
        =>
      (((((((h(a))(b))(c))(d))(e))(f))(npa) match {
         case None =>
           (try_heuristics_check(check, t,
                                  npa)).apply(a).apply(b).apply(c).apply(d).apply(e).apply(f).apply(npa)
         case Some(ea) =>
           (if (check(tm(ea)))
             Some[FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]](ea)
             else (try_heuristics_check(check, t,
 npa)).apply(a).apply(b).apply(c).apply(d).apply(e).apply(f).apply(npa))
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

def outgoing_transitions_from(e: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                               s: Nat.nat):
      FSet.fset[Transition.transition_ext[Unit]]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               Transition.transition_ext[Unit]](((a:
            (List[Nat.nat],
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
           =>
          {
            val (_, (_, t)):
                  (List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
              = a;
            t
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
                            val (orig, _): (Nat.nat, Nat.nat) = ab;
                            ((_: Transition.transition_ext[Unit]) =>
                              Nat.equal_nata(orig, s))
                          })(b)
                       }),
                      e))

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

def Str(s: List[String.char]): Value.value = Value.Str(String.implode(s))

def maxS(t: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]):
      Nat.nat
  =
  (if (FSet.equal_fset[((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit])](t,
                    FSet.bot_fset[((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])]))
    Nat.zero_nata
    else FSet.fMax[Nat.nat](FSet.sup_fset[Nat.nat](FSet.fimage[((Nat.nat,
                          Nat.nat),
                         Transition.transition_ext[Unit]),
                        Nat.nat](((a: ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))
                                    =>
                                   {
                                     val (aa, b):
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                                       = a;
                                     ({
val (origin, _): (Nat.nat, Nat.nat) = aa;
((_: Transition.transition_ext[Unit]) => origin)
                                      })(b)
                                   }),
                                  t),
            FSet.fimage[((Nat.nat, Nat.nat), Transition.transition_ext[Unit]),
                         Nat.nat](((a: ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))
                                     =>
                                    {
                                      val
(aa, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = a;
                                      ({
 val (_, dest): (Nat.nat, Nat.nat) = aa;
 ((_: Transition.transition_ext[Unit]) => dest)
                                       })(b)
                                    }),
                                   t))))

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
                 l) && ((Nat.equal_nata(Nat.Nata(i.length),
 Transition.Arity[Unit](t))) && (GExp.apply_guards(Transition.Guard[Unit](t),
            AExp.join_ir(i, r))))))
                          })(b)
                       }),
                      e))

def apply_updates(x0: List[(Nat.nat, AExp.aexp[VName.vname])],
                   uu: VName.vname => Option[Value.value],
                   newa: Map[Nat.nat, Option[Value.value]]):
      Map[Nat.nat, Option[Value.value]]
  =
  (x0, uu, newa) match {
  case (Nil, uu, newa) => newa
  case (h :: t, old, newa) =>
    (apply_updates(t, old,
                    newa)) + ((h._1) -> (AExp.aval[VName.vname](h._2, old)))
}

def apply_outputs[A](p: List[AExp.aexp[A]], s: A => Option[Value.value]):
      List[Option[Value.value]]
  =
  Lista.map[AExp.aexp[A],
             Option[Value.value]](((pa: AExp.aexp[A]) => AExp.aval[A](pa, s)),
                                   p)

def step(e: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
          s: Nat.nat, r: Map[Nat.nat, Option[Value.value]], l: String,
          i: List[Value.value]):
      Option[(Transition.transition_ext[Unit],
               (Nat.nat,
                 (List[Option[Value.value]],
                   Map[Nat.nat, Option[Value.value]])))]
  =
  (Dirties.randomMember[(Nat.nat,
                          Transition.transition_ext[Unit])](possible_steps(e, s,
                                    r, l, i))
     match {
     case None => None
     case Some((sa, t)) =>
       Some[(Transition.transition_ext[Unit],
              (Nat.nat,
                (List[Option[Value.value]],
                  Map[Nat.nat, Option[Value.value]])))]((t,
                  (sa, (apply_outputs[VName.vname](Transition.Outputs[Unit](t),
            AExp.join_ir(i, r)),
                         apply_updates(Transition.Updates[Unit](t),
AExp.join_ir(i, r), r)))))
   })

def choice(ta: Transition.transition_ext[Unit],
            t: Transition.transition_ext[Unit]):
      Boolean
  =
  Code_Generation.choice_cases(ta, t)

def accepts_prim(e: FSet.fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])],
                  s: Nat.nat, d: Map[Nat.nat, Option[Value.value]],
                  x3: List[(String, List[Value.value])]):
      Boolean
  =
  (e, s, d, x3) match {
  case (e, s, d, Nil) => true
  case (e, s, d, (l, i) :: t) =>
    {
      val poss_steps: FSet.fset[(Nat.nat, Transition.transition_ext[Unit])] =
        possible_steps(e, s, d, l, i);
      (if (FSet_Utils.fis_singleton[(Nat.nat,
                                      Transition.transition_ext[Unit])](poss_steps))
        {
          val (sa, ta): (Nat.nat, Transition.transition_ext[Unit]) =
            FSet.fthe_elem[(Nat.nat,
                             Transition.transition_ext[Unit])](poss_steps);
          accepts_prim(e, sa,
                        apply_updates(Transition.Updates[Unit](ta),
                                       AExp.join_ir(i, d), d),
                        t)
        }
        else FSet.fBex[(Nat.nat,
                         Transition.transition_ext[Unit])](poss_steps,
                    ((a: (Nat.nat, Transition.transition_ext[Unit])) =>
                      {
                        val (sa, ta): (Nat.nat, Transition.transition_ext[Unit])
                          = a;
                        accepts_prim(e, sa,
                                      apply_updates(Transition.Updates[Unit](ta),
             AExp.join_ir(i, d), d),
                                      t)
                      })))
    }
}

def accepts(e: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
             s: Nat.nat, d: Map[Nat.nat, Option[Value.value]],
             t: List[(String, List[Value.value])]):
      Boolean
  =
  accepts_prim(e, s, d, t)

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
    (if (FSet.equal_fset[Option[Nat.nat]](maxes,
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
                              Transition.enumerate_registers(aa)
                            }),
                           FSet.fset[((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])](e)))

} /* object EFSM */

object Equals {

def equality_pairs(x0: List[GExp.gexp[VName.vname]]):
      List[(Nat.nat, Value.value)]
  =
  x0 match {
  case Nil => Nil
  case GExp.Eq(AExp.V(VName.I(n)), AExp.L(l)) :: t =>
    (n, l) :: equality_pairs(t)
  case GExp.Bc(v) :: t => equality_pairs(t)
  case GExp.Eq(AExp.L(vb), va) :: t => equality_pairs(t)
  case GExp.Eq(AExp.V(VName.R(vc)), va) :: t => equality_pairs(t)
  case GExp.Eq(AExp.Plus(vb, vc), va) :: t => equality_pairs(t)
  case GExp.Eq(AExp.Minus(vb, vc), va) :: t => equality_pairs(t)
  case GExp.Eq(AExp.Times(vb, vc), va) :: t => equality_pairs(t)
  case GExp.Eq(v, AExp.V(vb)) :: t => equality_pairs(t)
  case GExp.Eq(v, AExp.Plus(vb, vc)) :: t => equality_pairs(t)
  case GExp.Eq(v, AExp.Minus(vb, vc)) :: t => equality_pairs(t)
  case GExp.Eq(v, AExp.Times(vb, vc)) :: t => equality_pairs(t)
  case GExp.Gt(v, va) :: t => equality_pairs(t)
  case GExp.In(v, va) :: t => equality_pairs(t)
  case GExp.Nor(v, va) :: t => equality_pairs(t)
}

def is_equals(t: Transition.transition_ext[Unit]): Boolean =
  {
    val ep: List[(Nat.nat, Value.value)] =
      equality_pairs(Transition.Guard[Unit](t));
    (Transition.Label[Unit](t) ==
      "equals") && ((Nat.equal_nata(Transition.Arity[Unit](t),
                                     Code_Numeral.nat_of_integer(BigInt(2)))) && ((Value.equal_valuea((ep(Code_Numeral.integer_of_nat(Nat.zero_nata).toInt))._2,
                       (ep(Code_Numeral.integer_of_nat(Nat.Nata((1))).toInt))._2)) && ((Lista.equal_lista[Nat.nat](Lista.map[(Nat.nat,
       Value.value),
      Nat.nat](((a: (Nat.nat, Value.value)) => a._1), ep),
                                    List(Nat.zero_nata,
  Nat.Nata((1))))) && (Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t),
                          List(AExp.L[VName.vname](EFSM.Str(List(String.Char(false,
                                      false, true, false, true, true, true,
                                      false),
                          String.Char(false, true, false, false, true, true,
                                       true, false),
                          String.Char(true, false, true, false, true, true,
                                       true, false),
                          String.Char(true, false, true, false, false, true,
                                       true, false))))))))))
  }

def gen_eq: Transition.transition_ext[Unit] =
  Transition.transition_exta[Unit]("equals",
                                    Code_Numeral.nat_of_integer(BigInt(2)),
                                    List(GExp.Eq[VName.vname](AExp.V[VName.vname](VName.I(Nat.zero_nata)),
                       AExp.V[VName.vname](VName.I(Nat.Nata((1)))))),
                                    List(AExp.L[VName.vname](EFSM.Str(List(String.Char(false,
        false, true, false, true, true, true, false),
                                    String.Char(false, true, false, false, true,
         true, true, false),
                                    String.Char(true, false, true, false, true,
         true, true, false),
                                    String.Char(true, false, true, false, false,
         true, true, false))))),
                                    Nil, ())

def equals(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
            destMerge:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
            preDestMerge:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
            oldEFSM:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
            uu: (FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit],
                                   List[Nat.nat]),
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] =
      Inference.get_by_ids(destMerge, t1ID)
    val t2: Transition.transition_ext[Unit] =
      Inference.get_by_ids(destMerge, t2ID);
    (if ((is_equals(t1)) && (is_equals(t2)))
      Some[FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](Inference.replace_transitions(destMerge,
            List((t1ID, gen_eq), (t2ID, gen_eq))))
      else None)
  }

def gen_neq: Transition.transition_ext[Unit] =
  Transition.transition_exta[Unit]("equals",
                                    Code_Numeral.nat_of_integer(BigInt(2)),
                                    List(GExp.Eq[VName.vname](AExp.V[VName.vname](VName.I(Nat.zero_nata)),
                       AExp.V[VName.vname](VName.I(Nat.Nata((1)))))),
                                    List(AExp.L[VName.vname](EFSM.Str(List(String.Char(false,
        false, true, false, true, true, true, false),
                                    String.Char(false, true, false, false, true,
         true, true, false),
                                    String.Char(true, false, true, false, true,
         true, true, false),
                                    String.Char(true, false, true, false, false,
         true, true, false))))),
                                    Nil, ())

def not_equals(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                destMerge:
                  FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
                preDestMerge:
                  FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
                oldEFSM:
                  FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
                uu: (FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    ((Transition.transition_ext[Unit],
                                       List[Nat.nat]),
                                      (Transition.transition_ext[Unit],
List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] =
      Inference.get_by_ids(destMerge, t1ID)
    val t2: Transition.transition_ext[Unit] =
      Inference.get_by_ids(destMerge, t2ID);
    (if ((is_equals(t1)) && (is_equals(t2)))
      Some[FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](Inference.replace_transitions(destMerge,
            List((t1ID, gen_neq), (t2ID, gen_neq))))
      else None)
  }

} /* object Equals */

object EFSM_Dot {

def vname2dot(x0: VName.vname): String = x0 match {
  case VName.I(n) =>
    "i<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub>"
  case VName.R(n) =>
    "r<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub>"
}

def value2dot(x0: Value.value): String = x0 match {
  case Value.Str(s) => "\"" + s.replace("\\", "\\\\") + "\""
  case Value.Numa(n) => Code_Numeral.integer_of_int(n).toString()
}

def aexp2dot(x0: AExp.aexp[VName.vname]): String = x0 match {
  case AExp.L(v) => value2dot(v)
  case AExp.V(v) => vname2dot(v)
  case AExp.Plus(a1, a2) => aexp2dot(a1) + " + " + aexp2dot(a2)
  case AExp.Minus(a1, a2) => aexp2dot(a1) + " - " + aexp2dot(a2)
  case AExp.Times(a1, a2) => aexp2dot(a1) + " &times; " + aexp2dot(a2)
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
  case v :: va => "&#91;" + (updates2dot_aux(v :: va)).mkString(", ") + "&#93;"
}

def outputs2dot(x0: List[AExp.aexp[VName.vname]], uu: Nat.nat): List[String] =
  (x0, uu) match {
  case (Nil, uu) => Nil
  case (h :: t, n) =>
    "o<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub> := " +
      aexp2dot(h) ::
      outputs2dot(t, Nat.plus_nata(n, Nat.Nata((1))))
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
  case GExp.Nor(g1, g2) => "!(" + gexp2dot(g1) + "&or;" + gexp2dot(g2) + ")"
}

def guards2dot_aux(l: List[GExp.gexp[VName.vname]]): List[String] =
  Lista.map[GExp.gexp[VName.vname],
             String](((a: GExp.gexp[VName.vname]) => gexp2dot(a)), l)

def guards2dot(x0: List[GExp.gexp[VName.vname]]): String = x0 match {
  case Nil => ""
  case v :: va => "&#91;" + (guards2dot_aux(v :: va)).mkString(", ") + "&#93;"
}

def transition2dot(t: Transition.transition_ext[Unit]): String =
  Transition.Label[Unit](t) + ":" +
    Code_Numeral.integer_of_nat(Transition.Arity[Unit](t)).toString() +
    guards2dot(Transition.Guard[Unit](t)) +
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

def aexp2sal(x0: AExp.aexp[VName.vname]): String = x0 match {
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

def gexp2sal(x0: GExp.gexp[VName.vname]): String = x0 match {
  case GExp.Bc(true) => "True"
  case GExp.Bc(false) => "False"
  case GExp.Eq(a1, a2) => "value_eq(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case GExp.Gt(a1, a2) => "value_gt(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case GExp.In(v, l) =>
    (Lista.map[Value.value,
                String](((la: Value.value) =>
                          "gval(value_eq(" + aexp2sal(AExp.V[VName.vname](v)) +
                            ", " +
                            aexp2sal(AExp.L[VName.vname](la)) +
                            "))"),
                         l)).mkString(" OR ")
  case GExp.Nor(g1, g2) =>
    "NOT (gval(" + gexp2sal(g1) + ") OR gval( " + gexp2sal(g2) + "))"
}

def guards2sal(x0: List[GExp.gexp[VName.vname]]): String = x0 match {
  case Nil => "TRUE"
  case v :: va =>
    (Lista.map[GExp.gexp[VName.vname],
                String](((a: GExp.gexp[VName.vname]) => gexp2sal(a)),
                         v :: va)).mkString(" AND ")
}

def aexp2sal_num(x0: AExp.aexp[VName.vname], uu: Nat.nat): String = (x0, uu)
  match {
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

def gexp2sal_num(x0: GExp.gexp[VName.vname], uu: Nat.nat): String = (x0, uu)
  match {
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
                            aexp2sal_num(AExp.V[VName.vname](v), m) +
                            ", " +
                            aexp2sal_num(AExp.L[VName.vname](la), m) +
                            "))"),
                         l)).mkString(" OR ")
  case (GExp.Nor(g1, g2), m) =>
    "NOT (" + gexp2sal_num(g1, m) + " OR " + gexp2sal_num(g2, m) + ")"
}

def guards2sal_num(x0: List[GExp.gexp[VName.vname]], uu: Nat.nat): String =
  (x0, uu) match {
  case (Nil, uu) => "TRUE"
  case (v :: va, m) =>
    (Lista.map[GExp.gexp[VName.vname],
                String](((g: GExp.gexp[VName.vname]) => gexp2sal_num(g, m)),
                         v :: va)).mkString(" AND ")
}

} /* object efsm2sal */

object Finite_Set {

def card[A](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.seta(xs) => Nat.Nata((xs.distinct).length)
}

} /* object Finite_Set */

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

def index(x0: List[Value.value], uu: Nat.nat, uv: ioTag, uw: Nat.nat):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  (x0, uu, uv, uw) match {
  case (Nil, uu, uv, uw) => FSet.bot_fset[(Nat.nat, (ioTag, Nat.nat))]
  case (h :: t, eventNo, io, ind) =>
    FSet.finsert[(Nat.nat,
                   (ioTag,
                     Nat.nat))]((eventNo, (io, ind)),
                                 index(t, eventNo, io,
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
                        EFSM.accepts(Inference.tm(e), sa,
                                      EFSM.apply_updates(Transition.Updates[Unit](t),
                  AExp.join_ir(i, r), r),
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
                    (sa, (u, EFSM.apply_updates(Transition.Updates[Unit](t),
         AExp.join_ir(i, r), r)))))
     })
  }

def lookup(x0: (Nat.nat, (ioTag, Nat.nat)),
            t: List[(String, (List[Value.value], List[Value.value]))]):
      Value.value
  =
  (x0, t) match {
  case ((eventNo, (In(), inx)), t) =>
    {
      val (_, (inputs, _)): (String, (List[Value.value], List[Value.value])) =
        t(Code_Numeral.integer_of_nat(eventNo).toInt);
      inputs(Code_Numeral.integer_of_nat(inx).toInt)
    }
  case ((eventNo, (Out(), inx)), t) =>
    {
      val (_, (_, outputs)): (String, (List[Value.value], List[Value.value])) =
        t(Code_Numeral.integer_of_nat(eventNo).toInt);
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
                                  Transition.Guard[Unit](t)),
                                    Transition.Outputs[Unit](t),
                                    (outputX,
                                      AExp.V[VName.vname](VName.I(inputX))) ::
                                      Transition.Updates[Unit](t),
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
  case (h :: t, e) =>
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
                                    Transition.Guard[Unit](t),
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
      = (relevant zip replacements)
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

def io_index(eventNo: Nat.nat, inputs: List[Value.value],
              outputs: List[Value.value]):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  FSet.sup_fset[(Nat.nat,
                  (ioTag,
                    Nat.nat))](index(inputs, eventNo, In(), Nat.zero_nata),
                                index(outputs, eventNo, Out(), Nat.zero_nata))

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
 val (eventNo, aa): (Nat.nat, (String, (List[Value.value], List[Value.value])))
   = x
 val (_, ab): (String, (List[Value.value], List[Value.value])) = aa
 val (ac, b): (List[Value.value], List[Value.value]) = ab;
 io_index(eventNo, ac, b)
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
                                    (outputX,
                                      AExp.V[VName.vname](VName.I(inputX))) ::
                                      Transition.Updates[Unit](t),
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
  case (a, ((t1, (io1, i1)), (t2, (io2, i2))) :: t) =>
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
                                    case GExp.Eq(AExp.V(VName.R(_)), _) => g
                                    case GExp.Eq(AExp.Plus(_, _), _) => g
                                    case GExp.Eq(AExp.Minus(_, _), _) => g
                                    case GExp.Eq(AExp.Times(_, _), _) => g
                                    case GExp.Gt(_, _) => g
                                    case GExp.In(_, _) => g
                                    case GExp.Nor(_, _) => g
                                  })),
                                Transition.Guard[Unit](t)),
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
      = (relevant zip replacements)
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
  case (n, e, s, r, h :: t) =>
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
    ((walk_up_to(e1, e, Nat.zero_nata, Map().withDefaultValue(None), t),
       (io1, inx1)),
      (walk_up_to(e2, e, Nat.zero_nata, Map().withDefaultValue(None), t),
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
                         (l zip (Lista.map[List[(String,
          (List[Value.value], List[Value.value]))],
    FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
                (Nat.nat,
                  (ioTag,
                    Nat.nat)))]](((a: List[(String,
     (List[Value.value], List[Value.value]))])
                                    =>
                                   get_by_id_intratrace_matches(a)),
                                  l)))))

def heuristic_1(l: List[List[(String,
                               (List[Value.value], List[Value.value]))]]):
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
                  ((FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]) =>
                    FSet.fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  ((Transition.transition_ext[Unit],
                                     List[Nat.nat]),
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat]))))]) =>
                    Option[FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]]
  =
  ((t1: List[Nat.nat]) => (t2: List[Nat.nat]) => (_: Nat.nat) =>
    (newa: FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (_: FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (old: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (np: (FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))]) =>
           FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], List[Nat.nat]),
                           (Transition.transition_ext[Unit], List[Nat.nat]))))])
      =>
    (modify(find_intertrace_matches(l, old), t1, t2, newa) match {
       case None => None
       case Some(newEFSM) =>
         Inference.resolve_nondeterminism(Nil,
   FSet.sorted_list_of_fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit],
                                   List[Nat.nat]),
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat]))))](np(newEFSM)),
   old, newEFSM,
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
     (g: (FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))]) =>
           FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], List[Nat.nat]),
                           (Transition.transition_ext[Unit], List[Nat.nat]))))])
       =>
     Inference.null_modifier(a, b, c, d, e, f, g)),
   ((_: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
     true),
   np)
     }))

def heuristic_2(l: List[List[(String,
                               (List[Value.value], List[Value.value]))]]):
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
                  ((FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]) =>
                    FSet.fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  ((Transition.transition_ext[Unit],
                                     List[Nat.nat]),
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat]))))]) =>
                    Option[FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]]
  =
  ((t1: List[Nat.nat]) => (t2: List[Nat.nat]) => (_: Nat.nat) =>
    (newa: FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (_: FSet.fset[(List[Nat.nat],
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (old: FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (np: (FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))]) =>
           FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], List[Nat.nat]),
                           (Transition.transition_ext[Unit], List[Nat.nat]))))])
      =>
    (modify_2(find_intertrace_matches(l, old), t1, t2, newa) match {
       case None => None
       case Some(newEFSM) =>
         Inference.resolve_nondeterminism(Nil,
   FSet.sorted_list_of_fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit],
                                   List[Nat.nat]),
                                  (Transition.transition_ext[Unit],
                                    List[Nat.nat]))))](Inference.nondeterministic_pairs(newEFSM)),
   old, newEFSM,
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
     (g: (FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))]) =>
           FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], List[Nat.nat]),
                           (Transition.transition_ext[Unit], List[Nat.nat]))))])
       =>
     Inference.null_modifier(a, b, c, d, e, f, g)),
   ((_: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
     true),
   np)
     }))

} /* object Store_Reuse */

object Ignore_Inputs {

def drop_guards(t: Transition.transition_ext[Unit]):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t), Nil,
                                    Transition.Outputs[Unit](t),
                                    Transition.Updates[Unit](t), ())

def enumerate_outputs(e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       l: String, a: Nat.nat):
      FSet.fset[List[AExp.aexp[VName.vname]]]
  =
  FSet.fimage[(List[Nat.nat],
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               List[AExp.aexp[VName.vname]]](((aa:
         (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
        =>
       {
         val (_, ab):
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
           = aa
         val (_, ac): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
           ab;
         Transition.Outputs[Unit](ac)
       }),
      FSet.ffilter[(List[Nat.nat],
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit]))](((b:
                      (List[Nat.nat],
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                     =>
                    {
                      val (_, (_, t)):
                            (List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))
                        = b;
                      (Transition.Label[Unit](t) ==
                        l) && (Nat.equal_nata(Transition.Arity[Unit](t), a))
                    }),
                   e))

def drop_inputs(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                 newa: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                 old: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                 uu: FSet.fset[(List[Nat.nat],
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                 np: (FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]) =>
                       FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     ((Transition.transition_ext[Unit],
List[Nat.nat]),
                                       (Transition.transition_ext[Unit],
 List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID);
    Inference.get_by_ids(newa, t2ID);
    (if (FSet_Utils.fis_singleton[List[AExp.aexp[VName.vname]]](enumerate_outputs(newa,
   Transition.Label[Unit](t1), Transition.Arity[Unit](t1))))
      Some[FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](FSet.fimage[(List[Nat.nat],
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
                                     val (id, (route, t)):
   (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                       = a;
                                     (if (Lista.equal_lista[Nat.nat](id, t1ID))
                                       (id, (route, drop_guards(t)))
                                       else (id, (route, t)))
                                   }),
                                  FSet.ffilter[(List[Nat.nat],
         ((Nat.nat, Nat.nat),
           Transition.transition_ext[Unit]))](((a:
          (List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
         =>
        {
          val (id, _):
                (List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
            = a;
          ! (Lista.equal_lista[Nat.nat](id, t2ID))
        }),
       newa)))
      else None)
  }

def transitionwise_drop_inputs(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                                s: Nat.nat,
                                newa: FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                uu: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                old: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                np: (FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                      FSet.fset[(Nat.nat,
          ((Nat.nat, Nat.nat),
            ((Transition.transition_ext[Unit], List[Nat.nat]),
              (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t2ID);
    (if (Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t1),
            Transition.Outputs[Unit](t2)))
      Some[FSet.fset[(List[Nat.nat],
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](Inference.replace_transitions(newa,
            List((t1ID, drop_guards(t1)), (t2ID, drop_guards(t1)))))
      else None)
  }

} /* object Ignore_Inputs */

object Same_Register {

def updates(x0: List[(Nat.nat, AExp.aexp[VName.vname])]): Option[VName.vname] =
  x0 match {
  case List((n, a)) => Some[VName.vname](VName.R(n))
  case Nil => None
  case v :: vb :: vc => None
}

def a_replace_with(x0: AExp.aexp[VName.vname], uu: Nat.nat, uv: Nat.nat):
      AExp.aexp[VName.vname]
  =
  (x0, uu, uv) match {
  case (AExp.L(v), uu, uv) => AExp.L[VName.vname](v)
  case (AExp.V(v), r1, r2) =>
    (if (VName.equal_vnamea(v, VName.R(r1))) AExp.V[VName.vname](VName.R(r2))
      else AExp.V[VName.vname](v))
  case (AExp.Plus(a1, a2), r1, r2) =>
    AExp.Plus[VName.vname](a_replace_with(a1, r1, r2),
                            a_replace_with(a2, r1, r2))
  case (AExp.Minus(a1, a2), r1, r2) =>
    AExp.Minus[VName.vname](a_replace_with(a1, r1, r2),
                             a_replace_with(a2, r1, r2))
  case (AExp.Times(a1, a2), r1, r2) =>
    AExp.Times[VName.vname](a_replace_with(a1, r1, r2),
                             a_replace_with(a2, r1, r2))
}

def u_replace_with(x0: (Nat.nat, AExp.aexp[VName.vname]), r1: Nat.nat,
                    r2: Nat.nat):
      (Nat.nat, AExp.aexp[VName.vname])
  =
  (x0, r1, r2) match {
  case ((r, a), r1, r2) =>
    ((if (Nat.equal_nata(r, r1)) r2 else r), a_replace_with(a, r1, r2))
}

def g_replace_with(x0: GExp.gexp[VName.vname], uu: Nat.nat, uv: Nat.nat):
      GExp.gexp[VName.vname]
  =
  (x0, uu, uv) match {
  case (GExp.Bc(x), uu, uv) => GExp.Bc[VName.vname](x)
  case (GExp.Eq(a1, a2), r1, r2) =>
    GExp.Eq[VName.vname](a_replace_with(a1, r1, r2), a_replace_with(a2, r1, r2))
  case (GExp.Gt(a1, a2), r1, r2) =>
    GExp.Eq[VName.vname](a_replace_with(a1, r1, r2), a_replace_with(a2, r1, r2))
  case (GExp.Nor(g1, g2), r1, r2) =>
    GExp.Nor[VName.vname](g_replace_with(g1, r1, r2),
                           g_replace_with(g2, r1, r2))
  case (GExp.In(v, s), r1, r2) => GExp.In[VName.vname](v, s)
}

def t_replace_with(t: Transition.transition_ext[Unit], r1: Nat.nat,
                    r2: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    Lista.map[GExp.gexp[VName.vname],
       GExp.gexp[VName.vname]](((g: GExp.gexp[VName.vname]) =>
                                 g_replace_with(g, r1, r2)),
                                Transition.Guard[Unit](t)),
                                    Lista.map[AExp.aexp[VName.vname],
       AExp.aexp[VName.vname]](((p: AExp.aexp[VName.vname]) =>
                                 a_replace_with(p, r1, r2)),
                                Transition.Outputs[Unit](t)),
                                    Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
       (Nat.nat,
         AExp.aexp[VName.vname])](((u: (Nat.nat, AExp.aexp[VName.vname])) =>
                                    u_replace_with(u, r1, r2)),
                                   Transition.Updates[Unit](t)),
                                    ())

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
                  (u, (tf, t_replace_with(t, r1, r2)))
                }),
               e)

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
                   uv: (FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
                         FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       ((Transition.transition_ext[Unit],
  List[Nat.nat]),
 (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t2ID)
    val ut1: Option[VName.vname] = updates(Transition.Updates[Unit](t1))
    val ut2: Option[VName.vname] = updates(Transition.Updates[Unit](t2));
    (if (Transition.same_structure(t1, t2))
      ((ut1, ut2) match {
         case (None, _) => None
         case (Some(VName.I(_)), _) => None
         case (Some(VName.R(_)), None) => None
         case (Some(VName.R(_)), Some(VName.I(_))) => None
         case (Some(VName.R(r1)), Some(VName.R(r2))) =>
           Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](replace_with(newa,
r1, r2))
       })
      else None)
  }

} /* object Same_Register */

object Code_Target_Nat {

def int_of_nat(n: Nat.nat): Int.int =
  Int.int_of_integer(Code_Numeral.integer_of_nat(n))

} /* object Code_Target_Nat */

object Increment_Reset {

def guardMatch[A, B](t1: Transition.transition_ext[A],
                      t2: Transition.transition_ext[B]):
      Boolean
  =
  Code_Generation.guardMatch_code(Transition.Guard[A](t1),
                                   Transition.Guard[B](t2))

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
                                    Transition.Guard[Unit](t),
                                    Transition.Outputs[Unit](t),
                                    (newReg,
                                      AExp.L[VName.vname](Value.Numa(Int.zero_int))) ::
                                      Transition.Updates[Unit](t),
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
                        np: (FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                              FSet.fset[(Nat.nat,
  ((Nat.nat, Nat.nat),
    ((Transition.transition_ext[Unit], List[Nat.nat]),
      (Transition.transition_ext[Unit], List[Nat.nat]))))]):
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
    List(AExp.Plus[VName.vname](AExp.V[VName.vname](newReg),
                                 AExp.V[VName.vname](VName.I(Nat.zero_nata)))),
    (r, AExp.Plus[VName.vname](AExp.V[VName.vname](newReg),
                                AExp.V[VName.vname](VName.I(Nat.zero_nata)))) ::
      Transition.Updates[Unit](t1),
    ())
        val newT2: Transition.transition_ext[Unit] =
          Transition.transition_exta[Unit](Transition.Label[Unit](t2),
    Transition.Arity[Unit](t2), Nil,
    List(AExp.Plus[VName.vname](AExp.V[VName.vname](newReg),
                                 AExp.V[VName.vname](VName.I(Nat.zero_nata)))),
    (r, AExp.Plus[VName.vname](AExp.V[VName.vname](newReg),
                                AExp.V[VName.vname](VName.I(Nat.zero_nata)))) ::
      Transition.Updates[Unit](t2),
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
        val newEFSM:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
          = struct_replace_all(struct_replace_all(initialised, t2, newT2), t1,
                                newT1);
        Inference.resolve_nondeterminism(Nil,
  FSet.sorted_list_of_fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit],
                                  List[Nat.nat]),
                                 (Transition.transition_ext[Unit],
                                   List[Nat.nat]))))](np(newEFSM)),
  old, newEFSM,
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
    (g: (FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
          FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        ((Transition.transition_ext[Unit], List[Nat.nat]),
                          (Transition.transition_ext[Unit], List[Nat.nat]))))])
      =>
    Inference.null_modifier(a, b, c, d, e, f, g)),
  ((_: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
    true),
  np)
      }
      else None)
  }

} /* object Increment_Reset */

object Weak_Subsumption {

def maxBy[A, B : Orderings.linorder](f: A => B, a: A, b: A): A =
  (if (Orderings.less[B](f(b), f(a))) a else b)

def weak_subsumption(log: List[List[(String,
                                      (List[Value.value], List[Value.value]))]],
                      t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
                      newa: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                      uu: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                      old: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))],
                      uv: (FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]) =>
                            FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat),
  ((Transition.transition_ext[Unit], List[Nat.nat]),
    (Transition.transition_ext[Unit], List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t2ID);
    (if (Transition.same_structure(t1, t2))
      {
        val newEFSM:
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
          = Inference.replace_all(newa, List(t1ID, t2ID),
                                   maxBy[Transition.transition_ext[Unit],
  (Nat.nat,
    List[AExp.aexp[VName.vname]])](((x: Transition.transition_ext[Unit]) =>
                                     ((Fun.comp[List[(Nat.nat,
               AExp.aexp[VName.vname])],
         Nat.nat,
         Transition.transition_ext[Unit]](((a:
      List[(Nat.nat, AExp.aexp[VName.vname])])
     =>
    Nat.Nata(a.length)),
   ((a: Transition.transition_ext[Unit]) =>
     Transition.Updates[Unit](a)))).apply(x),
                                       Lista.map[(Nat.nat,
           AExp.aexp[VName.vname]),
          AExp.aexp[VName.vname]](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
                                    a._2),
                                   Transition.Updates[Unit](x)))),
                                    t1, t2));
        (if (Inference.satisfies(Set.seta[List[(String,
         (List[Value.value], List[Value.value]))]](log),
                                  Inference.tm(newEFSM)))
          Some[FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]](newEFSM)
          else None)
      }
      else None)
  }

} /* object Weak_Subsumption */

object Least_Upper_Bound {

def all_literal_args[A](t: Transition.transition_ext[A]): Boolean =
  Lista.list_all[GExp.gexp[VName.vname]](((a: GExp.gexp[VName.vname]) =>
   Inference.literal_args[VName.vname](a)),
  Transition.Guard[A](t))

def merge_in_in(v: VName.vname, l: List[Value.value],
                 x2: List[GExp.gexp[VName.vname]]):
      List[GExp.gexp[VName.vname]]
  =
  (v, l, x2) match {
  case (v, l, Nil) => List(GExp.In[VName.vname](v, l))
  case (va, la, GExp.Eq(AExp.V(v), AExp.L(l)) :: t) =>
    (if (VName.equal_vnamea(va, v))
      GExp.In[VName.vname](va, Lista.insert[Value.value](l, la)) :: t
      else GExp.Eq[VName.vname](AExp.V[VName.vname](v),
                                 AExp.L[VName.vname](l)) ::
             merge_in_in(va, la, t))
  case (va, la, GExp.In(v, l) :: t) =>
    (if (VName.equal_vnamea(va, v))
      GExp.In[VName.vname](va, Lista.union[Value.value].apply(la).apply(l)) :: t
      else GExp.In[VName.vname](v, l) :: merge_in_in(va, la, t))
  case (v, l, GExp.Bc(va) :: t) =>
    GExp.Bc[VName.vname](va) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(AExp.L(vc), vb) :: t) =>
    GExp.Eq[VName.vname](AExp.L[VName.vname](vc), vb) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(AExp.Plus(vc, vd), vb) :: t) =>
    GExp.Eq[VName.vname](AExp.Plus[VName.vname](vc, vd), vb) ::
      merge_in_in(v, l, t)
  case (v, l, GExp.Eq(AExp.Minus(vc, vd), vb) :: t) =>
    GExp.Eq[VName.vname](AExp.Minus[VName.vname](vc, vd), vb) ::
      merge_in_in(v, l, t)
  case (v, l, GExp.Eq(AExp.Times(vc, vd), vb) :: t) =>
    GExp.Eq[VName.vname](AExp.Times[VName.vname](vc, vd), vb) ::
      merge_in_in(v, l, t)
  case (v, l, GExp.Eq(va, AExp.V(vc)) :: t) =>
    GExp.Eq[VName.vname](va, AExp.V[VName.vname](vc)) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Plus(vc, vd)) :: t) =>
    GExp.Eq[VName.vname](va, AExp.Plus[VName.vname](vc, vd)) ::
      merge_in_in(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Minus(vc, vd)) :: t) =>
    GExp.Eq[VName.vname](va, AExp.Minus[VName.vname](vc, vd)) ::
      merge_in_in(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Times(vc, vd)) :: t) =>
    GExp.Eq[VName.vname](va, AExp.Times[VName.vname](vc, vd)) ::
      merge_in_in(v, l, t)
  case (v, l, GExp.Gt(va, vb) :: t) =>
    GExp.Gt[VName.vname](va, vb) :: merge_in_in(v, l, t)
  case (v, l, GExp.Nor(va, vb) :: t) =>
    GExp.Nor[VName.vname](va, vb) :: merge_in_in(v, l, t)
}

def merge_in_eq(v: VName.vname, l: Value.value,
                 x2: List[GExp.gexp[VName.vname]]):
      List[GExp.gexp[VName.vname]]
  =
  (v, l, x2) match {
  case (v, l, Nil) =>
    List(GExp.Eq[VName.vname](AExp.V[VName.vname](v), AExp.L[VName.vname](l)))
  case (va, la, GExp.Eq(AExp.V(v), AExp.L(l)) :: t) =>
    (if ((VName.equal_vnamea(va, v)) && (! (Value.equal_valuea(la, l))))
      GExp.In[VName.vname](va, List(la, l)) :: t
      else GExp.Eq[VName.vname](AExp.V[VName.vname](v),
                                 AExp.L[VName.vname](l)) ::
             merge_in_eq(va, la, t))
  case (va, la, GExp.In(v, l) :: t) =>
    (if (VName.equal_vnamea(va, v))
      GExp.In[VName.vname](va, (la :: l).distinct) :: t
      else GExp.In[VName.vname](v, l) :: merge_in_eq(va, la, t))
  case (v, l, GExp.Bc(va) :: t) =>
    GExp.Bc[VName.vname](va) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(AExp.L(vc), vb) :: t) =>
    GExp.Eq[VName.vname](AExp.L[VName.vname](vc), vb) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(AExp.Plus(vc, vd), vb) :: t) =>
    GExp.Eq[VName.vname](AExp.Plus[VName.vname](vc, vd), vb) ::
      merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(AExp.Minus(vc, vd), vb) :: t) =>
    GExp.Eq[VName.vname](AExp.Minus[VName.vname](vc, vd), vb) ::
      merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(AExp.Times(vc, vd), vb) :: t) =>
    GExp.Eq[VName.vname](AExp.Times[VName.vname](vc, vd), vb) ::
      merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(va, AExp.V(vc)) :: t) =>
    GExp.Eq[VName.vname](va, AExp.V[VName.vname](vc)) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Plus(vc, vd)) :: t) =>
    GExp.Eq[VName.vname](va, AExp.Plus[VName.vname](vc, vd)) ::
      merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Minus(vc, vd)) :: t) =>
    GExp.Eq[VName.vname](va, AExp.Minus[VName.vname](vc, vd)) ::
      merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Times(vc, vd)) :: t) =>
    GExp.Eq[VName.vname](va, AExp.Times[VName.vname](vc, vd)) ::
      merge_in_eq(v, l, t)
  case (v, l, GExp.Gt(va, vb) :: t) =>
    GExp.Gt[VName.vname](va, vb) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Nor(va, vb) :: t) =>
    GExp.Nor[VName.vname](va, vb) :: merge_in_eq(v, l, t)
}

def merge_guards(x0: List[GExp.gexp[VName.vname]],
                  g2: List[GExp.gexp[VName.vname]]):
      List[GExp.gexp[VName.vname]]
  =
  (x0, g2) match {
  case (Nil, g2) => g2
  case (GExp.Eq(AExp.V(v), AExp.L(l)) :: t, g2) =>
    merge_guards(t, merge_in_eq(v, l, g2))
  case (GExp.In(v, l) :: t, g2) => merge_guards(t, merge_in_in(v, l, g2))
  case (GExp.Bc(v) :: t, g2) => GExp.Bc[VName.vname](v) :: merge_guards(t, g2)
  case (GExp.Eq(AExp.L(vb), va) :: t, g2) =>
    GExp.Eq[VName.vname](AExp.L[VName.vname](vb), va) :: merge_guards(t, g2)
  case (GExp.Eq(AExp.Plus(vb, vc), va) :: t, g2) =>
    GExp.Eq[VName.vname](AExp.Plus[VName.vname](vb, vc), va) ::
      merge_guards(t, g2)
  case (GExp.Eq(AExp.Minus(vb, vc), va) :: t, g2) =>
    GExp.Eq[VName.vname](AExp.Minus[VName.vname](vb, vc), va) ::
      merge_guards(t, g2)
  case (GExp.Eq(AExp.Times(vb, vc), va) :: t, g2) =>
    GExp.Eq[VName.vname](AExp.Times[VName.vname](vb, vc), va) ::
      merge_guards(t, g2)
  case (GExp.Eq(v, AExp.V(vb)) :: t, g2) =>
    GExp.Eq[VName.vname](v, AExp.V[VName.vname](vb)) :: merge_guards(t, g2)
  case (GExp.Eq(v, AExp.Plus(vb, vc)) :: t, g2) =>
    GExp.Eq[VName.vname](v, AExp.Plus[VName.vname](vb, vc)) ::
      merge_guards(t, g2)
  case (GExp.Eq(v, AExp.Minus(vb, vc)) :: t, g2) =>
    GExp.Eq[VName.vname](v, AExp.Minus[VName.vname](vb, vc)) ::
      merge_guards(t, g2)
  case (GExp.Eq(v, AExp.Times(vb, vc)) :: t, g2) =>
    GExp.Eq[VName.vname](v, AExp.Times[VName.vname](vb, vc)) ::
      merge_guards(t, g2)
  case (GExp.Gt(v, va) :: t, g2) =>
    GExp.Gt[VName.vname](v, va) :: merge_guards(t, g2)
  case (GExp.Nor(v, va) :: t, g2) =>
    GExp.Nor[VName.vname](v, va) :: merge_guards(t, g2)
}

def is_In[A](x0: GExp.gexp[A]): Boolean = x0 match {
  case GExp.In(uu, uv) => true
  case GExp.Bc(v) => false
  case GExp.Eq(v, va) => false
  case GExp.Gt(v, va) => false
  case GExp.Nor(v, va) => false
}

def gob_aux(t1: Transition.transition_ext[Unit],
             t2: Transition.transition_ext[Unit]):
      Option[Transition.transition_ext[Unit]]
  =
  (if ((Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t1),
           Transition.Outputs[Unit](t2))) && ((Lista.equal_lista[(Nat.nat,
                           AExp.aexp[VName.vname])](Transition.Updates[Unit](t1),
             Transition.Updates[Unit](t2))) && ((all_literal_args[Unit](t1)) && (all_literal_args[Unit](t2)))))
    Some[Transition.transition_ext[Unit]](Transition.transition_exta[Unit](Transition.Label[Unit](t1),
                                    Transition.Arity[Unit](t1),
                                    (Lista.filter[GExp.gexp[VName.vname]](Fun.comp[Boolean,
    Boolean,
    GExp.gexp[VName.vname]](((a: Boolean) => ! a),
                             ((a: GExp.gexp[VName.vname]) =>
                               is_In[VName.vname](a))),
                                   merge_guards(Transition.Guard[Unit](t1),
         Transition.Guard[Unit](t2)))).distinct,
                                    Transition.Outputs[Unit](t1),
                                    Transition.Updates[Unit](t1), ()))
    else None)

def gob(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
         newa: FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))],
         uu: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
         old: FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
         uv: (FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]) =>
               FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             ((Transition.transition_ext[Unit], List[Nat.nat]),
                               (Transition.transition_ext[Unit],
                                 List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t2ID);
    (gob_aux(t1, t2) match {
       case None => None
       case Some(gob_t) =>
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](Inference.replace_transitions(newa,
               List((t1ID, gob_t), (t2ID, gob_t))))
     })
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
                                    (merge_guards(Transition.Guard[Unit](t1),
           Transition.Guard[Unit](t2))).distinct,
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
         uv: (FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]) =>
               FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             ((Transition.transition_ext[Unit], List[Nat.nat]),
                               (Transition.transition_ext[Unit],
                                 List[Nat.nat]))))]):
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
               List((t1ID, lob_t), (t2ID, lob_t))))
     })
  }

def gung_ho_aux(t1: Transition.transition_ext[Unit],
                 t2: Transition.transition_ext[Unit]):
      Option[Transition.transition_ext[Unit]]
  =
  (if ((Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t1),
           Transition.Outputs[Unit](t2))) && ((Lista.equal_lista[(Nat.nat,
                           AExp.aexp[VName.vname])](Transition.Updates[Unit](t1),
             Transition.Updates[Unit](t2))) && ((all_literal_args[Unit](t1)) && (all_literal_args[Unit](t2)))))
    Some[Transition.transition_ext[Unit]](Transition.transition_exta[Unit](Transition.Label[Unit](t1),
                                    Transition.Arity[Unit](t1), Nil,
                                    Transition.Outputs[Unit](t1),
                                    Transition.Updates[Unit](t1), ()))
    else None)

def gung_ho(t1ID: List[Nat.nat], t2ID: List[Nat.nat], s: Nat.nat,
             newa: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
             uu: FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))],
             old: FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
             uv: (FSet.fset[(List[Nat.nat],
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                   FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 ((Transition.transition_ext[Unit],
                                    List[Nat.nat]),
                                   (Transition.transition_ext[Unit],
                                     List[Nat.nat]))))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(newa, t2ID);
    (gung_ho_aux(t1, t2) match {
       case None => None
       case Some(gob_t) =>
         Some[FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](Inference.replace_transitions(newa,
               List((t1ID, gob_t), (t2ID, gob_t))))
     })
  }

} /* object Least_Upper_Bound */

object Use_Small_Numbers {

def is_Num(x0: Value.value): Boolean = x0 match {
  case Value.Numa(uu) => true
  case Value.Str(v) => false
}

def map_of[A : HOL.equal, B](l: List[(A, B)]): A => Option[B] =
  Lista.foldr[(A, B),
               A => Option[B]](((a: (A, B)) =>
                                 {
                                   val (aa, b): (A, B) = a;
                                   ((m: A => Option[B]) =>
                                     Fun.fun_upd[A,
          Option[B]](m, aa, Some[B](b)))
                                 }),
                                l, ((_: A) => None))

def enumerate[A](l: List[A]): List[(A, Int.int)] =
  (l zip (Lista.upto(Int.zero_int,
                      Code_Target_Nat.int_of_nat(Nat.Nata(l.length)))))

def make_small(f: Int.int => Option[Int.int], l: List[Value.value]):
      List[Value.value]
  =
  Lista.map[Value.value,
             Value.value](((x: Value.value) =>
                            (x match {
                               case Value.Numa(n) =>
                                 {
                                   val (Some(a)): Option[Int.int] = f(n);
                                   Value.Numa(a)
                                 }
                               case Value.Str(_) => x
                             })),
                           l)

def trace_enumerate_ints(t: List[(String,
                                   (List[Value.value], List[Value.value]))]):
      List[Int.int]
  =
  Lista.map[Value.value,
             Int.int](((a: Value.value) =>
                        {
                          val (Value.Numa(n)): Value.value = a;
                          n
                        }),
                       Lista.fold[(String,
                                    (List[Value.value], List[Value.value])),
                                   List[Value.value]](Fun.comp[List[Value.value],
                        (List[Value.value]) => List[Value.value],
                        (String,
                          (List[Value.value],
                            List[Value.value]))](Lista.union[Value.value],
          ((a: (String, (List[Value.value], List[Value.value]))) =>
            {
              val (_, (inputs, outputs)):
                    (String, (List[Value.value], List[Value.value]))
                = a;
              Lista.filter[Value.value](((aa: Value.value) => is_Num(aa)),
 inputs ++ outputs)
            })),
               t, Nil))

def log_enumerate_ints(l: List[List[(String,
                                      (List[Value.value],
List[Value.value]))]]):
      List[Int.int]
  =
  Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
              List[Int.int]](Fun.comp[List[Int.int],
                                       (List[Int.int]) => List[Int.int],
                                       List[(String,
      (List[Value.value],
        List[Value.value]))]](Lista.union[Int.int],
                               ((a: List[(String,
   (List[Value.value], List[Value.value]))])
                                  =>
                                 trace_enumerate_ints(a))),
                              l, Nil)

def use_smallest_ints(l: List[List[(String,
                                     (List[Value.value], List[Value.value]))]]):
      List[List[(String, (List[Value.value], List[Value.value]))]]
  =
  {
    val ints: List[Int.int] = log_enumerate_ints(l)
    val f: Int.int => Option[Int.int] =
      map_of[Int.int, Int.int](enumerate[Int.int](ints));
    Lista.map[List[(String, (List[Value.value], List[Value.value]))],
               List[(String,
                      (List[Value.value],
                        List[Value.value]))]](((a:
          List[(String, (List[Value.value], List[Value.value]))])
         =>
        Lista.map[(String, (List[Value.value], List[Value.value])),
                   (String,
                     (List[Value.value],
                       List[Value.value]))](((aa:
        (String, (List[Value.value], List[Value.value])))
       =>
      {
        val (la, (inputs, outputs)):
              (String, (List[Value.value], List[Value.value]))
          = aa;
        (la, (make_small(f, inputs), make_small(f, outputs)))
      }),
     a)),
       l)
  }

} /* object Use_Small_Numbers */

object PTA_Generalisation {

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
                              ts, (b.reverse, tRegs)))._1

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
  target_fold[Nat.nat, Option[Value.value], Nat.nat,
               Map[Nat.nat, Option[Value.value]], List[Value.value],
               List[Nat.nat], Transition.transition_ext[Unit]](tRegs, ts, Nil)

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
                       (if (Cardinality.subset[Nat.nat](Set.seta[Nat.nat](uid),
                 Set.seta[Nat.nat](uids)))
                         (uids, ((from, to), newa))
                         else (uids, ((from, to), t))))
                   })(b)
                }),
               e)

def insert_updates(t: Transition.transition_ext[Unit],
                    u: List[(Nat.nat, AExp.aexp[VName.vname])]):
      Transition.transition_ext[Unit]
  =
  {
    Set.image[VName.vname,
               AExp.aexp[VName.vname]](((a: VName.vname) =>
 AExp.V[VName.vname](a)),
Lista.fold[(Nat.nat, AExp.aexp[VName.vname]),
            Set.set[VName.vname]](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
                                    {
                                      val
(_, ua): (Nat.nat, AExp.aexp[VName.vname]) = a;
                                      ((acc: Set.set[VName.vname]) =>
Set.sup_set[VName.vname](acc, AExp.enumerate_vars(ua)))
                                    }),
                                   u, Set.bot_set[VName.vname]))
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
    Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                      Transition.Arity[Unit](t),
                                      Transition.Guard[Unit](t),
                                      Transition.Outputs[Unit](t),
                                      Lista.filter[(Nat.nat,
             AExp.aexp[VName.vname])](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
{
  val (r, _): (Nat.nat, AExp.aexp[VName.vname]) = a;
  ! ((Lista.map[(Nat.nat, AExp.aexp[VName.vname]),
                 Nat.nat](((aa: (Nat.nat, AExp.aexp[VName.vname])) => aa._1),
                           u)) contains r)
}),
                                       Transition.Updates[Unit](t)) ++
necessary_updates,
                                      ())
  }

def get_updates(u: List[(List[Nat.nat],
                          List[(Nat.nat, AExp.aexp[VName.vname])])],
                 t: List[Nat.nat]):
      List[(Nat.nat, AExp.aexp[VName.vname])]
  =
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
                     (List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname])])
                 = a;
               Cardinality.subset[Nat.nat](Set.seta[Nat.nat](t),
    Set.seta[Nat.nat](tids))
             }),
            u))

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
  case ((l, (i, ux)) :: trace, funs, e, s, r) =>
    {
      val (id, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, l, i))
      val updated: Map[Nat.nat, Option[Value.value]] =
        EFSM.apply_updates(Transition.Updates[Unit](t), AExp.join_ir(i, r), r)
      val newUpdates: List[(Nat.nat, AExp.aexp[VName.vname])] =
        get_updates(funs, id)
      val ta: Transition.transition_ext[Unit] = insert_updates(t, newUpdates)
      val updateda: Map[Nat.nat, Option[Value.value]] =
        EFSM.apply_updates(Transition.Updates[Unit](ta), AExp.join_ir(i, r), r)
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
        = replace_transition(e, id, tb);
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
               Nat.zero_nata, Map().withDefaultValue(None))),
                         log, e)

def everything_walk(uu: AExp.aexp[VName.vname], uv: Nat.nat,
                     uw: Map[VName.vname, String],
                     x3: List[(String, (List[Value.value], List[Value.value]))],
                     ux: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                     uy: Nat.nat, uz: Map[Nat.nat, Option[Value.value]],
                     va: List[List[Nat.nat]]):
      List[(Nat.nat,
             (Map[Nat.nat, Option[Value.value]],
               (Map[Nat.nat, Option[Value.value]],
                 (List[Value.value],
                   (List[Nat.nat], Transition.transition_ext[Unit])))))]
  =
  (uu, uv, uw, x3, ux, uy, uz, va) match {
  case (uu, uv, uw, Nil, ux, uy, uz, va) => Nil
  case (f, fi, types, (label, (inputs, outputs)) :: t, oPTA, s, regs, gp) =>
    {
      val (tid, (sa, ta)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(oPTA,
            s, regs, label, inputs));
      (if (gp contains tid)
        (s, (regs,
              (Dirties.getRegs(types, inputs, f,
                                outputs(Code_Numeral.integer_of_nat(fi).toInt)),
                (inputs, (tid, ta))))) ::
          everything_walk(f, fi, types, t, oPTA, sa,
                           EFSM.apply_updates(Transition.Updates[Unit](ta),
       AExp.join_ir(inputs, regs), regs),
                           gp)
        else {
               val empty: Map[Nat.nat, Option[Value.value]] =
                 Map().withDefaultValue(None);
               (s, (regs, (empty, (inputs, (tid, ta))))) ::
                 everything_walk(f, fi, types, t, oPTA, sa,
                                  EFSM.apply_updates(Transition.Updates[Unit](ta),
              AExp.join_ir(inputs, regs), regs),
                                  gp)
             })
    }
}

def everything_walk_log(f: AExp.aexp[VName.vname], fi: Nat.nat,
                         types: Map[VName.vname, String],
                         log: List[List[(String,
  (List[Value.value], List[Value.value]))]],
                         e: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                         gp: List[List[Nat.nat]]):
      List[List[(Nat.nat,
                  (Map[Nat.nat, Option[Value.value]],
                    (Map[Nat.nat, Option[Value.value]],
                      (List[Value.value],
                        (List[Nat.nat], Transition.transition_ext[Unit])))))]]
  =
  Lista.map[List[(String, (List[Value.value], List[Value.value]))],
             List[(Nat.nat,
                    (Map[Nat.nat, Option[Value.value]],
                      (Map[Nat.nat, Option[Value.value]],
                        (List[Value.value],
                          (List[Nat.nat],
                            Transition.transition_ext[Unit])))))]](((t:
                               List[(String,
                                      (List[Value.value], List[Value.value]))])
                              =>
                             everything_walk(f, fi, types, t, e, Nat.zero_nata,
      Map().withDefaultValue(None), gp)),
                            log)

def get_updates_opt(values: List[Value.value],
                     train:
                       List[(List[Value.value],
                              (Map[Nat.nat, Option[Value.value]],
                                Map[Nat.nat, Option[Value.value]]))]):
      List[(Nat.nat, Option[AExp.aexp[VName.vname]])]
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
                 Option[AExp.aexp[VName.vname]])](((r: Nat.nat) =>
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
          train)).distinct;
              (if (Lista.list_all[(List[Value.value],
                                    (Map[Nat.nat, Option[Value.value]],
                                      Map[Nat.nat, Option[Value.value]]))](((aa:
                                       (List[Value.value],
 (Map[Nat.nat, Option[Value.value]], Map[Nat.nat, Option[Value.value]])))
                                      =>
                                     {
                                       val
 (_, (anteriorRegs, posteriorRegs)):
   (List[Value.value],
     (Map[Nat.nat, Option[Value.value]], Map[Nat.nat, Option[Value.value]]))
 = aa;
                                       Optiona.equal_optiona[Value.value](anteriorRegs(r),
                                   posteriorRegs(r))
                                     }),
                                    train))
                (r, Some[AExp.aexp[VName.vname]](AExp.V[VName.vname](VName.R(r))))
                else (if ((Nat.equal_nata(Nat.Nata(targetValues.length),
   Nat.Nata((1)))) && (Lista.list_all[(List[Value.value],
(Map[Nat.nat, Option[Value.value]],
  Map[Nat.nat, Option[Value.value]]))](((aa:
   (List[Value.value],
     (Map[Nat.nat, Option[Value.value]], Map[Nat.nat, Option[Value.value]])))
  =>
 {
   val (_, (initialRegs, _)):
         (List[Value.value],
           (Map[Nat.nat, Option[Value.value]],
             Map[Nat.nat, Option[Value.value]]))
     = aa;
   (initialRegs.keySet.toList).isEmpty
 }),
train)))
                       {
                         val (Some(v)): Option[Value.value] = targetValues.head;
                         (r, Some[AExp.aexp[VName.vname]](AExp.L[VName.vname](v)))
                       }
                       else (r, Dirties.getUpdate(r, values, train))))
            }),
           a)
  }

def finfun_add[A : HOL.equal : Orderings.linorder,
                B : HOL.equal](a: Map[A, B], b: Map[A, B]):
      Map[A, B]
  =
  Lista.fold[A, Map[A, B]](((k: A) => (f: Map[A, B]) => f + (k -> (b(k)))),
                            b.keySet.toList, a)

def group_update(values: List[Value.value],
                  l: List[(Map[Nat.nat, Option[Value.value]],
                            (Nat.nat,
                              (Map[Nat.nat, Option[Value.value]],
                                (Map[Nat.nat, Option[Value.value]],
                                  (List[Value.value],
                                    (List[Nat.nat],
                                      Transition.transition_ext[Unit]))))))]):
      Option[(List[Nat.nat], List[(Nat.nat, AExp.aexp[VName.vname])])]
  =
  {
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
    val maybe_updates: List[(Nat.nat, Option[AExp.aexp[VName.vname]])] =
      get_updates_opt(values,
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
                                       val
 (tRegs, (_, (oldRegs, (regs, (inputs, (_, _)))))):
   (Map[Nat.nat, Option[Value.value]],
     (Nat.nat,
       (Map[Nat.nat, Option[Value.value]],
         (Map[Nat.nat, Option[Value.value]],
           (List[Value.value],
             (List[Nat.nat], Transition.transition_ext[Unit]))))))
 = a;
                                       (inputs,
 (finfun_add[Nat.nat, Option[Value.value]](oldRegs, regs), tRegs))
                                     }),
                                    targeted));
    (if (Lista.list_ex[(Nat.nat,
                         Option[AExp.aexp[VName.vname]])](((a:
                      (Nat.nat, Option[AExp.aexp[VName.vname]]))
                     =>
                    {
                      val (_, aa): (Nat.nat, Option[AExp.aexp[VName.vname]]) =
                        a;
                      Optiona.is_none[AExp.aexp[VName.vname]](aa)
                    }),
                   maybe_updates))
      None
      else Some[(List[Nat.nat],
                  List[(Nat.nat,
                         AExp.aexp[VName.vname])])]((Lista.fold[(Map[Nat.nat, Option[Value.value]],
                          (Nat.nat,
                            (Map[Nat.nat, Option[Value.value]],
                              (Map[Nat.nat, Option[Value.value]],
                                (List[Value.value],
                                  (List[Nat.nat],
                                    Transition.transition_ext[Unit])))))),
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
                                     (List[Nat.nat],
                                       Transition.transition_ext[Unit])))))))
                         =>
                        {
                          val (_, (_, (_, (_, (_, (tid, _)))))):
                                (Map[Nat.nat, Option[Value.value]],
                                  (Nat.nat,
                                    (Map[Nat.nat, Option[Value.value]],
                                      (Map[Nat.nat, Option[Value.value]],
(List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit]))))))
                            = a;
                          tid
                        })),
 l, Nil),
              Lista.map[(Nat.nat, Option[AExp.aexp[VName.vname]]),
                         (Nat.nat,
                           AExp.aexp[VName.vname])](((a:
                (Nat.nat, Option[AExp.aexp[VName.vname]]))
               =>
              {
                val (r, f_o): (Nat.nat, Option[AExp.aexp[VName.vname]]) = a;
                (r, Optiona.the[AExp.aexp[VName.vname]](f_o))
              }),
             maybe_updates))))
  }

def groupwise_put_updates(x0: List[List[(List[Nat.nat],
  Transition.transition_ext[Unit])]],
                           uu: List[List[(String,
   (List[Value.value], List[Value.value]))]],
                           uv: List[Value.value], uw: List[List[Nat.nat]],
                           ux: (Nat.nat,
                                 (AExp.aexp[VName.vname],
                                   Map[VName.vname, String])),
                           e: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (x0, uu, uv, uw, ux, e) match {
  case (Nil, uu, uv, uw, ux, e) => e
  case (gp :: gps, log, values, current, (o_inx, (op, types)), e) =>
    {
      val walked:
            List[List[(Nat.nat,
                        (Map[Nat.nat, Option[Value.value]],
                          (Map[Nat.nat, Option[Value.value]],
                            (List[Value.value],
                              (List[Nat.nat],
                                Transition.transition_ext[Unit])))))]]
        = everything_walk_log(op, o_inx, types, log, e, current)
      val targeted:
            List[List[(Map[Nat.nat, Option[Value.value]],
                        (Nat.nat,
                          (Map[Nat.nat, Option[Value.value]],
                            (Map[Nat.nat, Option[Value.value]],
                              (List[Value.value],
                                (List[Nat.nat],
                                  Transition.transition_ext[Unit]))))))]]
        = Lista.map[List[(Map[Nat.nat, Option[Value.value]],
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
                                      Transition.transition_ext[Unit]))))))]](((a:
  List[(Map[Nat.nat, Option[Value.value]],
         (Nat.nat,
           (Map[Nat.nat, Option[Value.value]],
             (Map[Nat.nat, Option[Value.value]],
               (List[Value.value],
                 (List[Nat.nat], Transition.transition_ext[Unit]))))))])
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
                            val (_, (_, (_, (_, (_, (id, tran)))))):
                                  (Map[Nat.nat, Option[Value.value]],
                                    (Nat.nat,
                                      (Map[Nat.nat, Option[Value.value]],
(Map[Nat.nat, Option[Value.value]],
  (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit]))))))
                              = aa;
                            gp contains (id, tran)
                          }),
                         a)),
                                       Lista.map[List[(Nat.nat,
                (Map[Nat.nat, Option[Value.value]],
                  (Map[Nat.nat, Option[Value.value]],
                    (List[Value.value],
                      (List[Nat.nat], Transition.transition_ext[Unit])))))],
          List[(Map[Nat.nat, Option[Value.value]],
                 (Nat.nat,
                   (Map[Nat.nat, Option[Value.value]],
                     (Map[Nat.nat, Option[Value.value]],
                       (List[Value.value],
                         (List[Nat.nat],
                           Transition.transition_ext[Unit]))))))]](((w:
                               List[(Nat.nat,
                                      (Map[Nat.nat, Option[Value.value]],
(Map[Nat.nat, Option[Value.value]],
  (List[Value.value], (List[Nat.nat], Transition.transition_ext[Unit])))))])
                              =>
                             (target(Map().withDefaultValue(None),
                                      w.reverse)).reverse),
                            walked))
      val group:
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
                                       Transition.transition_ext[Unit]))))))]](Lista.union[(Map[Nat.nat, Option[Value.value]],
             (Nat.nat,
               (Map[Nat.nat, Option[Value.value]],
                 (Map[Nat.nat, Option[Value.value]],
                   (List[Value.value],
                     (List[Nat.nat], Transition.transition_ext[Unit]))))))],
targeted, Nil);
      (group_update(values, group) match {
         case None =>
           groupwise_put_updates(gps, log, values, current,
                                  (o_inx, (op, types)), e)
         case Some(u) =>
           groupwise_put_updates(gps, log, values, current,
                                  (o_inx, (op, types)),
                                  Inference.make_distinct(add_groupwise_updates(log,
 List(u), e)))
       })
    }
}

def same_structure_opt(x0: Option[Transition.transition_ext[Unit]],
                        x1: Option[Transition.transition_ext[Unit]]):
      Boolean
  =
  (x0, x1) match {
  case (None, None) => true
  case (Some(ta), Some(t)) => Transition.same_structure(ta, t)
  case (Some(v), None) => false
  case (None, Some(v)) => false
}

def assign_group(x0: List[(Option[Transition.transition_ext[Unit]],
                            (Nat.nat,
                              List[(List[Nat.nat],
                                     Transition.transition_ext[Unit])]))],
                  count: Option[Transition.transition_ext[Unit]] => Nat.nat,
                  prev: Option[Transition.transition_ext[Unit]],
                  x3: (List[Nat.nat], Transition.transition_ext[Unit])):
      List[(Option[Transition.transition_ext[Unit]],
             (Nat.nat, List[(List[Nat.nat], Transition.transition_ext[Unit])]))]
  =
  (x0, count, prev, x3) match {
  case (Nil, count, prev, (tid, t)) =>
    List((prev, (count(prev), List((tid, t)))))
  case ((preva, (c, gp)) :: t, count, prev, (tid, tr)) =>
    (if ((same_structure_opt(prev,
                              preva)) && ((Lista.list_all[(List[Nat.nat],
                    Transition.transition_ext[Unit])](((a:
                  (List[Nat.nat], Transition.transition_ext[Unit]))
                 =>
                {
                  val (_, aa): (List[Nat.nat], Transition.transition_ext[Unit])
                    = a;
                  Transition.same_structure(tr, aa)
                }),
               gp)) && (Nat.equal_nata(count(prev), c))))
      (preva,
        (c, Lista.insert[(List[Nat.nat],
                           Transition.transition_ext[Unit])]((tid, tr), gp))) ::
        t
      else (preva, (c, gp)) :: assign_group(t, count, prev, (tid, tr)))
}

def trace_group_transitions(uu: Option[Transition.transition_ext[Unit]] =>
                                  Nat.nat,
                             uv: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                             x2: List[(String,
(List[Value.value], List[Value.value]))],
                             uw: Nat.nat, ux: Map[Nat.nat, Option[Value.value]],
                             uy: Option[Transition.transition_ext[Unit]],
                             uz: Option[Transition.transition_ext[Unit]],
                             g: List[(Option[Transition.transition_ext[Unit]],
                                       (Nat.nat,
 List[(List[Nat.nat], Transition.transition_ext[Unit])]))]):
      List[(Option[Transition.transition_ext[Unit]],
             (Nat.nat, List[(List[Nat.nat], Transition.transition_ext[Unit])]))]
  =
  (uu, uv, x2, uw, ux, uy, uz, g) match {
  case (uu, uv, Nil, uw, ux, uy, uz, g) => g
  case (count, e, (l, (i, va)) :: trace, s, r, prevGroup, currentGroup, g) =>
    {
      val (id, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, l, i))
      val ra: Map[Nat.nat, Option[Value.value]] =
        EFSM.apply_updates(Transition.Updates[Unit](t), AExp.join_ir(i, r), r)
      val newCount: Option[Transition.transition_ext[Unit]] => Nat.nat =
        ((x: Option[Transition.transition_ext[Unit]]) =>
          (if (Optiona.equal_optiona[Transition.transition_ext[Unit]](x,
                               Some[Transition.transition_ext[Unit]](t)))
            Nat.Suc(count(x)) else count(x)));
      (if (same_structure_opt(Some[Transition.transition_ext[Unit]](t),
                               currentGroup))
        trace_group_transitions(newCount, e, trace, sa, ra, prevGroup,
                                 currentGroup,
                                 assign_group(g, count, prevGroup, (id, t)))
        else trace_group_transitions(newCount, e, trace, sa, ra, currentGroup,
                                      Some[Transition.transition_ext[Unit]](t),
                                      assign_group(g, count, currentGroup,
            (id, t))))
    }
}

def log_group_transitions(e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                           l: List[List[(String,
  (List[Value.value], List[Value.value]))]]):
      List[(Option[Transition.transition_ext[Unit]],
             (Nat.nat, List[(List[Nat.nat], Transition.transition_ext[Unit])]))]
  =
  Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
              List[(Option[Transition.transition_ext[Unit]],
                     (Nat.nat,
                       List[(List[Nat.nat],
                              Transition.transition_ext[Unit])]))]](((t:
                                List[(String,
                                       (List[Value.value], List[Value.value]))])
                               =>
                              ((a: List[(Option[Transition.transition_ext[Unit]],
  (Nat.nat, List[(List[Nat.nat], Transition.transition_ext[Unit])]))])
                                 =>
                                trace_group_transitions(((_:
                    Option[Transition.transition_ext[Unit]])
                   =>
                  Nat.zero_nata),
                 e, t, Nat.zero_nata, Map().withDefaultValue(None), None, None,
                 a))),
                             l, Nil)

def transition_groups(e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       l: List[List[(String,
                                      (List[Value.value],
List[Value.value]))]]):
      List[List[(List[Nat.nat], Transition.transition_ext[Unit])]]
  =
  {
    val a: List[(Option[Transition.transition_ext[Unit]],
                  (Nat.nat,
                    List[(List[Nat.nat], Transition.transition_ext[Unit])]))]
      = log_group_transitions(e, l);
    Lista.map[(Option[Transition.transition_ext[Unit]],
                (Nat.nat,
                  List[(List[Nat.nat], Transition.transition_ext[Unit])])),
               List[(List[Nat.nat],
                      Transition.transition_ext[Unit])]](Fun.comp[(Nat.nat,
                            List[(List[Nat.nat],
                                   Transition.transition_ext[Unit])]),
                           List[(List[Nat.nat],
                                  Transition.transition_ext[Unit])],
                           (Option[Transition.transition_ext[Unit]],
                             (Nat.nat,
                               List[(List[Nat.nat],
                                      Transition.transition_ext[Unit])]))](((aa:
                                       (Nat.nat,
 List[(List[Nat.nat], Transition.transition_ext[Unit])]))
                                      =>
                                     aa._2),
                                    ((aa:
(Option[Transition.transition_ext[Unit]],
  (Nat.nat, List[(List[Nat.nat], Transition.transition_ext[Unit])])))
                                       =>
                                      aa._2)),
                  a)
  }

def put_updates_fold(log: List[List[(String,
                                      (List[Value.value], List[Value.value]))]],
                      values: List[Value.value], current: List[List[Nat.nat]]):
      (List[(Nat.nat,
              Option[(AExp.aexp[VName.vname], Map[VName.vname, String])])]) =>
        Option[FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]] =>
          Option[FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]]
  =
  ((a: List[(Nat.nat,
              Option[(AExp.aexp[VName.vname], Map[VName.vname, String])])])
     =>
    (b: Option[FSet.fset[(List[Nat.nat],
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]])
      =>
    Lista.fold[(Nat.nat,
                 Option[(AExp.aexp[VName.vname], Map[VName.vname, String])]),
                Option[FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]]](((aa:
                                      (Nat.nat,
Option[(AExp.aexp[VName.vname], Map[VName.vname, String])]))
                                     =>
                                    {
                                      val
(o_inx, t):
  (Nat.nat, Option[(AExp.aexp[VName.vname], Map[VName.vname, String])])
= aa;
                                      ((ab:
  Option[FSet.fset[(List[Nat.nat],
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]])
 =>
(ab match {
   case None => None
   case Some(e) =>
     (t match {
        case None => None
        case Some((op, types)) =>
          {
            val groups:
                  List[List[(List[Nat.nat], Transition.transition_ext[Unit])]]
              = transition_groups(e, log)
            val ac: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]
              = groupwise_put_updates(groups, log, values, current,
                                       (o_inx, (op, types)), e);
            Some[FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]](ac)
          }
      })
 }))
                                    }),
                                   a, b))

def put_updates(log: List[List[(String,
                                 (List[Value.value], List[Value.value]))]],
                 values: List[Value.value], current: List[List[Nat.nat]],
                 xs: List[(Nat.nat,
                            Option[(AExp.aexp[VName.vname],
                                     Map[VName.vname, String])])],
                 e: FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (put_updates_fold(log, values,
                     current)).apply(xs).apply(Some[FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))]](e))

def put_outputs(xs: List[(Option[(AExp.aexp[VName.vname],
                                   Map[VName.vname, String])],
                           AExp.aexp[VName.vname])]):
      List[AExp.aexp[VName.vname]]
  =
  Lista.foldr[(Option[(AExp.aexp[VName.vname], Map[VName.vname, String])],
                AExp.aexp[VName.vname]),
               List[AExp.aexp[VName.vname]]](((x:
         (Option[(AExp.aexp[VName.vname], Map[VName.vname, String])],
           AExp.aexp[VName.vname]))
        =>
       (acc: List[AExp.aexp[VName.vname]]) =>
       {
         val (a, p):
               (Option[(AExp.aexp[VName.vname], Map[VName.vname, String])],
                 AExp.aexp[VName.vname])
           = x;
         (a match {
            case None => p :: acc
            case Some((pa, _)) => pa :: acc
          })
       }),
      xs, Nil)

def get_outputs(maxReg: Nat.nat, values: List[Value.value],
                 i: List[List[Value.value]],
                 r: List[Map[Nat.nat, Option[Value.value]]],
                 outputs: List[List[Value.value]]):
      List[Option[(AExp.aexp[VName.vname], Map[VName.vname, String])]]
  =
  Lista.map[List[Value.value],
             Option[(AExp.aexp[VName.vname],
                      Map[VName.vname, String])]](((a: List[Value.value]) =>
            Dirties.getOutput(maxReg, values, i, r, a)),
           Lista.transpose[Value.value](outputs))

def generalise_and_update(log: List[List[(String,
   (List[Value.value], List[Value.value]))]],
                           e: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                           gp: (List[(List[Nat.nat],
                                       Transition.transition_ext[Unit])],
                                 List[(Map[Nat.nat, Option[Value.value]],
(List[Value.value], List[Value.value]))])):
      Option[FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val values: List[Value.value] = Inference.enumerate_log_values(log)
    val i: List[List[Value.value]] =
      Lista.map[(Map[Nat.nat, Option[Value.value]],
                  (List[Value.value], List[Value.value])),
                 List[Value.value]](((a:
(Map[Nat.nat, Option[Value.value]], (List[Value.value], List[Value.value])))
                                       =>
                                      {
val (_, (ins, _)):
      (Map[Nat.nat, Option[Value.value]],
        (List[Value.value], List[Value.value]))
  = a;
ins
                                      }),
                                     gp._2)
    val r: List[Map[Nat.nat, Option[Value.value]]] =
      Lista.map[(Map[Nat.nat, Option[Value.value]],
                  (List[Value.value], List[Value.value])),
                 Map[Nat.nat, Option[Value.value]]](((a:
                (Map[Nat.nat, Option[Value.value]],
                  (List[Value.value], List[Value.value])))
               =>
              {
                val (regs, (_, _)):
                      (Map[Nat.nat, Option[Value.value]],
                        (List[Value.value], List[Value.value]))
                  = a;
                regs
              }),
             gp._2)
    val p: List[List[Value.value]] =
      Lista.map[(Map[Nat.nat, Option[Value.value]],
                  (List[Value.value], List[Value.value])),
                 List[Value.value]](((a:
(Map[Nat.nat, Option[Value.value]], (List[Value.value], List[Value.value])))
                                       =>
                                      {
val (_, (_, outs)):
      (Map[Nat.nat, Option[Value.value]],
        (List[Value.value], List[Value.value]))
  = a;
outs
                                      }),
                                     gp._2)
    val max_reg: Nat.nat = Inference.max_reg_total(e)
    val outputs:
          List[Option[(AExp.aexp[VName.vname], Map[VName.vname, String])]]
      = get_outputs(max_reg, values, i, r, p)
    val changes: List[(List[Nat.nat], Transition.transition_ext[Unit])] =
      Lista.map[(List[Nat.nat], Transition.transition_ext[Unit]),
                 (List[Nat.nat],
                   Transition.transition_ext[Unit])](((a:
                 (List[Nat.nat], Transition.transition_ext[Unit]))
                =>
               {
                 val (id, tran):
                       (List[Nat.nat], Transition.transition_ext[Unit])
                   = a;
                 (id, Transition.Outputs_update[Unit](((_:
                  List[AExp.aexp[VName.vname]])
                 =>
                put_outputs((outputs zip (Transition.Outputs[Unit](tran))))),
               tran))
               }),
              gp._1)
    val generalised_model:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = Lista.fold[(List[Nat.nat], Transition.transition_ext[Unit]),
                    FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]](((a:
                                  (List[Nat.nat],
                                    Transition.transition_ext[Unit]))
                                 =>
                                {
                                  val (id, t):
(List[Nat.nat], Transition.transition_ext[Unit])
                                    = a;
                                  ((acc: FSet.fset[(List[Nat.nat],
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                                     =>
                                    replace_transition(acc, id, t))
                                }),
                               changes, e);
    (put_updates(log, values,
                  Lista.map[(List[Nat.nat], Transition.transition_ext[Unit]),
                             List[Nat.nat]](((a:
        (List[Nat.nat], Transition.transition_ext[Unit]))
       =>
      a._1),
     gp._1),
                  Lista.enumerate[Option[(AExp.aexp[VName.vname],
   Map[VName.vname, String])]](Nat.zero_nata, outputs),
                  generalised_model)
       match {
       case None => None
       case Some(ea) =>
         (if (Inference.satisfies(Set.seta[List[(String,
          (List[Value.value], List[Value.value]))]](log),
                                   Inference.tm(ea)))
           Some[FSet.fset[(List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](ea)
           else None)
     })
  }

def groupwise_generalise_and_update(log: List[List[(String,
             (List[Value.value], List[Value.value]))]],
                                     e: FSet.fset[(List[Nat.nat],
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                     gs: List[(List[(List[Nat.nat],
              Transition.transition_ext[Unit])],
        List[(Map[Nat.nat, Option[Value.value]],
               (List[Value.value], List[Value.value]))])]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
               List[(Map[Nat.nat, Option[Value.value]],
                      (List[Value.value], List[Value.value]))]),
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((gp:
                            (List[(List[Nat.nat],
                                    Transition.transition_ext[Unit])],
                              List[(Map[Nat.nat, Option[Value.value]],
                                     (List[Value.value], List[Value.value]))]))
                           =>
                          (ea: FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                            =>
                          (generalise_and_update(log, ea, gp) match {
                             case None => ea
                             case Some(eb) => eb
                           })),
                         gs, e)

def standardise_group_updates(g: List[(List[Nat.nat],
Transition.transition_ext[Unit])]):
      List[(List[Nat.nat], Transition.transition_ext[Unit])]
  =
  {
    val updates: List[(Nat.nat, AExp.aexp[VName.vname])] =
      (Lista.maps[(List[Nat.nat], Transition.transition_ext[Unit]),
                   (Nat.nat,
                     AExp.aexp[VName.vname])](Fun.comp[Transition.transition_ext[Unit],
                List[(Nat.nat, AExp.aexp[VName.vname])],
                (List[Nat.nat],
                  Transition.transition_ext[Unit])](((a:
                Transition.transition_ext[Unit])
               =>
              Transition.Updates[Unit](a)),
             ((a: (List[Nat.nat], Transition.transition_ext[Unit])) => a._2)),
       g)).distinct;
    Lista.map[(List[Nat.nat], Transition.transition_ext[Unit]),
               (List[Nat.nat],
                 Transition.transition_ext[Unit])](((a:
               (List[Nat.nat], Transition.transition_ext[Unit]))
              =>
             {
               val (id, t): (List[Nat.nat], Transition.transition_ext[Unit]) =
                 a;
               (id, Transition.Updates_update[Unit](((_:
                List[(Nat.nat, AExp.aexp[VName.vname])])
               =>
              updates),
             t))
             }),
            g)
  }

def standardise_outputs(p1: List[AExp.aexp[VName.vname]],
                         p2: List[AExp.aexp[VName.vname]]):
      List[AExp.aexp[VName.vname]]
  =
  Lista.map[(AExp.aexp[VName.vname], AExp.aexp[VName.vname]),
             AExp.aexp[VName.vname]](((a:
 (AExp.aexp[VName.vname], AExp.aexp[VName.vname]))
=>
                                       {
 val (aa, b): (AExp.aexp[VName.vname], AExp.aexp[VName.vname]) = a;
 Orderings.max[AExp.aexp[VName.vname]](aa, b)
                                       }),
                                      (p1 zip p2))

def standardise_group_outputs(g: List[(List[Nat.nat],
Transition.transition_ext[Unit])]):
      List[(List[Nat.nat], Transition.transition_ext[Unit])]
  =
  {
    val outputs: List[AExp.aexp[VName.vname]] =
      (g match {
         case Nil => Nil
         case h :: t =>
           Lista.fold[(List[Nat.nat], Transition.transition_ext[Unit]),
                       List[AExp.aexp[VName.vname]]](Fun.comp[List[AExp.aexp[VName.vname]],
                       (List[AExp.aexp[VName.vname]]) =>
                         List[AExp.aexp[VName.vname]],
                       (List[Nat.nat],
                         Transition.transition_ext[Unit])](((a:
                       List[AExp.aexp[VName.vname]])
                      =>
                     (b: List[AExp.aexp[VName.vname]]) =>
                     standardise_outputs(a, b)),
                    Fun.comp[Transition.transition_ext[Unit],
                              List[AExp.aexp[VName.vname]],
                              (List[Nat.nat],
                                Transition.transition_ext[Unit])](((a:
                              Transition.transition_ext[Unit])
                             =>
                            Transition.Outputs[Unit](a)),
                           ((a: (List[Nat.nat],
                                  Transition.transition_ext[Unit]))
                              =>
                             a._2))),
              t, Transition.Outputs[Unit](h._2))
       });
    Lista.map[(List[Nat.nat], Transition.transition_ext[Unit]),
               (List[Nat.nat],
                 Transition.transition_ext[Unit])](((a:
               (List[Nat.nat], Transition.transition_ext[Unit]))
              =>
             {
               val (id, t): (List[Nat.nat], Transition.transition_ext[Unit]) =
                 a;
               (id, Transition.Outputs_update[Unit](((_:
                List[AExp.aexp[VName.vname]])
               =>
              outputs),
             t))
             }),
            g)
  }

def standardise_groups_aux(e: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            l: List[List[(String,
   (List[Value.value], List[Value.value]))]],
                            xs: List[List[(List[Nat.nat],
    Transition.transition_ext[Unit])]],
                            s: (List[(List[Nat.nat],
                                       Transition.transition_ext[Unit])]) =>
                                 List[(List[Nat.nat],
Transition.transition_ext[Unit])]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[List[(List[Nat.nat], Transition.transition_ext[Unit])],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((h:
                            List[(List[Nat.nat],
                                   Transition.transition_ext[Unit])])
                           =>
                          (acc: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                            =>
                          {
                            val ea: FSet.fset[(List[Nat.nat],
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
                              = Inference.replace_transitions(acc, s(h));
                            (if (Inference.satisfies(Set.seta[List[(String,
                             (List[Value.value], List[Value.value]))]](l),
              Inference.tm(ea)))
                              ea else acc)
                          }),
                         xs, e)

def insert_into_group(x0: List[List[(List[Nat.nat],
                                      Transition.transition_ext[Unit])]],
                       pair: (List[Nat.nat], Transition.transition_ext[Unit])):
      List[List[(List[Nat.nat], Transition.transition_ext[Unit])]]
  =
  (x0, pair) match {
  case (Nil, pair) => List(List(pair))
  case (h :: t, pair) =>
    (if (Lista.list_all[(List[Nat.nat],
                          Transition.transition_ext[Unit])](((a:
                        (List[Nat.nat], Transition.transition_ext[Unit]))
                       =>
                      {
                        val (_, aa):
                              (List[Nat.nat], Transition.transition_ext[Unit])
                          = a;
                        Transition.same_structure(pair._2, aa)
                      }),
                     h))
      Lista.insert[(List[Nat.nat], Transition.transition_ext[Unit])](pair, h) ::
        t
      else h :: insert_into_group(t, pair))
}

def group_by_structure(e: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]):
      List[List[(List[Nat.nat], Transition.transition_ext[Unit])]]
  =
  Lista.fold[(List[Nat.nat],
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
              List[List[(List[Nat.nat],
                          Transition.transition_ext[Unit])]]](((a:
                          (List[Nat.nat],
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])))
                         =>
                        {
                          val (tid, (_, transition)):
                                (List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))
                            = a;
                          ((acc: List[List[(List[Nat.nat],
     Transition.transition_ext[Unit])]])
                             =>
                            insert_into_group(acc, (tid, transition)))
                        }),
                       FSet.sorted_list_of_fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](e),
                       Nil)

def standardise_groups(e: FSet.fset[(List[Nat.nat],
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                        l: List[List[(String,
                                       (List[Value.value],
 List[Value.value]))]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  standardise_groups_aux(e, l, group_by_structure(e),
                          Fun.comp[List[(List[Nat.nat],
  Transition.transition_ext[Unit])],
                                    List[(List[Nat.nat],
   Transition.transition_ext[Unit])],
                                    List[(List[Nat.nat],
   Transition.transition_ext[Unit])]](((a:
  List[(List[Nat.nat], Transition.transition_ext[Unit])])
 =>
standardise_group_outputs(a)),
                                       ((a:
   List[(List[Nat.nat], Transition.transition_ext[Unit])])
  =>
 standardise_group_updates(a))))

def assign_training_set(data: List[(List[(List[Nat.nat],
   Transition.transition_ext[Unit])],
                                     List[(Map[Nat.nat, Option[Value.value]],
    (List[Value.value], List[Value.value]))])],
                         tids: List[Nat.nat], label: String,
                         inputs: List[Value.value],
                         registers: Map[Nat.nat, Option[Value.value]],
                         outputs: List[Value.value]):
      List[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
             List[(Map[Nat.nat, Option[Value.value]],
                    (List[Value.value], List[Value.value]))])]
  =
  Lista.map[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
              List[(Map[Nat.nat, Option[Value.value]],
                     (List[Value.value], List[Value.value]))]),
             (List[(List[Nat.nat], Transition.transition_ext[Unit])],
               List[(Map[Nat.nat, Option[Value.value]],
                      (List[Value.value],
                        List[Value.value]))])](((gp:
           (List[(List[Nat.nat], Transition.transition_ext[Unit])],
             List[(Map[Nat.nat, Option[Value.value]],
                    (List[Value.value], List[Value.value]))]))
          =>
         {
           val (transitions, trainingSet):
                 (List[(List[Nat.nat], Transition.transition_ext[Unit])],
                   List[(Map[Nat.nat, Option[Value.value]],
                          (List[Value.value], List[Value.value]))])
             = gp;
           (if (Lista.list_ex[(List[Nat.nat],
                                Transition.transition_ext[Unit])](((a:
                              (List[Nat.nat], Transition.transition_ext[Unit]))
                             =>
                            {
                              val (tidsa, _):
                                    (List[Nat.nat],
                                      Transition.transition_ext[Unit])
                                = a;
                              Lista.equal_lista[Nat.nat](tidsa, tids)
                            }),
                           transitions))
             (transitions, (registers, (inputs, outputs)) :: trainingSet)
             else gp)
         }),
        data)

def trace_training_set(uu: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))],
                        x1: List[(String,
                                   (List[Value.value], List[Value.value]))],
                        uv: Nat.nat, uw: Map[Nat.nat, Option[Value.value]],
                        ts: List[(List[(List[Nat.nat],
 Transition.transition_ext[Unit])],
                                   List[(Map[Nat.nat, Option[Value.value]],
  (List[Value.value], List[Value.value]))])]):
      List[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
             List[(Map[Nat.nat, Option[Value.value]],
                    (List[Value.value], List[Value.value]))])]
  =
  (uu, x1, uv, uw, ts) match {
  case (uu, Nil, uv, uw, ts) => ts
  case (e, (label, (inputs, outputs)) :: t, s, r, ts) =>
    {
      val (id, (sa, transition)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, label, inputs));
      trace_training_set(e, t, sa,
                          EFSM.apply_updates(Transition.Updates[Unit](transition),
      AExp.join_ir(inputs, r), r),
                          assign_training_set(ts, id, label, inputs, r,
       outputs))
    }
}

def log_training_set(e: FSet.fset[(List[Nat.nat],
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      l: List[List[(String,
                                     (List[Value.value], List[Value.value]))]],
                      ts: List[(List[(List[Nat.nat],
                                       Transition.transition_ext[Unit])],
                                 List[(Map[Nat.nat, Option[Value.value]],
(List[Value.value], List[Value.value]))])]):
      List[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
             List[(Map[Nat.nat, Option[Value.value]],
                    (List[Value.value], List[Value.value]))])]
  =
  Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
              List[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
                     List[(Map[Nat.nat, Option[Value.value]],
                            (List[Value.value],
                              List[Value.value]))])]](((h:
                  List[(String, (List[Value.value], List[Value.value]))])
                 =>
                ((a: List[(List[(List[Nat.nat],
                                  Transition.transition_ext[Unit])],
                            List[(Map[Nat.nat, Option[Value.value]],
                                   (List[Value.value], List[Value.value]))])])
                   =>
                  trace_training_set(e, h, Nat.zero_nata,
                                      Map().withDefaultValue(None), a))),
               l, ts)

def make_training_set(e: FSet.fset[(List[Nat.nat],
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       l: List[List[(String,
                                      (List[Value.value],
List[Value.value]))]]):
      List[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
             List[(Map[Nat.nat, Option[Value.value]],
                    (List[Value.value], List[Value.value]))])]
  =
  log_training_set(e, l,
                    Lista.map[List[(List[Nat.nat],
                                     Transition.transition_ext[Unit])],
                               (List[(List[Nat.nat],
                                       Transition.transition_ext[Unit])],
                                 List[(Map[Nat.nat, Option[Value.value]],
(List[Value.value],
  List[Value.value]))])](((x: List[(List[Nat.nat],
                                     Transition.transition_ext[Unit])])
                            =>
                           (x, Nil)),
                          transition_groups(e, l)))

def incremental_normalised_pta(log: List[List[(String,
        (List[Value.value], List[Value.value]))]],
                                pta: FSet.fset[(List[Nat.nat],
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  {
    Inference.enumerate_log_values(log)
    val training_set:
          List[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
                 List[(Map[Nat.nat, Option[Value.value]],
                        (List[Value.value], List[Value.value]))])]
      = make_training_set(pta, log);
    standardise_groups(groupwise_generalise_and_update(log, pta, training_set),
                        log)
  }

def find_initialisation_of_trace(uu: Nat.nat,
                                  x1: List[(String,
     (List[Value.value], List[Value.value]))],
                                  uv: FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                  uw: Nat.nat,
                                  ux: Map[Nat.nat, Option[Value.value]]):
      Option[(List[Nat.nat], Transition.transition_ext[Unit])]
  =
  (uu, x1, uv, uw, ux) match {
  case (uu, Nil, uv, uw, ux) => None
  case (ra, (l, (i, uy)) :: es, e, s, r) =>
    {
      val (tids, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, l, i));
      (if (Lista.list_ex[(Nat.nat,
                           AExp.aexp[VName.vname])](((a:
                (Nat.nat, AExp.aexp[VName.vname]))
               =>
              {
                val (rr, u): (Nat.nat, AExp.aexp[VName.vname]) = a;
                (Nat.equal_nata(rr, ra)) && (AExp.is_lit[VName.vname](u))
              }),
             Transition.Updates[Unit](t)))
        Some[(List[Nat.nat], Transition.transition_ext[Unit])]((tids, t))
        else find_initialisation_of_trace(ra, es, e, sa,
   EFSM.apply_updates(Transition.Updates[Unit](t), AExp.join_ir(i, r), r)))
    }
}

def find_initialisation_of(uu: Nat.nat,
                            uv: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            x2: List[List[(String,
    (List[Value.value], List[Value.value]))]]):
      List[Option[(List[Nat.nat], Transition.transition_ext[Unit])]]
  =
  (uu, uv, x2) match {
  case (uu, uv, Nil) => Nil
  case (r, e, h :: t) =>
    (find_initialisation_of_trace(r, h, e, Nat.zero_nata,
                                   Map().withDefaultValue(None))
       match {
       case None => find_initialisation_of(r, e, t)
       case Some(thing) =>
         Some[(List[Nat.nat], Transition.transition_ext[Unit])](thing) ::
           find_initialisation_of(r, e, t)
     })
}

def delay_initialisation_of(r: Nat.nat,
                             l: List[List[(String,
    (List[Value.value], List[Value.value]))]],
                             e: FSet.fset[(List[Nat.nat],
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                             tids: List[List[Nat.nat]]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[Option[(List[Nat.nat], Transition.transition_ext[Unit])],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((x:
                            Option[(List[Nat.nat],
                                     Transition.transition_ext[Unit])])
                           =>
                          (ea: FSet.fset[(List[Nat.nat],
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                            =>
                          (x match {
                             case None => ea
                             case Some((i_tids, t)) =>
                               {
                                 val origins: List[Nat.nat] =
                                   Lista.map[List[Nat.nat],
      Nat.nat](((id: List[Nat.nat]) => Inference.origin(id, ea)), tids)
                                 val init_val: AExp.aexp[VName.vname] =
                                   ((Lista.filter[(Nat.nat,
            AExp.aexp[VName.vname])](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
                                       {
 val (ra, _): (Nat.nat, AExp.aexp[VName.vname]) = a;
 Nat.equal_nata(r, ra)
                                       }),
                                      Transition.Updates[Unit](t))).head)._2;
                                 FSet.fimage[(List[Nat.nat],
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
      (List[Nat.nat],
        ((Nat.nat, Nat.nat),
          Transition.transition_ext[Unit]))](((a:
         (List[Nat.nat], ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
        =>
       {
         val (id, aa):
               (List[Nat.nat],
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
           = a
         val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) =
           aa;
         ({
            val (origin, dest): (Nat.nat, Nat.nat) = ab;
            ((tr: Transition.transition_ext[Unit]) =>
              (if (origins contains dest)
                (id, ((origin, dest),
                       Transition.Updates_update[Unit](((_:
                   List[(Nat.nat, AExp.aexp[VName.vname])])
                  =>
                 Lista.insert[(Nat.nat,
                                AExp.aexp[VName.vname])]((r, init_val),
                  Transition.Updates[Unit](tr))),
                tr)))
                else (if (Lista.equal_lista[Nat.nat](id, i_tids))
                       (id, ((origin, dest),
                              Transition.Updates_update[Unit](((_:
                          List[(Nat.nat, AExp.aexp[VName.vname])])
                         =>
                        Lista.filter[(Nat.nat,
                                       AExp.aexp[VName.vname])](((ac:
                            (Nat.nat, AExp.aexp[VName.vname]))
                           =>
                          {
                            val (ra, _): (Nat.nat, AExp.aexp[VName.vname]) = ac;
                            ! (Nat.equal_nata(r, ra))
                          }),
                         Transition.Updates[Unit](tr))),
                       tr)))
                       else (id, ((origin, dest), tr)))))
          })(b)
       }),
      ea)
                               }
                           })),
                         find_initialisation_of(r, e, l), e)

def derestrict_transition(t: Transition.transition_ext[Unit]):
      Transition.transition_ext[Unit]
  =
  {
    val relevant_vars: Set.set[AExp.aexp[VName.vname]] =
      Set.image[VName.vname,
                 AExp.aexp[VName.vname]](((a: VName.vname) =>
   AExp.V[VName.vname](a)),
  Lista.fold[(Nat.nat, AExp.aexp[VName.vname]),
              Set.set[VName.vname]](((a: (Nat.nat, AExp.aexp[VName.vname])) =>
                                      {
val (_, u): (Nat.nat, AExp.aexp[VName.vname]) = a;
((acc: Set.set[VName.vname]) =>
  Set.sup_set[VName.vname](acc, AExp.enumerate_vars(u)))
                                      }),
                                     Transition.Updates[Unit](t),
                                     Set.bot_set[VName.vname]));
    Transition.Guard_update[Unit](((_: List[GExp.gexp[VName.vname]]) =>
                                    Lista.filter[GExp.gexp[VName.vname]](((g:
                                     GExp.gexp[VName.vname])
                                    =>
                                   Set.Ball[AExp.aexp[VName.vname]](relevant_vars,
                             ((v: AExp.aexp[VName.vname]) =>
                               ! (GExp.gexp_constrains[VName.vname](g, v))))),
                                  Transition.Guard[Unit](t))),
                                   t)
  }

def find_first_use_of_trace(uu: Nat.nat,
                             x1: List[(String,
(List[Value.value], List[Value.value]))],
                             uv: FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                             uw: Nat.nat,
                             ux: Map[Nat.nat, Option[Value.value]]):
      Option[List[Nat.nat]]
  =
  (uu, x1, uv, uw, ux) match {
  case (uu, Nil, uv, uw, ux) => None
  case (rr, (l, (i, uy)) :: es, e, s, r) =>
    {
      val (id, (sa, t)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(e,
            s, r, l, i));
      (if (Lista.list_ex[AExp.aexp[VName.vname]](((p: AExp.aexp[VName.vname]) =>
           AExp.aexp_constrains[VName.vname](p,
      AExp.V[VName.vname](VName.R(rr)))),
          Transition.Outputs[Unit](t)))
        Some[List[Nat.nat]](id)
        else find_first_use_of_trace(rr, es, e, sa,
                                      EFSM.apply_updates(Transition.Updates[Unit](t),
                  AExp.join_ir(i, r), r)))
    }
}

def find_first_uses_of(r: Nat.nat,
                        l: List[List[(String,
                                       (List[Value.value],
 List[Value.value]))]],
                        e: FSet.fset[(List[Nat.nat],
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]):
      List[List[Nat.nat]]
  =
  Lista.maps[Option[List[Nat.nat]],
              List[Nat.nat]](((a: Option[List[Nat.nat]]) =>
                               (a match {
                                  case None => Nil
                                  case Some(x) => List(x)
                                })),
                              Lista.map[List[(String,
       (List[Value.value], List[Value.value]))],
 Option[List[Nat.nat]]](((t: List[(String,
                                    (List[Value.value], List[Value.value]))])
                           =>
                          find_first_use_of_trace(r, t, e, Nat.zero_nata,
           Map().withDefaultValue(None))),
                         l))

def derestrict(log: List[List[(String,
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
                               ((FSet.fset[(List[Nat.nat],
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat),
       ((Transition.transition_ext[Unit], List[Nat.nat]),
         (Transition.transition_ext[Unit], List[Nat.nat]))))]) =>
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
    val pta: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = Inference.make_pta(log)
    val normalised:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = incremental_normalised_pta(log, pta)
    val delayed:
          FSet.fset[(List[Nat.nat],
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = Lista.fold[Nat.nat,
                    FSet.fset[(List[Nat.nat],
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]](((r:
                                  Nat.nat)
                                 =>
                                (acc: FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                                  =>
                                delay_initialisation_of(r, log, acc,
                 find_first_uses_of(r, log, acc))),
                               Lista.sorted_list_of_set[Nat.nat](Inference.all_regs(normalised)),
                               normalised)
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
                        (id, (tf, derestrict_transition(tran)))
                      }),
                     delayed)
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
    (Inference.resolve_nondeterminism(Nil, nondeterministic_pairs, pta,
                                       derestricted, m,
                                       ((a:
   FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])])
  =>
 Inference.satisfies(Set.seta[List[(String,
                                     (List[Value.value],
                                       List[Value.value]))]](log),
                      a)),
                                       np)
       match {
       case None => pta
       case Some(resolved) => resolved
     })
  }

def replace_groups(xs: List[List[(List[Nat.nat],
                                   Transition.transition_ext[Unit])]],
                    e: FSet.fset[(List[Nat.nat],
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]):
      FSet.fset[(List[Nat.nat],
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  Lista.fold[List[(List[Nat.nat], Transition.transition_ext[Unit])],
              FSet.fset[(List[Nat.nat],
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](((a:
                            List[(List[Nat.nat],
                                   Transition.transition_ext[Unit])])
                           =>
                          (b: FSet.fset[(List[Nat.nat],
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
                            =>
                          Lista.fold[(List[Nat.nat],
                                       Transition.transition_ext[Unit]),
                                      FSet.fset[(List[Nat.nat],
          ((Nat.nat, Nat.nat),
            Transition.transition_ext[Unit]))]](((aa:
            (List[Nat.nat], Transition.transition_ext[Unit]))
           =>
          {
            val (id, t): (List[Nat.nat], Transition.transition_ext[Unit]) = aa;
            ((acc: FSet.fset[(List[Nat.nat],
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))])
               =>
              replace_transition(acc, id, t))
          }),
         a, b)),
                         xs, e)

def generalise_outputs(values: List[Value.value],
                        groups:
                          List[(List[(List[Nat.nat],
                                       Transition.transition_ext[Unit])],
                                 List[(Map[Nat.nat, Option[Value.value]],
(List[Value.value], List[Value.value]))])]):
      List[List[(List[Nat.nat],
                  (Transition.transition_ext[Unit],
                    List[(Nat.nat,
                           Option[(AExp.aexp[VName.vname],
                                    Map[VName.vname, String])])]))]]
  =
  Lista.map[(Nat.nat,
              (List[(List[Nat.nat], Transition.transition_ext[Unit])],
                List[(Map[Nat.nat, Option[Value.value]],
                       (List[Value.value], List[Value.value]))])),
             List[(List[Nat.nat],
                    (Transition.transition_ext[Unit],
                      List[(Nat.nat,
                             Option[(AExp.aexp[VName.vname],
                                      Map[VName.vname, String])])]))]](((a:
                                   (Nat.nat,
                                     (List[(List[Nat.nat],
     Transition.transition_ext[Unit])],
                                       List[(Map[Nat.nat, Option[Value.value]],
      (List[Value.value], List[Value.value]))])))
                                  =>
                                 {
                                   val (maxReg, group):
 (Nat.nat,
   (List[(List[Nat.nat], Transition.transition_ext[Unit])],
     List[(Map[Nat.nat, Option[Value.value]],
            (List[Value.value], List[Value.value]))]))
                                     = a
                                   val i: List[List[Value.value]] =
                                     Lista.map[(Map[Nat.nat, Option[Value.value]],
         (List[Value.value], List[Value.value])),
        List[Value.value]](((aa: (Map[Nat.nat, Option[Value.value]],
                                   (List[Value.value], List[Value.value])))
                              =>
                             {
                               val (_, (ins, _)):
                                     (Map[Nat.nat, Option[Value.value]],
                                       (List[Value.value], List[Value.value]))
                                 = aa;
                               ins
                             }),
                            group._2)
                                   val r:
 List[Map[Nat.nat, Option[Value.value]]]
                                     = Lista.map[(Map[Nat.nat, Option[Value.value]],
           (List[Value.value], List[Value.value])),
          Map[Nat.nat, Option[Value.value]]](((aa:
         (Map[Nat.nat, Option[Value.value]],
           (List[Value.value], List[Value.value])))
        =>
       {
         val (regs, (_, _)):
               (Map[Nat.nat, Option[Value.value]],
                 (List[Value.value], List[Value.value]))
           = aa;
         regs
       }),
      group._2)
                                   val p: List[List[Value.value]] =
                                     Lista.map[(Map[Nat.nat, Option[Value.value]],
         (List[Value.value], List[Value.value])),
        List[Value.value]](((aa: (Map[Nat.nat, Option[Value.value]],
                                   (List[Value.value], List[Value.value])))
                              =>
                             {
                               val (_, (_, outs)):
                                     (Map[Nat.nat, Option[Value.value]],
                                       (List[Value.value], List[Value.value]))
                                 = aa;
                               outs
                             }),
                            group._2)
                                   val outputs:
 List[Option[(AExp.aexp[VName.vname], Map[VName.vname, String])]]
                                     = get_outputs(maxReg, values, i, r, p);
                                   Lista.map[(List[Nat.nat],
       Transition.transition_ext[Unit]),
      (List[Nat.nat],
        (Transition.transition_ext[Unit],
          List[(Nat.nat,
                 Option[(AExp.aexp[VName.vname],
                          Map[VName.vname, String])])]))](((aa:
                      (List[Nat.nat], Transition.transition_ext[Unit]))
                     =>
                    {
                      val (id, tran):
                            (List[Nat.nat], Transition.transition_ext[Unit])
                        = aa;
                      (id, (Transition.transition_exta[Unit](Transition.Label[Unit](tran),
                      Transition.Arity[Unit](tran),
                      Transition.Guard[Unit](tran),
                      put_outputs((outputs zip (Transition.Outputs[Unit](tran)))),
                      Transition.Updates[Unit](tran), ()),
                             Lista.enumerate[Option[(AExp.aexp[VName.vname],
              Map[VName.vname, String])]](Nat.zero_nata, outputs)))
                    }),
                   group._1)
                                 }),
                                Lista.enumerate[(List[(List[Nat.nat],
                Transition.transition_ext[Unit])],
          List[(Map[Nat.nat, Option[Value.value]],
                 (List[Value.value],
                   List[Value.value]))])](Nat.zero_nata, groups))

def pta_generalise_outputs(log: List[List[(String,
    (List[Value.value], List[Value.value]))]]):
      (FSet.fset[(List[Nat.nat],
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
        List[List[(List[Nat.nat],
                    (Transition.transition_ext[Unit],
                      List[(Nat.nat,
                             Option[(AExp.aexp[VName.vname],
                                      Map[VName.vname, String])])]))]])
  =
  {
    val values: List[Value.value] = Inference.enumerate_log_values(log)
    val pta: FSet.fset[(List[Nat.nat],
                         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
      = Inference.make_pta(log)
    val training_set:
          List[(List[(List[Nat.nat], Transition.transition_ext[Unit])],
                 List[(Map[Nat.nat, Option[Value.value]],
                        (List[Value.value], List[Value.value]))])]
      = make_training_set(pta, log)
    val generalised_outs:
          List[List[(List[Nat.nat],
                      (Transition.transition_ext[Unit],
                        List[(Nat.nat,
                               Option[(AExp.aexp[VName.vname],
Map[VName.vname, String])])]))]]
      = generalise_outputs(values, training_set);
    (replace_groups(Lista.map[List[(List[Nat.nat],
                                     (Transition.transition_ext[Unit],
                                       List[(Nat.nat,
      Option[(AExp.aexp[VName.vname], Map[VName.vname, String])])]))],
                               List[(List[Nat.nat],
                                      Transition.transition_ext[Unit])]](((a:
                                     List[(List[Nat.nat],
    (Transition.transition_ext[Unit],
      List[(Nat.nat,
             Option[(AExp.aexp[VName.vname], Map[VName.vname, String])])]))])
                                    =>
                                   Lista.map[(List[Nat.nat],
       (Transition.transition_ext[Unit],
         List[(Nat.nat,
                Option[(AExp.aexp[VName.vname], Map[VName.vname, String])])])),
      (List[Nat.nat],
        Transition.transition_ext[Unit])](((aa:
      (List[Nat.nat],
        (Transition.transition_ext[Unit],
          List[(Nat.nat,
                 Option[(AExp.aexp[VName.vname], Map[VName.vname, String])])])))
     =>
    {
      val (tids, (tran, _)):
            (List[Nat.nat],
              (Transition.transition_ext[Unit],
                List[(Nat.nat,
                       Option[(AExp.aexp[VName.vname],
                                Map[VName.vname, String])])]))
        = aa;
      (tids, tran)
    }),
   a)),
                                  generalised_outs),
                     pta),
      generalised_outs)
  }

} /* object PTA_Generalisation */

object SelectionStrategies {

def bool2nat(x0: Boolean): Nat.nat = x0 match {
  case true => Nat.Nata((1))
  case false => Nat.zero_nata
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
    bool2nat((Transition.Label[Unit](t1) ==
               Transition.Label[Unit](t2)) && ((Nat.equal_nata(Transition.Arity[Unit](t1),
                        Transition.Arity[Unit](t2))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).length),
                                 Nat.Nata((Transition.Outputs[Unit](t2)).length)))))
  }

def exactly_equal(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                   e: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  bool2nat(Transition.equal_transition_exta[Unit](Inference.get_by_ids(e, t1ID),
           Inference.get_by_ids(e, t2ID)))

def origin_states(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                   e: FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1Orig: Nat.nat = Inference.origin(t1ID, e)
    val t2Orig: Nat.nat = Inference.origin(t2ID, e);
    (if ((Nat.equal_nata(t1Orig,
                          Code_Numeral.nat_of_integer(BigInt(9)))) && (Nat.equal_nata(t2Orig,
       Code_Numeral.nat_of_integer(BigInt(58)))))
      Code_Numeral.nat_of_integer(BigInt(1000)) else Nat.zero_nata)
  }

def naive_score_outputs(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                         e: FSet.fset[(List[Nat.nat],
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t2ID);
    Nat.plus_nata(Nat.plus_nata(bool2nat(Transition.Label[Unit](t1) ==
   Transition.Label[Unit](t2)),
                                 bool2nat(Nat.equal_nata(Transition.Arity[Unit](t1),
                  Transition.Arity[Unit](t2)))),
                   bool2nat(Lista.equal_lista[AExp.aexp[VName.vname]](Transition.Outputs[Unit](t1),
                               Transition.Outputs[Unit](t2))))
  }

def naive_score_eq_bonus(t1ID: List[Nat.nat], t2ID: List[Nat.nat],
                          e: FSet.fset[(List[Nat.nat],
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_ids(e, t2ID);
    Nat.plus_nata(bool2nat((Transition.Label[Unit](t1) ==
                             Transition.Label[Unit](t2)) && ((Nat.equal_nata(Transition.Arity[Unit](t1),
                                      Transition.Arity[Unit](t2))) && (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).length),
       Nat.Nata((Transition.Outputs[Unit](t2)).length))))),
                   bool2nat(Transition.equal_transition_exta[Unit](t1, t2)))
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
      (if (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).length),
                           Nat.Nata((Transition.Outputs[Unit](t2)).length)))
        Nat.plus_nata(Finite_Set.card[GExp.gexp[VName.vname]](Set.inf_set[GExp.gexp[VName.vname]](Set.seta[GExp.gexp[VName.vname]](Transition.Guard[Unit](t1)),
                   Set.seta[GExp.gexp[VName.vname]](Transition.Guard[Unit](t2)))),
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
                                  ((Transition.Outputs[Unit](t1)) zip (Transition.Outputs[Unit](t2))))).length))
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
             (if (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](t1)).length),
                                  Nat.Nata((Transition.Outputs[Unit](t2)).length)))
               Nat.plus_nata(Finite_Set.card[GExp.gexp[VName.vname]](Set.inf_set[GExp.gexp[VName.vname]](Set.seta[GExp.gexp[VName.vname]](Transition.Guard[Unit](t1)),
                          Set.seta[GExp.gexp[VName.vname]](Transition.Guard[Unit](t2)))),
                              Nat.Nata((Lista.filter[(AExp.aexp[VName.vname],
               AExp.aexp[VName.vname])](((a:
    (AExp.aexp[VName.vname], AExp.aexp[VName.vname]))
   =>
  {
    val (aa, b): (AExp.aexp[VName.vname], AExp.aexp[VName.vname]) = a;
    AExp.equal_aexpa[VName.vname](aa, b)
  }),
 ((Transition.Outputs[Unit](t1)) zip (Transition.Outputs[Unit](t2))))).length))
               else Nat.zero_nata)
             else Nat.zero_nata))
  }

} /* object SelectionStrategies */

object Distinguishing_Guards {

def add_guard(t: Transition.transition_ext[Unit], g: GExp.gexp[VName.vname]):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    g :: Transition.Guard[Unit](t),
                                    Transition.Outputs[Unit](t),
                                    Transition.Updates[Unit](t), ())

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
  case ((label, (inputs, outputs)) :: t, uPTA, s, registers, t1, t2, g1, g2) =>
    {
      val (uids, (sa, tran)):
            (List[Nat.nat], (Nat.nat, Transition.transition_ext[Unit]))
        = FSet.fthe_elem[(List[Nat.nat],
                           (Nat.nat,
                             Transition.transition_ext[Unit]))](Inference.i_possible_steps(uPTA,
            s, registers, label, inputs))
      val updated: Map[Nat.nat, Option[Value.value]] =
        EFSM.apply_updates(Transition.Updates[Unit](tran),
                            AExp.join_ir(inputs, registers), registers);
      (if (t1 contains (uids.head))
        trace_collect_training_sets(t, uPTA, sa, updated, t1, t2,
                                     (inputs, registers) :: g1, g2)
        else (if (t2 contains (uids.head))
               trace_collect_training_sets(t, uPTA, sa, updated, t1, t2, g1,
    (inputs, registers) :: g2)
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
  case (h :: t, uPTA, t1, t2, g1, g2) =>
    {
      val (g1a, g2a):
            (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])],
              List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])
        = trace_collect_training_sets(h, uPTA, Nat.zero_nata,
                                       Map().withDefaultValue(None), t1, t2,
                                       Nil, Nil);
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
                  val List(u): List[Nat.nat] = uid;
                  (if (uids contains u)
                    (uid, (fromTo,
                            Transition.transition_exta[Unit](Transition.Label[Unit](tran),
                      Transition.Arity[Unit](tran),
                      Transition.Guard[Unit](tran),
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

def distinguish(log: List[List[(String,
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
                 np: (FSet.fset[(List[Nat.nat],
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]) =>
                       FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     ((Transition.transition_ext[Unit],
List[Nat.nat]),
                                       (Transition.transition_ext[Unit],
 List[Nat.nat]))))]):
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
      = transfer_updates(destMerge, Inference.make_pta(log))
    val (g1, g2):
          (List[(List[Value.value], Map[Nat.nat, Option[Value.value]])],
            List[(List[Value.value], Map[Nat.nat, Option[Value.value]])])
      = collect_training_sets(log, uPTA, t1ID, t2ID, Nil, Nil);
    (Dirties.findDistinguishingGuard(g1, g2) match {
       case None => None
       case Some((g1a, g2a)) =>
         {
           val newEFSM:
                 FSet.fset[(List[Nat.nat],
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]
             = Inference.replace_transitions(preDestMerge,
      List((t1ID, add_guard(t1, g1a)), (t2ID, add_guard(t2, g2a))));
           Inference.resolve_nondeterminism(Nil,
     FSet.sorted_list_of_fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  ((Transition.transition_ext[Unit],
                                     List[Nat.nat]),
                                    (Transition.transition_ext[Unit],
                                      List[Nat.nat]))))](np(newEFSM)),
     old, newEFSM,
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
       (g: (FSet.fset[(List[Nat.nat],
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))]) =>
             FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           ((Transition.transition_ext[Unit], List[Nat.nat]),
                             (Transition.transition_ext[Unit],
                               List[Nat.nat]))))])
         =>
       Inference.null_modifier(a, b, c, d, e, f, g)),
     ((_: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
       true),
     np)
         }
     })
  }

} /* object Distinguishing_Guards */
