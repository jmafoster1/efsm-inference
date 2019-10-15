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
  implicit def `GExp.equal_gexp`: equal[GExp.gexp] = new equal[GExp.gexp] {
    val `HOL.equal` = (a: GExp.gexp, b: GExp.gexp) => GExp.equal_gexpa(a, b)
  }
  implicit def `FSet.equal_fset`[A : equal]: equal[FSet.fset[A]] = new
    equal[FSet.fset[A]] {
    val `HOL.equal` = (a: FSet.fset[A], b: FSet.fset[A]) =>
      FSet.equal_fseta[A](a, b)
  }
  implicit def `AExp.equal_aexp`: equal[AExp.aexp] = new equal[AExp.aexp] {
    val `HOL.equal` = (a: AExp.aexp, b: AExp.aexp) => AExp.equal_aexpa(a, b)
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
  implicit def
    `Option_Lexorder.ord_option`[A : HOL.equal : linorder]: ord[Option[A]] = new
    ord[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_Lexorder.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_Lexorder.less_option[A](a, b)
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
  implicit def `GExp_Orderings.ord_gexp`: ord[GExp.gexp] = new ord[GExp.gexp] {
    val `Orderings.less_eq` = (a: GExp.gexp, b: GExp.gexp) =>
      GExp_Orderings.less_eq_gexp(a, b)
    val `Orderings.less` = (a: GExp.gexp, b: GExp.gexp) =>
      GExp_Orderings.less_gexp(a, b)
  }
  implicit def `GExp_Orderings.ord_aexp`: ord[AExp.aexp] = new ord[AExp.aexp] {
    val `Orderings.less_eq` = (a: AExp.aexp, b: AExp.aexp) =>
      GExp_Orderings.less_eq_aexp(a, b)
    val `Orderings.less` = (a: AExp.aexp, b: AExp.aexp) =>
      GExp_Orderings.less_aexp(a, b)
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
  implicit def
    `Option_Lexorder.preorder_option`[A : HOL.equal : linorder]:
      preorder[Option[A]]
    = new preorder[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_Lexorder.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_Lexorder.less_option[A](a, b)
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
  implicit def `GExp_Orderings.preorder_gexp`: preorder[GExp.gexp] = new
    preorder[GExp.gexp] {
    val `Orderings.less_eq` = (a: GExp.gexp, b: GExp.gexp) =>
      GExp_Orderings.less_eq_gexp(a, b)
    val `Orderings.less` = (a: GExp.gexp, b: GExp.gexp) =>
      GExp_Orderings.less_gexp(a, b)
  }
  implicit def `GExp_Orderings.preorder_aexp`: preorder[AExp.aexp] = new
    preorder[AExp.aexp] {
    val `Orderings.less_eq` = (a: AExp.aexp, b: AExp.aexp) =>
      GExp_Orderings.less_eq_aexp(a, b)
    val `Orderings.less` = (a: AExp.aexp, b: AExp.aexp) =>
      GExp_Orderings.less_aexp(a, b)
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
  implicit def
    `Option_Lexorder.order_option`[A : HOL.equal : linorder]: order[Option[A]] =
    new order[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_Lexorder.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_Lexorder.less_option[A](a, b)
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
  implicit def `GExp_Orderings.order_gexp`: order[GExp.gexp] = new
    order[GExp.gexp] {
    val `Orderings.less_eq` = (a: GExp.gexp, b: GExp.gexp) =>
      GExp_Orderings.less_eq_gexp(a, b)
    val `Orderings.less` = (a: GExp.gexp, b: GExp.gexp) =>
      GExp_Orderings.less_gexp(a, b)
  }
  implicit def `GExp_Orderings.order_aexp`: order[AExp.aexp] = new
    order[AExp.aexp] {
    val `Orderings.less_eq` = (a: AExp.aexp, b: AExp.aexp) =>
      GExp_Orderings.less_eq_aexp(a, b)
    val `Orderings.less` = (a: AExp.aexp, b: AExp.aexp) =>
      GExp_Orderings.less_aexp(a, b)
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
  implicit def
    `Option_Lexorder.linorder_option`[A : HOL.equal : linorder]:
      linorder[Option[A]]
    = new linorder[Option[A]] {
    val `Orderings.less_eq` = (a: Option[A], b: Option[A]) =>
      Option_Lexorder.less_eq_option[A](a, b)
    val `Orderings.less` = (a: Option[A], b: Option[A]) =>
      Option_Lexorder.less_option[A](a, b)
  }
  implicit def `VName.linorder_vname`: linorder[VName.vname] = new
    linorder[VName.vname] {
    val `Orderings.less_eq` = (a: VName.vname, b: VName.vname) =>
      VName.less_eq_vname(a, b)
    val `Orderings.less` = (a: VName.vname, b: VName.vname) =>
      VName.less_vname(a, b)
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

} /* object Optiona */

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

def insert[A : HOL.equal](x: A, xs: List[A]): List[A] =
  (if (xs contains x) xs else x :: xs)

def union[A : HOL.equal]: (List[A]) => (List[A]) => List[A] =
  ((a: List[A]) => (b: List[A]) =>
    fold[A, List[A]](((aa: A) => (ba: List[A]) => insert[A](aa, ba)), a, b))

def filter[A](l: A => Boolean, f: List[A]): List[A] = f.filter(l)

def list_ex[A](f: A => Boolean, l: List[A]): Boolean = l.exists(f)

def map[A, B](f: A => B, l: List[A]): List[B] = l.map(f)

def product[A, B](xs: List[A], ys: List[B]): List[(A, B)] =
  maps[A, (A, B)](((x: A) => map[B, (A, B)](((a: B) => (x, a)), ys)), xs)

def enumerate[A](n: Nat.nat, xs: List[A]): List[(Nat.nat, A)] =
  ((upt(n, Nat.plus_nata(n, Nat.Nata(xs.length)))) zip xs)

def removeAll[A : HOL.equal](a: A, l: List[A]): List[A] =
  filter[A](((x: A) => ! (HOL.eq[A](x, a))), l)

def map_filter[A, B](f: A => Option[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => (f(x) match {
                          case None => map_filter[A, B](f, xs)
                          case Some(y) => y :: map_filter[A, B](f, xs)
                        })
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

def sorted_list_of_set[A : HOL.equal : Orderings.linorder](x0: Set.set[A]):
      List[A]
  =
  x0 match {
  case Set.seta(xs) => sort_key[A, A](((x: A) => x), xs.distinct)
}

} /* object Lista */

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

def insert[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, seta(s)) => (if (s contains x) seta[A](s) else seta[A](x :: s))
}

def member[A : HOL.equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, seta(xs)) => xs contains x
}

def bot_set[A]: set[A] = seta[A](Nil)

def inf_set[A : HOL.equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, seta(xs)) =>
    seta[A](Lista.filter[A](((x: A) => member[A](x, a)), xs))
}

def sup_set[A : HOL.equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (seta(x), seta(y)) => seta[A](x ++ y)
  case (seta(xs), a) =>
    Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => insert[A](aa, b)), xs, a)
}

def less_eq_set[A : HOL.equal](a: set[A], b: set[A]): Boolean =
  Ball[A](a, ((x: A) => member[A](x, b)))

def less_set[A : HOL.equal](a: set[A], b: set[A]): Boolean =
  (less_eq_set[A](a, b)) && (! (less_eq_set[A](b, a)))

def equal_set[A : HOL.equal](a: set[A], b: set[A]): Boolean =
  (less_eq_set[A](a, b)) && (less_eq_set[A](b, a))

} /* object Set */

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

abstract sealed class aexp
final case class L(a: Value.value) extends aexp
final case class V(a: VName.vname) extends aexp
final case class Plus(a: aexp, b: aexp) extends aexp
final case class Minus(a: aexp, b: aexp) extends aexp

def equal_aexpa(x0: aexp, x1: aexp): Boolean = (x0, x1) match {
  case (Plus(x31, x32), Minus(x41, x42)) => false
  case (Minus(x41, x42), Plus(x31, x32)) => false
  case (V(x2), Minus(x41, x42)) => false
  case (Minus(x41, x42), V(x2)) => false
  case (V(x2), Plus(x31, x32)) => false
  case (Plus(x31, x32), V(x2)) => false
  case (L(x1), Minus(x41, x42)) => false
  case (Minus(x41, x42), L(x1)) => false
  case (L(x1), Plus(x31, x32)) => false
  case (Plus(x31, x32), L(x1)) => false
  case (L(x1), V(x2)) => false
  case (V(x2), L(x1)) => false
  case (Minus(x41, x42), Minus(y41, y42)) =>
    (equal_aexpa(x41, y41)) && (equal_aexpa(x42, y42))
  case (Plus(x31, x32), Plus(y31, y32)) =>
    (equal_aexpa(x31, y31)) && (equal_aexpa(x32, y32))
  case (V(x2), V(y2)) => VName.equal_vnamea(x2, y2)
  case (L(x1), L(y1)) => Value.equal_valuea(x1, y1)
}

def MaybeArithInt(f: Int.int => Int.int => Int.int, uv: Option[Value.value],
                   uw: Option[Value.value]):
      Option[Value.value]
  =
  (f, uv, uw) match {
  case (f, Some(Value.Numa(x)), Some(Value.Numa(y))) =>
    Some[Value.value](Value.Numa((f(x))(y)))
  case (uu, None, uw) => None
  case (uu, Some(Value.Str(va)), uw) => None
  case (uu, uv, None) => None
  case (uu, uv, Some(Value.Str(va))) => None
}

def value_minus:
      Option[Value.value] => Option[Value.value] => Option[Value.value]
  =
  ((a: Option[Value.value]) => (b: Option[Value.value]) =>
    MaybeArithInt(((aa: Int.int) => (ba: Int.int) => Int.minus_int(aa, ba)), a,
                   b))

def value_plus:
      Option[Value.value] => Option[Value.value] => Option[Value.value]
  =
  ((a: Option[Value.value]) => (b: Option[Value.value]) =>
    MaybeArithInt(((aa: Int.int) => (ba: Int.int) => Int.plus_int(aa, ba)), a,
                   b))

def aval(x0: aexp, s: VName.vname => Option[Value.value]): Option[Value.value] =
  (x0, s) match {
  case (L(x), s) => Some[Value.value](x)
  case (V(x), s) => s(x)
  case (Plus(a_1, a_2), s) => value_plus.apply(aval(a_1, s)).apply(aval(a_2, s))
  case (Minus(a_1, a_2), s) =>
    value_minus.apply(aval(a_1, s)).apply(aval(a_2, s))
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

def aexp_constrains(x0: aexp, a: aexp): Boolean = (x0, a) match {
  case (L(l), a) => equal_aexpa(L(l), a)
  case (V(va), v) => equal_aexpa(V(va), v)
  case (Plus(a1, a2), v) =>
    (equal_aexpa(Plus(a1, a2),
                  v)) || ((equal_aexpa(Plus(a1, a2),
v)) || ((aexp_constrains(a1, v)) || (aexp_constrains(a2, v))))
  case (Minus(a1, a2), v) =>
    (equal_aexpa(Minus(a1, a2),
                  v)) || ((aexp_constrains(a1, v)) || (aexp_constrains(a2, v)))
}

def aexp_same_structure(x0: aexp, x1: aexp): Boolean = (x0, x1) match {
  case (L(va), L(v)) => true
  case (V(va), V(v)) => true
  case (Plus(a1a, a2a), Plus(a1, a2)) =>
    (aexp_same_structure(a1a, a1)) && (aexp_same_structure(a2a, a2))
  case (Minus(a1a, a2a), Minus(a1, a2)) =>
    (aexp_same_structure(a1a, a1)) && (aexp_same_structure(a2a, a2))
  case (V(v), L(va)) => false
  case (V(v), Plus(va, vb)) => false
  case (V(v), Minus(va, vb)) => false
  case (Plus(v, va), L(vb)) => false
  case (Plus(v, va), V(vb)) => false
  case (Plus(v, va), Minus(vb, vc)) => false
  case (Minus(v, va), L(vb)) => false
  case (Minus(v, va), V(vb)) => false
  case (Minus(v, va), Plus(vb, vc)) => false
  case (L(va), V(v)) => false
  case (L(vb), Plus(v, va)) => false
  case (L(vb), Minus(v, va)) => false
}

def enumerate_aexp_ints(x0: aexp): Set.set[Int.int] = x0 match {
  case L(Value.Str(s)) => Set.bot_set[Int.int]
  case L(Value.Numa(s)) => Set.insert[Int.int](s, Set.bot_set[Int.int])
  case V(uu) => Set.bot_set[Int.int]
  case Plus(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints(a1), enumerate_aexp_ints(a2))
  case Minus(a1, a2) =>
    Set.sup_set[Int.int](enumerate_aexp_ints(a1), enumerate_aexp_ints(a2))
}

def enumerate_aexp_regs(x0: aexp): Set.set[Nat.nat] = x0 match {
  case L(uu) => Set.bot_set[Nat.nat]
  case V(VName.R(n)) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case V(VName.I(uv)) => Set.bot_set[Nat.nat]
  case Plus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
  case Minus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
}

def enumerate_aexp_inputs(x0: aexp): Set.set[Nat.nat] = x0 match {
  case L(uu) => Set.bot_set[Nat.nat]
  case V(VName.I(n)) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case V(VName.R(n)) => Set.bot_set[Nat.nat]
  case Plus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs(v), enumerate_aexp_inputs(va))
  case Minus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_inputs(v), enumerate_aexp_inputs(va))
}

} /* object AExp */

object Complete_Lattices {

def Sup_set[A : HOL.equal](x0: Set.set[Set.set[A]]): Set.set[A] = x0 match {
  case Set.seta(xs) =>
    Lista.fold[Set.set[A],
                Set.set[A]](((a: Set.set[A]) => (b: Set.set[A]) =>
                              Set.sup_set[A](a, b)),
                             xs, Set.bot_set[A])
}

} /* object Complete_Lattices */

object Option_Lexorder {

def less_option[A : Orderings.linorder](x0: Option[A], x1: Option[A]): Boolean =
  (x0, x1) match {
  case (None, None) => false
  case (None, Some(v)) => true
  case (Some(uv), None) => false
  case (Some(a), Some(b)) => Orderings.less[A](a, b)
}

def less_eq_option[A : HOL.equal : Orderings.linorder](a: Option[A],
                b: Option[A]):
      Boolean
  =
  (less_option[A](a, b)) || (Optiona.equal_optiona[A](a, b))

} /* object Option_Lexorder */

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

def eq_set[A : card_UNIV : HOL.equal](x0: Set.set[A], x1: Set.set[A]): Boolean =
  (x0, x1) match {
  case (Set.seta(xs), Set.seta(ys)) =>
    (Lista.list_all[A](((a: A) => ys contains a),
                        xs)) && (Lista.list_all[A](((a: A) => xs contains a),
            ys))
}

} /* object Cardinality */

object GExp {

abstract sealed class gexp
final case class Bc(a: Boolean) extends gexp
final case class Eq(a: AExp.aexp, b: AExp.aexp) extends gexp
final case class Gt(a: AExp.aexp, b: AExp.aexp) extends gexp
final case class Null(a: AExp.aexp) extends gexp
final case class In(a: VName.vname, b: List[Value.value]) extends gexp
final case class Nor(a: gexp, b: gexp) extends gexp

def equal_gexpa(x0: gexp, x1: gexp): Boolean = (x0, x1) match {
  case (In(x51, x52), Nor(x61, x62)) => false
  case (Nor(x61, x62), In(x51, x52)) => false
  case (Null(x4), Nor(x61, x62)) => false
  case (Nor(x61, x62), Null(x4)) => false
  case (Null(x4), In(x51, x52)) => false
  case (In(x51, x52), Null(x4)) => false
  case (Gt(x31, x32), Nor(x61, x62)) => false
  case (Nor(x61, x62), Gt(x31, x32)) => false
  case (Gt(x31, x32), In(x51, x52)) => false
  case (In(x51, x52), Gt(x31, x32)) => false
  case (Gt(x31, x32), Null(x4)) => false
  case (Null(x4), Gt(x31, x32)) => false
  case (Eq(x21, x22), Nor(x61, x62)) => false
  case (Nor(x61, x62), Eq(x21, x22)) => false
  case (Eq(x21, x22), In(x51, x52)) => false
  case (In(x51, x52), Eq(x21, x22)) => false
  case (Eq(x21, x22), Null(x4)) => false
  case (Null(x4), Eq(x21, x22)) => false
  case (Eq(x21, x22), Gt(x31, x32)) => false
  case (Gt(x31, x32), Eq(x21, x22)) => false
  case (Bc(x1), Nor(x61, x62)) => false
  case (Nor(x61, x62), Bc(x1)) => false
  case (Bc(x1), In(x51, x52)) => false
  case (In(x51, x52), Bc(x1)) => false
  case (Bc(x1), Null(x4)) => false
  case (Null(x4), Bc(x1)) => false
  case (Bc(x1), Gt(x31, x32)) => false
  case (Gt(x31, x32), Bc(x1)) => false
  case (Bc(x1), Eq(x21, x22)) => false
  case (Eq(x21, x22), Bc(x1)) => false
  case (Nor(x61, x62), Nor(y61, y62)) =>
    (equal_gexpa(x61, y61)) && (equal_gexpa(x62, y62))
  case (In(x51, x52), In(y51, y52)) =>
    (VName.equal_vnamea(x51, y51)) && (Lista.equal_lista[Value.value](x52, y52))
  case (Null(x4), Null(y4)) => AExp.equal_aexpa(x4, y4)
  case (Gt(x31, x32), Gt(y31, y32)) =>
    (AExp.equal_aexpa(x31, y31)) && (AExp.equal_aexpa(x32, y32))
  case (Eq(x21, x22), Eq(y21, y22)) =>
    (AExp.equal_aexpa(x21, y21)) && (AExp.equal_aexpa(x22, y22))
  case (Bc(x1), Bc(y1)) => x1 == y1
}

def gval(x0: gexp, uu: VName.vname => Option[Value.value]): Trilean.trilean =
  (x0, uu) match {
  case (Bc(true), uu) => Trilean.truea()
  case (Bc(false), uv) => Trilean.falsea()
  case (Gt(a_1, a_2), s) => Value.value_gt(AExp.aval(a_1, s), AExp.aval(a_2, s))
  case (Eq(a_1, a_2), s) => Value.value_eq(AExp.aval(a_1, s), AExp.aval(a_2, s))
  case (Null(v), s) => Value.value_eq(AExp.aval(v, s), None)
  case (In(v, l), s) =>
    (if ((Lista.map[Value.value,
                     Option[Value.value]](((a: Value.value) =>
    Some[Value.value](a)),
   l)) contains (s(v)))
      Trilean.truea() else Trilean.falsea())
  case (Nor(a_1, a_2), s) =>
    Trilean.maybe_not(Trilean.plus_trilean(gval(a_1, s), gval(a_2, s)))
}

def fold_In(uu: VName.vname, x1: List[Value.value]): gexp = (uu, x1) match {
  case (uu, Nil) => Bc(false)
  case (v, List(l)) => Eq(AExp.V(v), AExp.L(l))
  case (v, l :: va :: vb) =>
    Lista.fold[Value.value,
                gexp](Fun.comp[gexp, gexp => gexp,
                                Value.value](((vc: gexp) => (vaa: gexp) =>
       Nor(Nor(vc, vaa), Nor(vc, vaa))),
      ((x: Value.value) => Eq(AExp.V(v), AExp.L(x)))),
                       va :: vb, Eq(AExp.V(v), AExp.L(l)))
}

def enumerate_gexp_regs(x0: gexp): Set.set[Nat.nat] = x0 match {
  case Bc(uu) => Set.bot_set[Nat.nat]
  case Null(v) => AExp.enumerate_aexp_regs(v)
  case Eq(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_regs(v),
                          AExp.enumerate_aexp_regs(va))
  case Gt(va, v) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_regs(v),
                          AExp.enumerate_aexp_regs(va))
  case In(v, va) => AExp.enumerate_aexp_regs(AExp.V(v))
  case Nor(v, va) =>
    Set.sup_set[Nat.nat](enumerate_gexp_regs(v), enumerate_gexp_regs(va))
}

def max_reg(g: gexp): Option[Nat.nat] =
  {
    val regs: Set.set[Nat.nat] = enumerate_gexp_regs(g);
    (if (Cardinality.eq_set[Nat.nat](regs, Set.bot_set[Nat.nat])) None
      else Some[Nat.nat](Lattices_Big.Max[Nat.nat](regs)))
  }

def enumerate_gexp_inputs(x0: gexp): Set.set[Nat.nat] = x0 match {
  case Bc(uu) => Set.bot_set[Nat.nat]
  case Null(v) => AExp.enumerate_aexp_inputs(v)
  case Eq(v, va) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_inputs(v),
                          AExp.enumerate_aexp_inputs(va))
  case Gt(va, v) =>
    Set.sup_set[Nat.nat](AExp.enumerate_aexp_inputs(v),
                          AExp.enumerate_aexp_inputs(va))
  case In(v, va) => AExp.enumerate_aexp_inputs(AExp.V(v))
  case Nor(v, va) =>
    Set.sup_set[Nat.nat](enumerate_gexp_inputs(v), enumerate_gexp_inputs(va))
}

def max_input(g: gexp): Option[Nat.nat] =
  {
    val inputs: Set.set[Nat.nat] = enumerate_gexp_inputs(g);
    (if (Cardinality.eq_set[Nat.nat](inputs, Set.bot_set[Nat.nat])) None
      else Some[Nat.nat](Lattices_Big.Max[Nat.nat](inputs)))
  }

def apply_guards(g: List[gexp], s: VName.vname => Option[Value.value]): Boolean
  =
  Lista.list_all[Trilean.trilean](((ga: Trilean.trilean) =>
                                    Trilean.equal_trilean(ga, Trilean.truea())),
                                   Lista.map[gexp,
      Trilean.trilean](((ga: gexp) => gval(ga, s)), g))

def max_reg_list(g: List[gexp]): Option[Nat.nat] =
  Lista.fold[gexp,
              Option[Nat.nat]](Fun.comp[Option[Nat.nat],
 Option[Nat.nat] => Option[Nat.nat],
 gexp](((a: Option[Nat.nat]) => (b: Option[Nat.nat]) =>
         Orderings.max[Option[Nat.nat]](a, b)),
        ((a: gexp) => max_reg(a))),
                                g, None)

def enumerate_vars(g: gexp): List[VName.vname] =
  Lista.sorted_list_of_set[VName.vname](Set.sup_set[VName.vname](Set.image[Nat.nat,
                                    VName.vname](((a: Nat.nat) => VName.R(a)),
          enumerate_gexp_regs(g)),
                          Set.image[Nat.nat,
                                     VName.vname](((a: Nat.nat) => VName.I(a)),
           enumerate_gexp_inputs(g))))

def max_input_list(g: List[gexp]): Option[Nat.nat] =
  Lista.fold[gexp,
              Option[Nat.nat]](Fun.comp[Option[Nat.nat],
 Option[Nat.nat] => Option[Nat.nat],
 gexp](((a: Option[Nat.nat]) => (b: Option[Nat.nat]) =>
         Orderings.max[Option[Nat.nat]](a, b)),
        ((a: gexp) => max_input(a))),
                                g, None)

def gexp_constrains(x0: gexp, uv: AExp.aexp): Boolean = (x0, uv) match {
  case (Bc(uu), uv) => false
  case (Null(aa), a) => AExp.aexp_constrains(aa, a)
  case (Eq(a1, a2), a) =>
    (AExp.aexp_constrains(a1, a)) || (AExp.aexp_constrains(a2, a))
  case (Gt(a1, a2), a) =>
    (AExp.aexp_constrains(a1, a)) || (AExp.aexp_constrains(a2, a))
  case (Nor(g1, g2), a) => (gexp_constrains(g1, a)) || (gexp_constrains(g2, a))
  case (In(v, l), a) => AExp.aexp_constrains(AExp.V(v), a)
}

def restricted_once(v: VName.vname, g: List[gexp]): Boolean =
  Nat.equal_nata(Nat.Nata((Lista.filter[gexp](((ga: gexp) =>
        gexp_constrains(ga, AExp.V(v))),
       g)).length),
                  Nat.Nata((1)))

def enumerate_gexp_ints(x0: gexp): Set.set[Int.int] = x0 match {
  case Bc(uu) => Set.bot_set[Int.int]
  case Eq(a1, a2) =>
    Set.sup_set[Int.int](AExp.enumerate_aexp_ints(a1),
                          AExp.enumerate_aexp_ints(a2))
  case Gt(a1, a2) =>
    Set.sup_set[Int.int](AExp.enumerate_aexp_ints(a1),
                          AExp.enumerate_aexp_ints(a2))
  case In(v, l) =>
    Set.sup_set[Int.int](AExp.enumerate_aexp_ints(AExp.V(v)),
                          Lista.fold[Value.value,
                                      Set.set[Int.int]](Fun.comp[Set.set[Int.int],
                          (Set.set[Int.int]) => Set.set[Int.int],
                          Value.value](((a: Set.set[Int.int]) =>
 (b: Set.set[Int.int]) => Set.sup_set[Int.int](a, b)),
((x: Value.value) => AExp.enumerate_aexp_ints(AExp.L(x)))),
                 l, Set.bot_set[Int.int]))
  case Nor(g1, g2) =>
    Set.sup_set[Int.int](enumerate_gexp_ints(g1), enumerate_gexp_ints(g2))
  case Null(a) => AExp.enumerate_aexp_ints(a)
}

def gexp_same_structure(x0: gexp, x1: gexp): Boolean = (x0, x1) match {
  case (Bc(ba), Bc(b)) => ba == b
  case (Eq(a1a, a2a), Eq(a1, a2)) =>
    (AExp.aexp_same_structure(a1a, a1)) && (AExp.aexp_same_structure(a2a, a2))
  case (Gt(a1a, a2a), Gt(a1, a2)) =>
    (AExp.aexp_same_structure(a1a, a1)) && (AExp.aexp_same_structure(a2a, a2))
  case (Nor(g1a, g2a), Nor(g1, g2)) =>
    (gexp_same_structure(g1a, g1)) && (gexp_same_structure(g2a, g2))
  case (Null(a1), Null(a2)) => AExp.aexp_same_structure(a1, a2)
  case (In(va, la), In(v, l)) =>
    (VName.equal_vnamea(va, v)) && (Lista.equal_lista[Value.value](la, l))
  case (Eq(v, va), Bc(vb)) => false
  case (Eq(v, va), Gt(vb, vc)) => false
  case (Eq(v, va), Null(vb)) => false
  case (Eq(v, va), In(vb, vc)) => false
  case (Eq(v, va), Nor(vb, vc)) => false
  case (Gt(v, va), Bc(vb)) => false
  case (Gt(v, va), Eq(vb, vc)) => false
  case (Gt(v, va), Null(vb)) => false
  case (Gt(v, va), In(vb, vc)) => false
  case (Gt(v, va), Nor(vb, vc)) => false
  case (Null(v), Bc(va)) => false
  case (Null(v), Eq(va, vb)) => false
  case (Null(v), Gt(va, vb)) => false
  case (Null(v), In(va, vb)) => false
  case (Null(v), Nor(va, vb)) => false
  case (In(v, va), Bc(vb)) => false
  case (In(v, va), Eq(vb, vc)) => false
  case (In(v, va), Gt(vb, vc)) => false
  case (In(v, va), Null(vb)) => false
  case (In(v, va), Nor(vb, vc)) => false
  case (Nor(v, va), Bc(vb)) => false
  case (Nor(v, va), Eq(vb, vc)) => false
  case (Nor(v, va), Gt(vb, vc)) => false
  case (Nor(v, va), Null(vb)) => false
  case (Nor(v, va), In(vb, vc)) => false
  case (Bc(vb), Eq(v, va)) => false
  case (Bc(vb), Gt(v, va)) => false
  case (Bc(va), Null(v)) => false
  case (Bc(vb), In(v, va)) => false
  case (Bc(vb), Nor(v, va)) => false
}

} /* object GExp */

object GExp_Orderings {

def less_aexpr(x0: AExp.aexp, x1: AExp.aexp): Boolean = (x0, x1) match {
  case (AExp.L(l1), AExp.L(l2)) => Value.less_value(l1, l2)
  case (AExp.L(l1), AExp.V(v2)) => true
  case (AExp.L(l1), AExp.Plus(e1, e2)) => true
  case (AExp.L(l1), AExp.Minus(e1, e2)) => true
  case (AExp.V(v1), AExp.L(l1)) => false
  case (AExp.V(v1), AExp.V(v2)) => VName.less_vname(v1, v2)
  case (AExp.V(v1), AExp.Plus(e1, e2)) => true
  case (AExp.V(v1), AExp.Minus(e1, e2)) => true
  case (AExp.Plus(e1, e2), AExp.L(l2)) => false
  case (AExp.Plus(e1, e2), AExp.V(v2)) => false
  case (AExp.Plus(e1a, e2a), AExp.Plus(e1, e2)) =>
    (less_aexpr(e1a, e1)) || ((AExp.equal_aexpa(e1a,
         e1)) && (less_aexpr(e2a, e2)))
  case (AExp.Plus(e1a, e2a), AExp.Minus(e1, e2)) => true
  case (AExp.Minus(e1, e2), AExp.L(l2)) => false
  case (AExp.Minus(e1, e2), AExp.V(v2)) => false
  case (AExp.Minus(e1a, e2a), AExp.Plus(e1, e2)) => false
  case (AExp.Minus(e1a, e2a), AExp.Minus(e1, e2)) =>
    (less_aexpr(e1a, e1)) || ((AExp.equal_aexpa(e1a,
         e1)) && (less_aexpr(e2a, e2)))
}

def less_eq_aexp(e1: AExp.aexp, e2: AExp.aexp): Boolean =
  (less_aexpr(e1, e2)) || (AExp.equal_aexpa(e1, e2))

def less_aexp(e1: AExp.aexp, e2: AExp.aexp): Boolean = less_aexpr(e1, e2)

def less_gexpr(x0: GExp.gexp, x1: GExp.gexp): Boolean = (x0, x1) match {
  case (GExp.Bc(b1), GExp.Bc(b2)) => Orderings.less_bool(b1, b2)
  case (GExp.Bc(b1), GExp.Eq(v, va)) => true
  case (GExp.Bc(b1), GExp.Gt(v, va)) => true
  case (GExp.Bc(b1), GExp.Null(v)) => true
  case (GExp.Bc(b1), GExp.In(v, va)) => true
  case (GExp.Bc(b1), GExp.Nor(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.Bc(b2)) => false
  case (GExp.Eq(e1a, e2a), GExp.Eq(e1, e2)) =>
    (less_aexpr(e1a, e1)) || ((AExp.equal_aexpa(e1a,
         e1)) && (less_aexpr(e2a, e2)))
  case (GExp.Eq(e1, e2), GExp.Gt(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.Null(v)) => true
  case (GExp.Eq(e1, e2), GExp.In(v, va)) => true
  case (GExp.Eq(e1, e2), GExp.Nor(v, va)) => true
  case (GExp.Gt(e1, e2), GExp.Bc(b2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Eq(e1, e2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Gt(e1, e2)) =>
    (less_aexpr(e1a, e1)) || ((AExp.equal_aexpa(e1a,
         e1)) && (less_aexpr(e2a, e2)))
  case (GExp.Gt(e1, e2), GExp.Null(v)) => true
  case (GExp.Gt(e1, e2), GExp.In(v, va)) => true
  case (GExp.Gt(e1, e2), GExp.Nor(v, va)) => true
  case (GExp.Null(v), GExp.Bc(b2)) => false
  case (GExp.Null(v), GExp.Eq(e1, e2)) => false
  case (GExp.Null(v), GExp.Gt(e1, e2)) => false
  case (GExp.Null(va), GExp.Null(v)) => less_aexp(va, v)
  case (GExp.Null(v), GExp.In(va, vb)) => true
  case (GExp.Null(v), GExp.Nor(va, vb)) => true
  case (GExp.In(vb, vc), GExp.Nor(v, va)) => true
  case (GExp.In(vb, vc), GExp.In(v, va)) =>
    (VName.less_vname(vb, v)) || ((VName.equal_vnamea(vb,
               v)) && (List_Lexorder.less_list[Value.value](vc, va)))
  case (GExp.In(vb, vc), GExp.Bc(v)) => false
  case (GExp.In(vb, vc), GExp.Eq(v, va)) => false
  case (GExp.In(vb, vc), GExp.Gt(v, va)) => false
  case (GExp.In(vb, vc), GExp.Null(v)) => false
  case (GExp.Nor(g1a, g2a), GExp.Nor(g1, g2)) =>
    (less_gexpr(g1a, g1)) || ((GExp.equal_gexpa(g1a,
         g1)) && (less_gexpr(g2a, g2)))
  case (GExp.Nor(g1, g2), GExp.Bc(v)) => false
  case (GExp.Nor(g1, g2), GExp.Eq(v, va)) => false
  case (GExp.Nor(g1, g2), GExp.Gt(v, va)) => false
  case (GExp.Nor(g1, g2), GExp.Null(v)) => false
  case (GExp.Nor(g1, g2), GExp.In(v, va)) => false
}

def less_eq_gexp(e1: GExp.gexp, e2: GExp.gexp): Boolean =
  (less_gexpr(e1, e2)) || (GExp.equal_gexpa(e1, e2))

def less_gexp(e1: GExp.gexp, e2: GExp.gexp): Boolean = less_gexpr(e1, e2)

} /* object GExp_Orderings */

object Transition {

abstract sealed class transition_ext[A]
final case class
  transition_exta[A](a: String, b: Nat.nat, c: List[GExp.gexp],
                      d: List[AExp.aexp], e: List[(Nat.nat, AExp.aexp)], f: A)
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
                                     arity)) && ((Lista.equal_lista[GExp.gexp](guarda,
guard)) && ((Lista.equal_lista[AExp.aexp](outputsa,
   outputs)) && ((Lista.equal_lista[(Nat.nat,
                                      AExp.aexp)](updatesa,
           updates)) && (HOL.eq[A](morea, more))))))
}

def Updates[A](x0: transition_ext[A]): List[(Nat.nat, AExp.aexp)] = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => updates
}

def Outputs[A](x0: transition_ext[A]): List[AExp.aexp] = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => outputs
}

def Guard[A](x0: transition_ext[A]): List[GExp.gexp] = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => guard
}

def enumerate_registers(t: transition_ext[Unit]): Set.set[Nat.nat] =
  Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[GExp.gexp,
                  Set.set[Nat.nat]](((a: GExp.gexp) =>
                                      GExp.enumerate_gexp_regs(a)),
                                     Guard[Unit](t)))),
                          Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[AExp.aexp,
                   Set.set[Nat.nat]](((a: AExp.aexp) =>
                                       AExp.enumerate_aexp_regs(a)),
                                      Outputs[Unit](t))))),
     Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                                       AExp.aexp),
                                      Set.set[Nat.nat]](((a:
                    (Nat.nat, AExp.aexp))
                   =>
                  {
                    val (_, aa): (Nat.nat, AExp.aexp) = a;
                    AExp.enumerate_aexp_regs(aa)
                  }),
                 Updates[Unit](t))))),
                        Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                  AExp.aexp),
                 Set.set[Nat.nat]](((a: (Nat.nat, AExp.aexp)) =>
                                     {
                                       val (r, _): (Nat.nat, AExp.aexp) = a;
                                       AExp.enumerate_aexp_regs(AExp.V(VName.R(r)))
                                     }),
                                    Updates[Unit](t)))))

def max_reg(t: transition_ext[Unit]): Option[Nat.nat] =
  (if (Cardinality.eq_set[Nat.nat](enumerate_registers(t),
                                    Set.bot_set[Nat.nat]))
    None else Some[Nat.nat](Lattices_Big.Max[Nat.nat](enumerate_registers(t))))

def total_max_reg(t: transition_ext[Unit]): Nat.nat =
  (max_reg(t) match {
     case None => Nat.zero_nata
     case Some(a) => a
   })

def enumerate_ints(t: transition_ext[Unit]): Set.set[Int.int] =
  Set.sup_set[Int.int](Set.sup_set[Int.int](Set.sup_set[Int.int](Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[GExp.gexp,
                  Set.set[Int.int]](((a: GExp.gexp) =>
                                      GExp.enumerate_gexp_ints(a)),
                                     Guard[Unit](t)))),
                          Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[AExp.aexp,
                   Set.set[Int.int]](((a: AExp.aexp) =>
                                       AExp.enumerate_aexp_ints(a)),
                                      Outputs[Unit](t))))),
     Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[(Nat.nat,
                                       AExp.aexp),
                                      Set.set[Int.int]](((a:
                    (Nat.nat, AExp.aexp))
                   =>
                  {
                    val (_, aa): (Nat.nat, AExp.aexp) = a;
                    AExp.enumerate_aexp_ints(aa)
                  }),
                 Updates[Unit](t))))),
                        Complete_Lattices.Sup_set[Int.int](Set.seta[Set.set[Int.int]](Lista.map[(Nat.nat,
                  AExp.aexp),
                 Set.set[Int.int]](((a: (Nat.nat, AExp.aexp)) =>
                                     {
                                       val (r, _): (Nat.nat, AExp.aexp) = a;
                                       AExp.enumerate_aexp_ints(AExp.V(VName.R(r)))
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
  Arity[Unit](t2))) && (Lista.list_all[(GExp.gexp,
 GExp.gexp)](((a: (GExp.gexp, GExp.gexp)) =>
               {
                 val (aa, b): (GExp.gexp, GExp.gexp) = a;
                 GExp.gexp_same_structure(aa, b)
               }),
              ((Guard[Unit](t1)) zip (Guard[Unit](t2))))))

def more[A](x0: transition_ext[A]): A = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => more
}

def enumerate_inputs(t: transition_ext[Unit]): Set.set[Nat.nat] =
  Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[GExp.gexp,
                                     Set.set[Nat.nat]](((a: GExp.gexp) =>
                 GExp.enumerate_gexp_inputs(a)),
                Guard[Unit](t)))),
     Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[AExp.aexp,
                                      Set.set[Nat.nat]](((a: AExp.aexp) =>
                  AExp.enumerate_aexp_inputs(a)),
                 Outputs[Unit](t))))),
                        Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(Nat.nat,
                  AExp.aexp),
                 Set.set[Nat.nat]](((a: (Nat.nat, AExp.aexp)) =>
                                     {
                                       val (_, aa): (Nat.nat, AExp.aexp) = a;
                                       AExp.enumerate_aexp_inputs(aa)
                                     }),
                                    Updates[Unit](t)))))

} /* object Transition */

object Transition_Ordering {

def less_transition_ext[A : Orderings.linorder](t1:
          Transition.transition_ext[A],
         t2: Transition.transition_ext[A]):
      Boolean
  =
  (if (Transition.Label[A](t1) == Transition.Label[A](t2))
    (if (Nat.equal_nata(Transition.Arity[A](t1), Transition.Arity[A](t2)))
      (if (Lista.equal_lista[GExp.gexp](Transition.Guard[A](t1),
 Transition.Guard[A](t2)))
        (if (Lista.equal_lista[AExp.aexp](Transition.Outputs[A](t1),
   Transition.Outputs[A](t2)))
          (if (Lista.equal_lista[(Nat.nat,
                                   AExp.aexp)](Transition.Updates[A](t1),
        Transition.Updates[A](t2)))
            Orderings.less[A](Transition.more[A](t1), Transition.more[A](t2))
            else List_Lexorder.less_list[(Nat.nat,
   AExp.aexp)](Transition.Updates[A](t1), Transition.Updates[A](t2)))
          else List_Lexorder.less_list[AExp.aexp](Transition.Outputs[A](t1),
           Transition.Outputs[A](t2)))
        else List_Lexorder.less_list[GExp.gexp](Transition.Guard[A](t1),
         Transition.Guard[A](t2)))
      else Nat.less_nat(Transition.Arity[A](t1), Transition.Arity[A](t2)))
    else Transition.Label[A](t1) < Transition.Label[A](t2))

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

def size_fset[A : HOL.equal](x0: fset[A]): Nat.nat = x0 match {
  case fset_of_list(as) => Nat.Nata((as.distinct).length)
}

def fBall[A](x0: fset[A], f: A => Boolean): Boolean = (x0, f) match {
  case (fset_of_list(l), f) => Lista.list_all[A](f, l)
}

def equal_fseta[A : HOL.equal](x: fset[A], xa1: fset[A]): Boolean = (x, xa1)
  match {
  case (x, fset_of_list(y)) =>
    (Nat.equal_nata(size_fset[A](x),
                     Nat.Nata((y.distinct).length))) && (fBall[A](x,
                           ((a: A) => y contains a)))
}

def fBex[A](x0: fset[A], f: A => Boolean): Boolean = (x0, f) match {
  case (fset_of_list(l), f) => Lista.list_ex[A](f, l)
}

def fimage[A, B : HOL.equal](f: A => B, x1: fset[A]): fset[B] = (f, x1) match {
  case (f, fset_of_list(as)) =>
    fset_of_list[B]((Lista.map[A, B](f, as)).distinct)
}

def sup_fset[A : HOL.equal](x0: fset[A], x1: fset[A]): fset[A] = (x0, x1) match
  {
  case (fset_of_list(f1), fset_of_list(f2)) =>
    fset_of_list[A]((f1 ++ f2).distinct)
}

def bot_fset[A]: fset[A] = fset_of_list[A](Nil)

def ffUnion[A : HOL.equal](x0: fset[fset[A]]): fset[A] = x0 match {
  case fset_of_list(as) =>
    Lista.fold[fset[A],
                fset[A]](((a: fset[A]) => (b: fset[A]) => sup_fset[A](a, b)),
                          as, bot_fset[A])
}

def ffilter[A : HOL.equal](f: A => Boolean, x1: fset[A]): fset[A] = (f, x1)
  match {
  case (f, fset_of_list(as)) =>
    fset_of_list[A]((Lista.filter[A](f, as)).distinct)
}

def finsert[A : HOL.equal](a: A, x1: fset[A]): fset[A] = (a, x1) match {
  case (a, fset_of_list(as)) => fset_of_list[A](Lista.insert[A](a, as))
}

def fmember[A : HOL.equal](a: A, x1: fset[A]): Boolean = (a, x1) match {
  case (a, fset_of_list(as)) => as contains a
}

def fset[A : HOL.equal](x0: fset[A]): Set.set[A] = x0 match {
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

def sorted_list_of_fset[A : HOL.equal : Orderings.linorder](x0: fset[A]):
      List[A]
  =
  x0 match {
  case fset_of_list(l) => (l.distinct).sortWith((Orderings.less))
}

def less_eq_fset[A : HOL.equal](x0: fset[A], a: fset[A]): Boolean = (x0, a)
  match {
  case (fset_of_list(l), a) =>
    Lista.list_all[A](((x: A) => fmember[A](x, a)), l)
}

def less_fset[A : HOL.equal](sa: fset[A], s: fset[A]): Boolean =
  (less_eq_fset[A](sa, s)) && (Nat.less_nat(size_fset[A](sa), size_fset[A](s)))

} /* object FSet */

object FSet_Utils {

def fSum[A : Groups.comm_monoid_add : HOL.equal](x0: FSet.fset[A]): A = x0 match
  {
  case FSet.fset_of_list(l) =>
    Lista.fold[A, A](((a: A) => (b: A) => Groups.plus[A](a, b)), l.distinct,
                      Groups.zero[A])
}

def fprod[A : HOL.equal, B : HOL.equal](x0: FSet.fset[A], x1: FSet.fset[B]):
      FSet.fset[(A, B)]
  =
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

def fis_singleton[A : HOL.equal](s: FSet.fset[A]): Boolean =
  Nat.equal_nata(FSet.size_fset[A](s), Nat.Nata((1)))

} /* object FSet_Utils */

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

object Least_Upper_Bound {

def all_literal_args[A](t: Transition.transition_ext[A]): Boolean =
  Lista.list_all[GExp.gexp](((a: GExp.gexp) => Inference.literal_args(a)),
                             Transition.Guard[A](t))

def merge_in_in(v: VName.vname, l: List[Value.value], x2: List[GExp.gexp]):
      List[GExp.gexp]
  =
  (v, l, x2) match {
  case (v, l, Nil) => List(GExp.In(v, l))
  case (va, la, GExp.Eq(AExp.V(v), AExp.L(l)) :: t) =>
    (if (VName.equal_vnamea(va, v))
      GExp.In(va, Lista.insert[Value.value](l, la)) :: t
      else GExp.Eq(AExp.V(v), AExp.L(l)) :: merge_in_in(va, la, t))
  case (va, la, GExp.In(v, l) :: t) =>
    (if (VName.equal_vnamea(va, v))
      GExp.In(va, Lista.union[Value.value].apply(la).apply(l)) :: t
      else GExp.In(v, l) :: merge_in_in(va, la, t))
  case (v, l, GExp.Bc(va) :: t) => GExp.Bc(va) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(AExp.L(vc), vb) :: t) =>
    GExp.Eq(AExp.L(vc), vb) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(AExp.Plus(vc, vd), vb) :: t) =>
    GExp.Eq(AExp.Plus(vc, vd), vb) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(AExp.Minus(vc, vd), vb) :: t) =>
    GExp.Eq(AExp.Minus(vc, vd), vb) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(va, AExp.V(vc)) :: t) =>
    GExp.Eq(va, AExp.V(vc)) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Plus(vc, vd)) :: t) =>
    GExp.Eq(va, AExp.Plus(vc, vd)) :: merge_in_in(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Minus(vc, vd)) :: t) =>
    GExp.Eq(va, AExp.Minus(vc, vd)) :: merge_in_in(v, l, t)
  case (v, l, GExp.Gt(va, vb) :: t) => GExp.Gt(va, vb) :: merge_in_in(v, l, t)
  case (v, l, GExp.Null(va) :: t) => GExp.Null(va) :: merge_in_in(v, l, t)
  case (v, l, GExp.Nor(va, vb) :: t) => GExp.Nor(va, vb) :: merge_in_in(v, l, t)
}

def merge_in_eq(v: VName.vname, l: Value.value, x2: List[GExp.gexp]):
      List[GExp.gexp]
  =
  (v, l, x2) match {
  case (v, l, Nil) => List(GExp.Eq(AExp.V(v), AExp.L(l)))
  case (va, la, GExp.Eq(AExp.V(v), AExp.L(l)) :: t) =>
    (if ((VName.equal_vnamea(va, v)) && (! (Value.equal_valuea(la, l))))
      GExp.In(va, List(la, l)) :: t
      else GExp.Eq(AExp.V(v), AExp.L(l)) :: merge_in_eq(va, la, t))
  case (va, la, GExp.In(v, l) :: t) =>
    (if (VName.equal_vnamea(va, v)) GExp.In(va, (la :: l).distinct) :: t
      else GExp.In(v, l) :: merge_in_eq(va, la, t))
  case (v, l, GExp.Bc(va) :: t) => GExp.Bc(va) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(AExp.L(vc), vb) :: t) =>
    GExp.Eq(AExp.L(vc), vb) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(AExp.Plus(vc, vd), vb) :: t) =>
    GExp.Eq(AExp.Plus(vc, vd), vb) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(AExp.Minus(vc, vd), vb) :: t) =>
    GExp.Eq(AExp.Minus(vc, vd), vb) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(va, AExp.V(vc)) :: t) =>
    GExp.Eq(va, AExp.V(vc)) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Plus(vc, vd)) :: t) =>
    GExp.Eq(va, AExp.Plus(vc, vd)) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Eq(va, AExp.Minus(vc, vd)) :: t) =>
    GExp.Eq(va, AExp.Minus(vc, vd)) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Gt(va, vb) :: t) => GExp.Gt(va, vb) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Null(va) :: t) => GExp.Null(va) :: merge_in_eq(v, l, t)
  case (v, l, GExp.Nor(va, vb) :: t) => GExp.Nor(va, vb) :: merge_in_eq(v, l, t)
}

def merge_guards(x0: List[GExp.gexp], g2: List[GExp.gexp]): List[GExp.gexp] =
  (x0, g2) match {
  case (Nil, g2) => g2
  case (GExp.Eq(AExp.V(v), AExp.L(l)) :: t, g2) =>
    merge_guards(t, merge_in_eq(v, l, g2))
  case (GExp.In(v, l) :: t, g2) => merge_guards(t, merge_in_in(v, l, g2))
  case (GExp.Bc(v) :: t, g2) => GExp.Bc(v) :: merge_guards(t, g2)
  case (GExp.Eq(AExp.L(vb), va) :: t, g2) =>
    GExp.Eq(AExp.L(vb), va) :: merge_guards(t, g2)
  case (GExp.Eq(AExp.Plus(vb, vc), va) :: t, g2) =>
    GExp.Eq(AExp.Plus(vb, vc), va) :: merge_guards(t, g2)
  case (GExp.Eq(AExp.Minus(vb, vc), va) :: t, g2) =>
    GExp.Eq(AExp.Minus(vb, vc), va) :: merge_guards(t, g2)
  case (GExp.Eq(v, AExp.V(vb)) :: t, g2) =>
    GExp.Eq(v, AExp.V(vb)) :: merge_guards(t, g2)
  case (GExp.Eq(v, AExp.Plus(vb, vc)) :: t, g2) =>
    GExp.Eq(v, AExp.Plus(vb, vc)) :: merge_guards(t, g2)
  case (GExp.Eq(v, AExp.Minus(vb, vc)) :: t, g2) =>
    GExp.Eq(v, AExp.Minus(vb, vc)) :: merge_guards(t, g2)
  case (GExp.Gt(v, va) :: t, g2) => GExp.Gt(v, va) :: merge_guards(t, g2)
  case (GExp.Null(v) :: t, g2) => GExp.Null(v) :: merge_guards(t, g2)
  case (GExp.Nor(v, va) :: t, g2) => GExp.Nor(v, va) :: merge_guards(t, g2)
}

def is_In(x0: GExp.gexp): Boolean = x0 match {
  case GExp.In(uu, uv) => true
  case GExp.Bc(v) => false
  case GExp.Eq(v, va) => false
  case GExp.Gt(v, va) => false
  case GExp.Null(v) => false
  case GExp.Nor(v, va) => false
}

def gob_aux(t1: Transition.transition_ext[Unit],
             t2: Transition.transition_ext[Unit]):
      Option[Transition.transition_ext[Unit]]
  =
  (if ((Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](t1),
                                      Transition.Outputs[Unit](t2))) && ((Lista.equal_lista[(Nat.nat,
              AExp.aexp)](Transition.Updates[Unit](t1),
                           Transition.Updates[Unit](t2))) && ((all_literal_args[Unit](t1)) && (all_literal_args[Unit](t2)))))
    Some[Transition.transition_ext[Unit]](Transition.transition_exta[Unit](Transition.Label[Unit](t1),
                                    Transition.Arity[Unit](t1),
                                    (Lista.filter[GExp.gexp](Fun.comp[Boolean,
                               Boolean,
                               GExp.gexp](((a: Boolean) => ! a),
   ((a: GExp.gexp) => is_In(a))),
                      merge_guards(Transition.Guard[Unit](t1),
                                    Transition.Guard[Unit](t2)))).distinct,
                                    Transition.Outputs[Unit](t1),
                                    Transition.Updates[Unit](t1), ()))
    else None)

def gob(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
         newa: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))],
         old: FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
         uu: (FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]) =>
               FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             ((Transition.transition_ext[Unit], Nat.nat),
                               (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID);
    (gob_aux(t1, t2) match {
       case None => None
       case Some(gob_t) =>
         Some[FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](Inference.replace(Inference.drop_transitions(newa,
                              FSet.finsert[Nat.nat](t2ID,
             FSet.bot_fset[Nat.nat])),
   t1ID, gob_t))
     })
  }

def lob_aux(t1: Transition.transition_ext[Unit],
             t2: Transition.transition_ext[Unit]):
      Option[Transition.transition_ext[Unit]]
  =
  (if ((Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](t1),
                                      Transition.Outputs[Unit](t2))) && ((Lista.equal_lista[(Nat.nat,
              AExp.aexp)](Transition.Updates[Unit](t1),
                           Transition.Updates[Unit](t2))) && ((all_literal_args[Unit](t1)) && (all_literal_args[Unit](t2)))))
    Some[Transition.transition_ext[Unit]](Transition.transition_exta[Unit](Transition.Label[Unit](t1),
                                    Transition.Arity[Unit](t1),
                                    (merge_guards(Transition.Guard[Unit](t1),
           Transition.Guard[Unit](t2))).distinct,
                                    Transition.Outputs[Unit](t1),
                                    Transition.Updates[Unit](t1), ()))
    else None)

def lob(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
         newa: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))],
         old: FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
         uu: (FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]) =>
               FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             ((Transition.transition_ext[Unit], Nat.nat),
                               (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID);
    (lob_aux(t1, t2) match {
       case None => None
       case Some(lob_t) =>
         Some[FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](Inference.replace(Inference.drop_transitions(newa,
                              FSet.finsert[Nat.nat](t2ID,
             FSet.bot_fset[Nat.nat])),
   t1ID, lob_t))
     })
  }

def these[A](as: List[Option[A]]): List[A] =
  Lista.map_filter[Option[A],
                    A](((x: Option[A]) =>
                         (if (! (Optiona.is_none[A](x)))
                           Some[A]({
                                     val (Some(y)): Option[A] = x;
                                     y
                                   })
                           else None)),
                        as)

def get_in(x0: GExp.gexp): Option[(VName.vname, List[Value.value])] = x0 match {
  case GExp.In(v, s) => Some[(VName.vname, List[Value.value])]((v, s))
  case GExp.Bc(v) => None
  case GExp.Eq(v, va) => None
  case GExp.Gt(v, va) => None
  case GExp.Null(v) => None
  case GExp.Nor(v, va) => None
}

def has_corresponding(g: GExp.gexp, x1: List[GExp.gexp]): Boolean = (g, x1)
  match {
  case (g, Nil) => false
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.Eq(AExp.V(v), AExp.L(l)) :: t) =>
    (if ((VName.equal_vnamea(va, v)) && (Value.equal_valuea(la, l))) true
      else has_corresponding(GExp.Eq(AExp.V(va), AExp.L(la)), t))
  case (GExp.In(va, la), GExp.Eq(AExp.V(v), AExp.L(l)) :: t) =>
    (if ((VName.equal_vnamea(v, va)) && (la contains l)) true
      else has_corresponding(GExp.In(va, la), t))
  case (GExp.In(va, la), GExp.In(v, l) :: t) =>
    (if ((VName.equal_vnamea(va, v)) && (Lista.list_all[Value.value](((a:
                                 Value.value)
                                =>
                               la contains a),
                              l)))
      true else has_corresponding(GExp.In(va, la), t))
  case (GExp.Bc(v), h :: t) => has_corresponding(GExp.Bc(v), t)
  case (GExp.Eq(AExp.L(vb), va), h :: t) =>
    has_corresponding(GExp.Eq(AExp.L(vb), va), t)
  case (GExp.Eq(AExp.Plus(vb, vc), va), h :: t) =>
    has_corresponding(GExp.Eq(AExp.Plus(vb, vc), va), t)
  case (GExp.Eq(AExp.Minus(vb, vc), va), h :: t) =>
    has_corresponding(GExp.Eq(AExp.Minus(vb, vc), va), t)
  case (GExp.Eq(v, AExp.V(vb)), h :: t) =>
    has_corresponding(GExp.Eq(v, AExp.V(vb)), t)
  case (GExp.Eq(v, AExp.Plus(vb, vc)), h :: t) =>
    has_corresponding(GExp.Eq(v, AExp.Plus(vb, vc)), t)
  case (GExp.Eq(v, AExp.Minus(vb, vc)), h :: t) =>
    has_corresponding(GExp.Eq(v, AExp.Minus(vb, vc)), t)
  case (GExp.Gt(v, va), h :: t) => has_corresponding(GExp.Gt(v, va), t)
  case (GExp.Null(v), h :: t) => has_corresponding(GExp.Null(v), t)
  case (GExp.In(v, va), GExp.Bc(vb) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Eq(AExp.L(vd), vc) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Eq(AExp.Plus(vd, ve), vc) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Eq(AExp.Minus(vd, ve), vc) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Eq(vb, AExp.V(vd)) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Plus(vd, ve)) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Minus(vd, ve)) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Gt(vb, vc) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Null(vb) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.In(v, va), GExp.Nor(vb, vc) :: t) =>
    has_corresponding(GExp.In(v, va), t)
  case (GExp.Nor(v, va), h :: t) => has_corresponding(GExp.Nor(v, va), t)
  case (g, GExp.Bc(v) :: t) => has_corresponding(g, t)
  case (g, GExp.Eq(AExp.L(vb), va) :: t) => has_corresponding(g, t)
  case (g, GExp.Eq(AExp.Plus(vb, vc), va) :: t) => has_corresponding(g, t)
  case (g, GExp.Eq(AExp.Minus(vb, vc), va) :: t) => has_corresponding(g, t)
  case (g, GExp.Eq(v, AExp.V(vb)) :: t) => has_corresponding(g, t)
  case (g, GExp.Eq(v, AExp.Plus(vb, vc)) :: t) => has_corresponding(g, t)
  case (g, GExp.Eq(v, AExp.Minus(vb, vc)) :: t) => has_corresponding(g, t)
  case (g, GExp.Gt(v, va) :: t) => has_corresponding(g, t)
  case (g, GExp.Null(v) :: t) => has_corresponding(g, t)
  case (GExp.Eq(vb, vc), GExp.In(v, va) :: t) =>
    has_corresponding(GExp.Eq(vb, vc), t)
  case (g, GExp.Nor(v, va) :: t) => has_corresponding(g, t)
}

def is_lob[A, B](t1: Transition.transition_ext[A],
                  t2: Transition.transition_ext[B]):
      Boolean
  =
  (Transition.Label[A](t1) ==
    Transition.Label[B](t2)) && ((Nat.equal_nata(Transition.Arity[A](t1),
          Transition.Arity[B](t2))) && ((Lista.equal_lista[AExp.aexp](Transition.Outputs[A](t1),
                               Transition.Outputs[B](t2))) && ((Lista.equal_lista[(Nat.nat,
    AExp.aexp)](Transition.Updates[A](t1),
                 Transition.Updates[B](t2))) && (Lista.list_all[GExp.gexp](((g:
                                       GExp.gexp)
                                      =>
                                     has_corresponding(g,
                Transition.Guard[A](t1))),
                                    Transition.Guard[B](t2))))))

def get_Ins(g: List[GExp.gexp]): List[(Nat.nat, List[Value.value])] =
  Lista.map_filter[GExp.gexp,
                    (Nat.nat,
                      List[Value.value])](((x: GExp.gexp) =>
    (if ((x match {
            case GExp.Bc(_) => false
            case GExp.Eq(_, _) => false
            case GExp.Gt(_, _) => false
            case GExp.Null(_) => false
            case GExp.In(VName.I(_), _) => true
            case GExp.In(VName.R(_), _) => false
            case GExp.Nor(_, _) => false
          }))
      Some[(Nat.nat,
             List[Value.value])]({
                                   val (GExp.In(VName.I(v), l)): GExp.gexp = x;
                                   (v, l)
                                 })
      else None)),
   g)

def get_ins(g: List[GExp.gexp]): List[(Nat.nat, List[Value.value])] =
  Lista.map_filter[(VName.vname, List[Value.value]),
                    (Nat.nat,
                      List[Value.value])](((x: (VName.vname, List[Value.value]))
     =>
    (if ((x match {
            case (VName.I(_), _) => true
            case (VName.R(_), _) => false
          }))
      Some[(Nat.nat,
             List[Value.value])]({
                                   val (VName.I(i), s):
 (VName.vname, List[Value.value])
                                     = x;
                                   (i, s)
                                 })
      else None)),
   these[(VName.vname,
           List[Value.value])](Lista.map[GExp.gexp,
  Option[(VName.vname, List[Value.value])]](((a: GExp.gexp) => get_in(a)), g)))

def gung_ho_aux(t1: Transition.transition_ext[Unit],
                 t2: Transition.transition_ext[Unit]):
      Option[Transition.transition_ext[Unit]]
  =
  (if ((Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](t1),
                                      Transition.Outputs[Unit](t2))) && ((Lista.equal_lista[(Nat.nat,
              AExp.aexp)](Transition.Updates[Unit](t1),
                           Transition.Updates[Unit](t2))) && ((all_literal_args[Unit](t1)) && (all_literal_args[Unit](t2)))))
    Some[Transition.transition_ext[Unit]](Transition.transition_exta[Unit](Transition.Label[Unit](t1),
                                    Transition.Arity[Unit](t1), Nil,
                                    Transition.Outputs[Unit](t1),
                                    Transition.Updates[Unit](t1), ()))
    else None)

def gung_ho(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
             newa: FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
             old: FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
             uu: (FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                   FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 ((Transition.transition_ext[Unit], Nat.nat),
                                   (Transition.transition_ext[Unit],
                                     Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID);
    (gung_ho_aux(t1, t2) match {
       case None => None
       case Some(gob_t) =>
         Some[FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](Inference.replace(Inference.drop_transitions(newa,
                              FSet.finsert[Nat.nat](t2ID,
             FSet.bot_fset[Nat.nat])),
   t1ID, gob_t))
     })
  }

def is_lit_eq(x0: GExp.gexp, i: Nat.nat): Boolean = (x0, i) match {
  case (GExp.Eq(AExp.V(VName.I(ia)), AExp.L(v)), i) => Nat.equal_nata(ia, i)
  case (GExp.Bc(v), uv) => false
  case (GExp.Eq(AExp.L(vb), va), uv) => false
  case (GExp.Eq(AExp.V(VName.R(vc)), va), uv) => false
  case (GExp.Eq(AExp.Plus(vb, vc), va), uv) => false
  case (GExp.Eq(AExp.Minus(vb, vc), va), uv) => false
  case (GExp.Eq(v, AExp.V(vb)), uv) => false
  case (GExp.Eq(v, AExp.Plus(vb, vc)), uv) => false
  case (GExp.Eq(v, AExp.Minus(vb, vc)), uv) => false
  case (GExp.Gt(v, va), uv) => false
  case (GExp.Null(v), uv) => false
  case (GExp.In(v, va), uv) => false
  case (GExp.Nor(v, va), uv) => false
}

def is_input_in(x0: GExp.gexp): Boolean = x0 match {
  case GExp.In(VName.I(i), s) => ! (s.isEmpty)
  case GExp.Bc(v) => false
  case GExp.Eq(v, va) => false
  case GExp.Gt(v, va) => false
  case GExp.Null(v) => false
  case GExp.In(VName.R(vb), va) => false
  case GExp.Nor(v, va) => false
}

def is_lit_eq_general(x0: GExp.gexp): Boolean = x0 match {
  case GExp.Eq(AExp.V(VName.I(uu)), AExp.L(uv)) => true
  case GExp.Bc(v) => false
  case GExp.Eq(AExp.L(vb), va) => false
  case GExp.Eq(AExp.V(VName.R(vc)), va) => false
  case GExp.Eq(AExp.Plus(vb, vc), va) => false
  case GExp.Eq(AExp.Minus(vb, vc), va) => false
  case GExp.Eq(v, AExp.V(vb)) => false
  case GExp.Eq(v, AExp.Plus(vb, vc)) => false
  case GExp.Eq(v, AExp.Minus(vb, vc)) => false
  case GExp.Gt(v, va) => false
  case GExp.Null(v) => false
  case GExp.In(v, va) => false
  case GExp.Nor(v, va) => false
}

def opposite_gob(t1: Transition.transition_ext[Unit],
                  t2: Transition.transition_ext[Unit]):
      Boolean
  =
  (Lista.list_all[GExp.gexp](((g: GExp.gexp) =>
                               (is_lit_eq_general(g)) || (is_input_in(g))),
                              Transition.Guard[Unit](t1))) && ((Lista.list_all[GExp.gexp](((g:
              GExp.gexp)
             =>
            (is_lit_eq_general(g)) || (is_input_in(g))),
           Transition.Guard[Unit](t2))) && ((Set.Bex[Nat.nat](Set.sup_set[Nat.nat](Transition.enumerate_inputs(t1),
    Transition.enumerate_inputs(t2)),
                       ((i: Nat.nat) =>
                         (Lista.list_ex[GExp.gexp](((g: GExp.gexp) =>
             is_lit_eq(g, i)),
            Transition.Guard[Unit](t1))) && (Lista.list_all[GExp.gexp](((g:
                                   GExp.gexp)
                                  =>
                                 ! (GExp.gexp_constrains(g,
                  AExp.V(VName.I(i))))),
                                Transition.Guard[Unit](t2)))))) && ((Nat.equal_nata(Transition.Arity[Unit](t1),
     Transition.Arity[Unit](t2))) && ((Set.Ball[Nat.nat](Transition.enumerate_inputs(t2),
                  ((i: Nat.nat) =>
                    Nat.less_nat(i, Transition.Arity[Unit](t2))))) && (Set.Ball[Nat.nat](Transition.enumerate_inputs(t2),
          ((i: Nat.nat) =>
            Nat.less_eq_nat(Nat.Nata((Lista.filter[GExp.gexp](((g: GExp.gexp) =>
                        GExp.gexp_constrains(g, AExp.V(VName.I(i)))),
                       Transition.Guard[Unit](t2))).length),
                             Nat.Nata((1))))))))))

def in_not_subset[A, B](t1: Transition.transition_ext[A],
                         t2: Transition.transition_ext[B]):
      Boolean
  =
  (Transition.Label[A](t1) ==
    Transition.Label[B](t2)) && ((Nat.equal_nata(Transition.Arity[A](t1),
          Transition.Arity[B](t2))) && ((Optiona.is_none[Nat.nat](GExp.max_reg_list(Transition.Guard[B](t2)))) && ((Option_Lexorder.less_option[Nat.nat](GExp.max_input_list(Transition.Guard[B](t2)),
                                  Some[Nat.nat](Transition.Arity[B](t2)))) && ((Inference.satisfiable_list(Inference.smart_not_null(Lista.upt(Nat.zero_nata,
                       Transition.Arity[B](t2)),
             Transition.Guard[B](t2)))) && (Lista.list_ex[(Nat.nat,
                    List[Value.value])](((a: (Nat.nat, List[Value.value])) =>
  {
    val (i, s1): (Nat.nat, List[Value.value]) = a;
    Lista.list_ex[(Nat.nat,
                    List[Value.value])](((aa: (Nat.nat, List[Value.value])) =>
  {
    val (ia, s2): (Nat.nat, List[Value.value]) = aa;
    (Nat.equal_nata(i, ia)) && ((! (Lista.list_all[Value.value](((ab:
                            Value.value)
                           =>
                          s1 contains ab),
                         s2))) && (GExp.restricted_once(VName.I(i),
                 Transition.Guard[B](t2))))
  }),
 get_ins(Transition.Guard[B](t2)))
  }),
 get_ins(Transition.Guard[A](t1))))))))

def lob_distinguished_2[A, B](t1: Transition.transition_ext[A],
                               t2: Transition.transition_ext[B]):
      Boolean
  =
  Lista.list_ex[(Nat.nat,
                  List[Value.value])](((a: (Nat.nat, List[Value.value])) =>
{
  val (i, l): (Nat.nat, List[Value.value]) = a;
  (Lista.equal_lista[GExp.gexp](Lista.filter[GExp.gexp](((g: GExp.gexp) =>
                  GExp.gexp_constrains(g, AExp.V(VName.I(i)))),
                 Transition.Guard[B](t2)),
                                 List(GExp.In(VName.I(i),
       l)))) && ((Lista.list_ex[Value.value](((la: Value.value) =>
       (Nat.less_nat(i, Transition.Arity[A](t1))) && (((Transition.Guard[A](t1)) contains (GExp.Eq(AExp.V(VName.I(i)),
                    AExp.L(la)))) && (Nat.less_nat(Nat.Nata((1)),
            FSet.size_fset[Value.value](FSet.fset_of_list[Value.value](l)))))),
      l)) && (Nat.equal_nata(Transition.Arity[A](t1), Transition.Arity[B](t2))))
}),
                                       get_Ins(Transition.Guard[B](t2)))

def lob_distinguished_3[A, B](t1: Transition.transition_ext[A],
                               t2: Transition.transition_ext[B]):
      Boolean
  =
  Lista.list_ex[(Nat.nat,
                  List[Value.value])](((a: (Nat.nat, List[Value.value])) =>
{
  val (i, l): (Nat.nat, List[Value.value]) = a;
  (Lista.equal_lista[GExp.gexp](Lista.filter[GExp.gexp](((g: GExp.gexp) =>
                  GExp.gexp_constrains(g, AExp.V(VName.I(i)))),
                 Transition.Guard[B](t2)),
                                 List(GExp.In(VName.I(i),
       l)))) && ((Lista.list_ex[(Nat.nat,
                                  List[Value.value])](((aa:
                  (Nat.nat, List[Value.value]))
                 =>
                {
                  val (ia, la): (Nat.nat, List[Value.value]) = aa;
                  (Nat.equal_nata(i, ia)) && (Set.less_set[Value.value](Set.seta[Value.value](la),
                                 Set.seta[Value.value](l)))
                }),
               get_Ins(Transition.Guard[A](t1)))) && (Nat.equal_nata(Transition.Arity[A](t1),
                              Transition.Arity[B](t2))))
}),
                                       get_Ins(Transition.Guard[B](t2)))

} /* object Least_Upper_Bound */

object Ignore_Inputs {

def drop_guards(t: Transition.transition_ext[Unit]):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t), Nil,
                                    Transition.Outputs[Unit](t),
                                    Transition.Updates[Unit](t), ())

def enumerate_outputs(e: FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       l: String, a: Nat.nat):
      FSet.fset[List[AExp.aexp]]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               List[AExp.aexp]](((aa: (Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                                   =>
                                  {
                                    val (_, ab):
  (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                      = aa
                                    val (_, ac):
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                                      = ab;
                                    Transition.Outputs[Unit](ac)
                                  }),
                                 FSet.ffilter[(Nat.nat,
        ((Nat.nat, Nat.nat),
          Transition.transition_ext[Unit]))](((b:
         (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
        =>
       {
         val (_, (_, t)):
               (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
           = b;
         (Transition.Label[Unit](t) ==
           l) && (Nat.equal_nata(Transition.Arity[Unit](t), a))
       }),
      e))

def drop_inputs(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
                 newa: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                 old: FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                 np: (FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]) =>
                       FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     ((Transition.transition_ext[Unit],
Nat.nat),
                                       (Transition.transition_ext[Unit],
 Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID);
    Inference.get_by_id(newa, t2ID);
    (if (FSet_Utils.fis_singleton[List[AExp.aexp]](enumerate_outputs(newa,
                              Transition.Label[Unit](t1),
                              Transition.Arity[Unit](t1))))
      Some[FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](FSet.fimage[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])),
                                  (Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))](((a:
                                     (Nat.nat,
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit])))
                                    =>
                                   {
                                     val (id, (route, t)):
   (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                       = a;
                                     (if (Nat.equal_nata(id, t1ID))
                                       (id, (route, drop_guards(t)))
                                       else (id, (route, t)))
                                   }),
                                  FSet.ffilter[(Nat.nat,
         ((Nat.nat, Nat.nat),
           Transition.transition_ext[Unit]))](((a:
          (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
         =>
        {
          val (id, _):
                (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
            = a;
          ! (Nat.equal_nata(id, t2ID))
        }),
       newa)))
      else None)
  }

def statewise_drop_inputs(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
                           newa: FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                           old: FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                           np: (FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat),
       ((Transition.transition_ext[Unit], Nat.nat),
         (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID);
    Inference.get_by_id(newa, t2ID);
    (if (FSet.fBall[(Nat.nat,
                      (Transition.transition_ext[Unit],
                        Nat.nat))](Inference.outgoing_transitions(s, newa),
                                    ((a:
(Nat.nat, (Transition.transition_ext[Unit], Nat.nat)))
                                       =>
                                      {
val (_, (t, _)): (Nat.nat, (Transition.transition_ext[Unit], Nat.nat)) = a;
(if ((Transition.Label[Unit](t) ==
       Transition.Label[Unit](t1)) && (Nat.equal_nata(Transition.Arity[Unit](t),
               Transition.Arity[Unit](t1))))
  Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](t),
                                Transition.Outputs[Unit](t1))
  else true)
                                      })))
      Some[FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](Inference.replace(Inference.drop_transitions(newa,
                           FSet_Utils.fremove[Nat.nat](t1ID,
                FSet.fimage[(Nat.nat,
                              (Transition.transition_ext[Unit], Nat.nat)),
                             Nat.nat](Fun.comp[(Transition.transition_ext[Unit],
         Nat.nat),
        Nat.nat,
        (Nat.nat,
          (Transition.transition_ext[Unit],
            Nat.nat))](((a: (Transition.transition_ext[Unit], Nat.nat)) =>
                         a._2),
                        ((a: (Nat.nat,
                               (Transition.transition_ext[Unit], Nat.nat)))
                           =>
                          a._2)),
                                       Inference.outgoing_transitions(s,
                               newa)))),
t1ID, drop_guards(t1)))
      else None)
  }

def transitionwise_drop_inputs(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
                                newa: FSet.fset[(Nat.nat,
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                old: FSet.fset[(Nat.nat,
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                np: (FSet.fset[(Nat.nat,
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                      FSet.fset[(Nat.nat,
          ((Nat.nat, Nat.nat),
            ((Transition.transition_ext[Unit], Nat.nat),
              (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID);
    (if (Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](t1),
                                       Transition.Outputs[Unit](t2)))
      Some[FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](Inference.replace(Inference.drop_transition(newa,
                          t2ID),
t1ID, drop_guards(t1)))
      else None)
  }

} /* object Ignore_Inputs */

object Inference {

def S(m: FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[Nat.nat]
  =
  FSet.sup_fset[Nat.nat](FSet.fimage[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit])),
                                      Nat.nat](((a:
           (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
          =>
         {
           val (_, aa):
                 (Nat.nat,
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
                          FSet.fimage[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                                       Nat.nat](((a:
            (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
           =>
          {
            val (_, aa):
                  (Nat.nat,
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

def tm(t: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               ((Nat.nat, Nat.nat),
                 Transition.transition_ext[Unit])](((a:
               (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
              =>
             a._2),
            t)

def dest(uid: Nat.nat,
          t: FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  (((FSet.fthe_elem[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))](FSet.ffilter[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))](((x:
                                   (Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])))
                                  =>
                                 Nat.equal_nata(x._1, uid)),
                                t)))._2)._1)._2

def maxS(t: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]):
      Nat.nat
  =
  (if (FSet.equal_fseta[((Nat.nat, Nat.nat),
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

def infer:
      Nat.nat =>
        (FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
          (Nat.nat =>
            Nat.nat =>
              (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                Nat.nat) =>
            (Nat.nat =>
              Nat.nat =>
                Nat.nat =>
                  (FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]) =>
                    (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      ((FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
                        FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      ((Transition.transition_ext[Unit],
 Nat.nat),
(Transition.transition_ext[Unit], Nat.nat))))]) =>
                        Option[FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]) =>
              ((FSet.fset[((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])]) =>
                Boolean) =>
                ((FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit], Nat.nat),
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]
  =
  ((a: Nat.nat) =>
    (b: FSet.fset[(Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (c: Nat.nat =>
          Nat.nat =>
            (FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              Nat.nat)
      =>
    (d: Nat.nat =>
          Nat.nat =>
            Nat.nat =>
              (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                (FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]) =>
                  ((FSet.fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]) =>
                    FSet.fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  ((Transition.transition_ext[Unit], Nat.nat),
                                    (Transition.transition_ext[Unit],
                                      Nat.nat))))]) =>
                    Option[FSet.fset[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]])
      =>
    (e: (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
          Boolean)
      =>
    (f: (FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
          FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (Transition.transition_ext[Unit], Nat.nat))))])
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
          (if (Lista.equal_lista[Option[Value.value]](EFSM.apply_outputs(Transition.Outputs[Unit](ta),
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
                        (Lista.equal_lista[Option[Value.value]](EFSM.apply_outputs(Transition.Outputs[Unit](ta),
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

def toiEFSM_aux(uu: Nat.nat,
                 x1: List[((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])]):
      List[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (uu, x1) match {
  case (uu, Nil) => Nil
  case (n, h :: t) => (n, h) :: toiEFSM_aux(Nat.plus_nata(n, Nat.Nata((1))), t)
}

def toiEFSM(e: FSet.fset[((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit])]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fset_of_list[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))](toiEFSM_aux(Nat.zero_nata,
                                FSet.sorted_list_of_fset[((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit])](e)))

def learn(n: Nat.nat,
           pta: FSet.fset[((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])],
           l: List[List[(String, (List[Value.value], List[Value.value]))]],
           r: Nat.nat =>
                Nat.nat =>
                  (FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]) =>
                    Nat.nat,
           m: Nat.nat =>
                Nat.nat =>
                  Nat.nat =>
                    (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        ((FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], Nat.nat),
  (Transition.transition_ext[Unit], Nat.nat))))]) =>
                          Option[FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
           np: (FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]) =>
                 FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit], Nat.nat),
                                 (Transition.transition_ext[Unit],
                                   Nat.nat))))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
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
    tm(infer.apply(n).apply(toiEFSM(pta)).apply(r).apply(m).apply(check).apply(np))
  }

def directly_subsumes(m1: FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                       m2: FSet.fset[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))],
                       sa: Nat.nat, s: Nat.nat,
                       t1: Transition.transition_ext[Unit],
                       t2: Transition.transition_ext[Unit]):
      Boolean
  =
  Code_Generation.directly_subsumes_cases(m1, m2, sa, s, t1, t2)

def drop_transition(e: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                     t: Nat.nat):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, _):
                        (Nat.nat,
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a;
                  ! (Nat.equal_nata(uid, t))
                }),
               e)

def origin(uid: Nat.nat,
            t: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  (((FSet.fthe_elem[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))](FSet.ffilter[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))](((x:
                                   (Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])))
                                  =>
                                 Nat.equal_nata(x._1, uid)),
                                t)))._2)._1)._1

def merge_transitions(oldEFSM:
                        FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                       destMerge:
                         FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       t_1: Transition.transition_ext[Unit], u_1: Nat.nat,
                       t_2: Transition.transition_ext[Unit], u_2: Nat.nat,
                       modifier:
                         Nat.nat =>
                           Nat.nat =>
                             Nat.nat =>
                               (FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 (FSet.fset[(Nat.nat,
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                   ((FSet.fset[(Nat.nat,
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                     FSet.fset[(Nat.nat,
         ((Nat.nat, Nat.nat),
           ((Transition.transition_ext[Unit], Nat.nat),
             (Transition.transition_ext[Unit], Nat.nat))))]) =>
                                     Option[FSet.fset[(Nat.nat,
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                       np: (FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                             FSet.fset[(Nat.nat,
 ((Nat.nat, Nat.nat),
   ((Transition.transition_ext[Unit], Nat.nat),
     (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (directly_subsumes(oldEFSM, destMerge, origin(u_1, oldEFSM),
                          origin(u_1, destMerge), t_2, t_1))
    Some[FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit]))]](drop_transition(destMerge,
                                    u_1))
    else (if (directly_subsumes(oldEFSM, destMerge, origin(u_2, oldEFSM),
                                 origin(u_2, destMerge), t_1, t_2))
           Some[FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](drop_transition(destMerge,
   u_2))
           else (((((modifier(u_1))(u_2))(origin(u_1,
          destMerge)))(destMerge))(oldEFSM))(np)))

def make_distinct_aux(x0: List[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                       e: FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (x0, e) match {
  case (Nil, e) => e
  case (h :: t, e) =>
    (if (FSet.fmember[((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit])](h._2,
                   FSet.fimage[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])),
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])](((a:
                                (Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])))
                               =>
                              a._2),
                             e)))
      make_distinct_aux(t, e)
      else make_distinct_aux(t, FSet.finsert[(Nat.nat,
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](h, e)))
}

def make_distinct(e: Option[FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (e match {
     case None => None
     case Some(ea) =>
       Some[FSet.fset[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))]](make_distinct_aux(FSet.sorted_list_of_fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))](ea),
 FSet.bot_fset[(Nat.nat,
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]))
   })

def deterministic(t: FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                   np: (FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
                         FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       ((Transition.transition_ext[Unit],
  Nat.nat),
 (Transition.transition_ext[Unit], Nat.nat))))]):
      Boolean
  =
  FSet.equal_fseta[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       ((Transition.transition_ext[Unit], Nat.nat),
                         (Transition.transition_ext[Unit],
                           Nat.nat))))](np(t),
 FSet.bot_fset[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (Transition.transition_ext[Unit], Nat.nat))))])

def merge_states_aux(x: Nat.nat, y: Nat.nat,
                      t: FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (Nat.nat,
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, aa):
                        (Nat.nat,
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a
                  val (ab, b):
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                    = aa;
                  ({
                     val (origin, dest): (Nat.nat, Nat.nat) = ab;
                     ((ta: Transition.transition_ext[Unit]) =>
                       (uid, (((if (Nat.equal_nata(origin, x)) y else origin),
                                (if (Nat.equal_nata(dest, x)) y else dest)),
                               ta)))
                   })(b)
                }),
               t)

def merge_states(x: Nat.nat, y: Nat.nat,
                  t: FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (if (Nat.less_nat(y, x)) merge_states_aux(x, y, t)
    else merge_states_aux(y, x, t))

def resolve_nondeterminism(uu: List[(Nat.nat, Nat.nat)],
                            x1: List[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 ((Transition.transition_ext[Unit], Nat.nat),
   (Transition.transition_ext[Unit], Nat.nat))))],
                            uv: FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            newa: FSet.fset[(Nat.nat,
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            uw: Nat.nat =>
                                  Nat.nat =>
                                    Nat.nat =>
                                      (FSet.fset[(Nat.nat,
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
(FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
  ((FSet.fset[(Nat.nat,
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
    FSet.fset[(Nat.nat,
                ((Nat.nat, Nat.nat),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (Transition.transition_ext[Unit], Nat.nat))))]) =>
    Option[FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                            check:
                              (FSet.fset[((Nat.nat, Nat.nat),
   Transition.transition_ext[Unit])]) =>
                                Boolean,
                            np: (FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                  FSet.fset[(Nat.nat,
      ((Nat.nat, Nat.nat),
        ((Transition.transition_ext[Unit], Nat.nat),
          (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (uu, x1, uv, newa, uw, check, np) match {
  case (uu, Nil, uv, newa, uw, check, np) =>
    (if ((deterministic(newa, np)) && (check(tm(newa))))
      Some[FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](newa)
      else None)
  case (closed, (from, ((dest_1, dest_2), ((t_1, u_1), (t_2, u_2)))) :: ss,
         oldEFSM, newEFSM, m, check, np)
    => (if (closed contains (dest_1, dest_2)) None
         else {
                val destMerge:
                      FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]
                  = (if (Nat.equal_nata(dest_1, dest_2)) newEFSM
                      else merge_states(dest_1, dest_2, newEFSM));
                (make_distinct(merge_transitions(oldEFSM, destMerge, t_1, u_1,
          t_2, u_2, m, np))
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
 Nat.nat),
(Transition.transition_ext[Unit], Nat.nat))))]
                         = FSet.sorted_list_of_fset[(Nat.nat,
              ((Nat.nat, Nat.nat),
                ((Transition.transition_ext[Unit], Nat.nat),
                  (Transition.transition_ext[Unit], Nat.nat))))](np(newa));
                       (if (Nat.less_nat(Nat.plus_nata(Nat.plus_nata(Nat.Nata(newScores.length),
                              FSet.size_fset[(Nat.nat,
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](newa)),
                FSet.size_fset[Nat.nat](S(newa))),
  Nat.plus_nata(Nat.plus_nata(Nat.plus_nata(Nat.Nata(ss.length), Nat.Nata((1))),
                               FSet.size_fset[(Nat.nat,
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](newEFSM)),
                 FSet.size_fset[Nat.nat](S(newEFSM)))))
                         (resolve_nondeterminism(closed, newScores, oldEFSM,
          newa, m, check, np)
                            match {
                            case None =>
                              resolve_nondeterminism((dest_1, dest_2) :: closed,
              ss, oldEFSM, newEFSM, m, check, np)
                            case Some(a) =>
                              Some[FSet.fset[(Nat.nat,
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]](a)
                          })
                         else None)
                     }
                 })
              })
}

def merge(e: FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
           s_1: Nat.nat, s_2: Nat.nat,
           m: Nat.nat =>
                Nat.nat =>
                  Nat.nat =>
                    (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        ((FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], Nat.nat),
  (Transition.transition_ext[Unit], Nat.nat))))]) =>
                          Option[FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
           check:
             (FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit])]) =>
               Boolean,
           np: (FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]) =>
                 FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit], Nat.nat),
                                 (Transition.transition_ext[Unit],
                                   Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (Nat.equal_nata(s_1, s_2)) None
    else {
           val ea: FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]
             = merge_states(s_1, s_2, e);
           resolve_nondeterminism(Nil, FSet.sorted_list_of_fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            ((Transition.transition_ext[Unit], Nat.nat),
                              (Transition.transition_ext[Unit],
                                Nat.nat))))](np(ea)),
                                   e, ea, m, check, np)
         })

def outgoing_transitions(n: Nat.nat,
                          t: FSet.fset[(Nat.nat,
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat, (Transition.transition_ext[Unit], Nat.nat))]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (Nat.nat,
                 (Transition.transition_ext[Unit],
                   Nat.nat))](((a: (Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit])))
                                 =>
                                {
                                  val (uid, aa):
(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                    = a
                                  val (ab, b):
((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                                    = aa;
                                  ({
                                     val (_, to): (Nat.nat, Nat.nat) = ab;
                                     ((ta: Transition.transition_ext[Unit]) =>
                                       (to, (ta, uid)))
                                   })(b)
                                }),
                               FSet.ffilter[(Nat.nat,
      ((Nat.nat, Nat.nat),
        Transition.transition_ext[Unit]))](((a:
       (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
      =>
     {
       val (_, aa):
             (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
         = a
       val (ab, b): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = aa;
       ({
          val (origin, _): (Nat.nat, Nat.nat) = ab;
          ((_: Transition.transition_ext[Unit]) => Nat.equal_nata(origin, n))
        })(b)
     }),
    t))

def k_outgoing(m: Nat.nat,
                i: FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                s: Nat.nat):
      FSet.fset[(Nat.nat, (Transition.transition_ext[Unit], Nat.nat))]
  =
  (if (Nat.equal_nata(m, Nat.zero_nata)) outgoing_transitions(s, i)
    else {
           val outgoing:
                 FSet.fset[(Nat.nat,
                             (Transition.transition_ext[Unit], Nat.nat))]
             = outgoing_transitions(s, i)
           val others: FSet.fset[Nat.nat] =
             FSet.fimage[(Nat.nat, (Transition.transition_ext[Unit], Nat.nat)),
                          Nat.nat](((a: (Nat.nat,
  (Transition.transition_ext[Unit], Nat.nat)))
                                      =>
                                     a._1),
                                    outgoing);
           FSet.sup_fset[(Nat.nat,
                           (Transition.transition_ext[Unit],
                             Nat.nat))](outgoing,
 FSet.ffUnion[(Nat.nat,
                (Transition.transition_ext[Unit],
                  Nat.nat))](FSet.fimage[Nat.nat,
  FSet.fset[(Nat.nat,
              (Transition.transition_ext[Unit],
                Nat.nat))]](((a: Nat.nat) =>
                              k_outgoing(Nat.minus_nat(m, Nat.Nata((1))), i,
  a)),
                             others)))
         })

def k_score(n: Nat.nat,
             e: FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))],
             rank: Nat.nat =>
                     Nat.nat =>
                       (FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
                         Nat.nat):
      FSet.fset[(Nat.nat, (Nat.nat, Nat.nat))]
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
    val a: FSet.fset[(Nat.nat, (Nat.nat, Nat.nat))] =
      FSet.fimage[(Nat.nat, Nat.nat),
                   (Nat.nat,
                     (Nat.nat,
                       Nat.nat))](((a: (Nat.nat, Nat.nat)) =>
                                    {
                                      val (s1, s2): (Nat.nat, Nat.nat) = a
                                      val outgoing_s1: FSet.fset[Nat.nat] =
FSet.fimage[(Nat.nat, (Transition.transition_ext[Unit], Nat.nat)),
             Nat.nat](Fun.comp[(Transition.transition_ext[Unit], Nat.nat),
                                Nat.nat,
                                (Nat.nat,
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))](((aa:
           (Transition.transition_ext[Unit], Nat.nat))
          =>
         aa._2),
        ((aa: (Nat.nat, (Transition.transition_ext[Unit], Nat.nat))) => aa._2)),
                       k_outgoing(n, e, s1))
                                      val outgoing_s2: FSet.fset[Nat.nat] =
FSet.fimage[(Nat.nat, (Transition.transition_ext[Unit], Nat.nat)),
             Nat.nat](Fun.comp[(Transition.transition_ext[Unit], Nat.nat),
                                Nat.nat,
                                (Nat.nat,
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))](((aa:
           (Transition.transition_ext[Unit], Nat.nat))
          =>
         aa._2),
        ((aa: (Nat.nat, (Transition.transition_ext[Unit], Nat.nat))) => aa._2)),
                       k_outgoing(n, e, s2))
                                      val scores: FSet.fset[Nat.nat] =
FSet.fimage[(Nat.nat, Nat.nat),
             Nat.nat](((aa: (Nat.nat, Nat.nat)) =>
                        {
                          val (x, y): (Nat.nat, Nat.nat) = aa;
                          ((rank(x))(y))(e)
                        }),
                       FSet_Utils.fprod[Nat.nat,
 Nat.nat](outgoing_s1, outgoing_s2));
                                      (FSet_Utils.fSum[Nat.nat](scores),
(s1, s2))
                                    }),
                                   pairs_to_score);
    FSet.ffilter[(Nat.nat,
                   (Nat.nat,
                     Nat.nat))](((aa: (Nat.nat, (Nat.nat, Nat.nat))) =>
                                  {
                                    val (score, _):
  (Nat.nat, (Nat.nat, Nat.nat))
                                      = aa;
                                    Nat.less_nat(Nat.zero_nata, score)
                                  }),
                                 a)
  }

def max_int(e: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Int.int
  =
  Lattices_Big.Max[Int.int](Set.insert[Int.int](Int.zero_int,
         EFSM.enumerate_ints(tm(e))))

def max_reg(e: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Option[Nat.nat]
  =
  {
    val maxes: FSet.fset[Option[Nat.nat]] =
      FSet.fimage[(Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                   Option[Nat.nat]](((a:
(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                                       =>
                                      {
val (_, aa): (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])) =
  a
val (_, ab): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = aa;
Transition.max_reg(ab)
                                      }),
                                     e);
    (if (FSet.equal_fseta[Option[Nat.nat]](maxes,
    FSet.bot_fset[Option[Nat.nat]]))
      None else FSet.fMax[Option[Nat.nat]](maxes))
  }

def replace(e: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))],
             tID: Nat.nat, t: Transition.transition_ext[Unit]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (Nat.nat,
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, aa):
                        (Nat.nat,
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a
                  val (ab, b):
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                    = aa;
                  ({
                     val (from, dest): (Nat.nat, Nat.nat) = ab;
                     ((ta: Transition.transition_ext[Unit]) =>
                       (if (Nat.equal_nata(uid, tID)) (uid, ((from, dest), t))
                         else (uid, ((from, dest), ta))))
                   })(b)
                }),
               e)

def make_outputs(x0: List[Value.value]): List[AExp.aexp] = x0 match {
  case Nil => Nil
  case h :: t => AExp.L(h) :: make_outputs(t)
}

def make_guard(x0: List[Value.value], uu: Nat.nat): List[GExp.gexp] = (x0, uu)
  match {
  case (Nil, uu) => Nil
  case (h :: t, n) =>
    GExp.Eq(AExp.V(VName.I(n)), AExp.L(h)) ::
      make_guard(t, Nat.plus_nata(n, Nat.Nata((1))))
}

def add_transition(e: FSet.fset[((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])],
                    s: Nat.nat, label: String, inputs: List[Value.value],
                    outputs: List[Value.value]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  FSet.finsert[((Nat.nat, Nat.nat),
                 Transition.transition_ext[Unit])](((s,
              Nat.plus_nata(maxS(e), Nat.Nata((1)))),
             Transition.transition_exta[Unit](label, Nat.Nata(inputs.length),
       make_guard(inputs, Nat.zero_nata), make_outputs(outputs), Nil, ())),
            e)

def make_branch(e: FSet.fset[((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit])],
                 uu: Nat.nat, uv: Map[Nat.nat, Option[Value.value]],
                 x3: List[(String, (List[Value.value], List[Value.value]))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  (e, uu, uv, x3) match {
  case (e, uu, uv, Nil) => e
  case (e, s, r, (label, (inputs, outputs)) :: t) =>
    (EFSM.step(e, s, r, label, inputs) match {
       case None =>
         make_branch(add_transition(e, s, label, inputs, outputs),
                      Nat.plus_nata(maxS(e), Nat.Nata((1))), r, t)
       case Some((_, (sa, (outputsa, updated)))) =>
         (if (Lista.equal_lista[Option[Value.value]](outputsa,
              Lista.map[Value.value,
                         Option[Value.value]](((a: Value.value) =>
        Some[Value.value](a)),
       outputs)))
           make_branch(e, sa, updated, t)
           else make_branch(add_transition(e, s, label, inputs, outputs),
                             Nat.plus_nata(maxS(e), Nat.Nata((1))), r, t))
     })
}

def make_pta(x0: List[List[(String, (List[Value.value], List[Value.value]))]],
              e: FSet.fset[((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  (x0, e) match {
  case (h :: t, e) =>
    make_pta(t, make_branch(e, Nat.zero_nata, Map().withDefaultValue(None), h))
  case (Nil, e) => e
}

def fold_into(n: Nat.nat, x1: List[GExp.gexp]): List[GExp.gexp] = (n, x1) match
  {
  case (n, Nil) =>
    List(GExp.Nor(GExp.Null(AExp.V(VName.I(n))), GExp.Null(AExp.V(VName.I(n)))))
  case (n, GExp.Eq(AExp.V(VName.I(i)), AExp.L(l)) :: t) =>
    (if (Nat.equal_nata(i, n)) GExp.Eq(AExp.V(VName.I(i)), AExp.L(l)) :: t
      else GExp.Eq(AExp.V(VName.I(i)), AExp.L(l)) :: fold_into(n, t))
  case (n, GExp.In(VName.I(i), l) :: t) =>
    (if (Nat.equal_nata(i, n)) GExp.In(VName.I(i), l) :: t
      else GExp.In(VName.I(i), l) :: fold_into(n, t))
  case (n, GExp.Bc(v) :: t) => GExp.Bc(v) :: fold_into(n, t)
  case (n, GExp.Eq(AExp.L(vb), va) :: t) =>
    GExp.Eq(AExp.L(vb), va) :: fold_into(n, t)
  case (n, GExp.Eq(AExp.V(VName.R(vc)), va) :: t) =>
    GExp.Eq(AExp.V(VName.R(vc)), va) :: fold_into(n, t)
  case (n, GExp.Eq(AExp.Plus(vb, vc), va) :: t) =>
    GExp.Eq(AExp.Plus(vb, vc), va) :: fold_into(n, t)
  case (n, GExp.Eq(AExp.Minus(vb, vc), va) :: t) =>
    GExp.Eq(AExp.Minus(vb, vc), va) :: fold_into(n, t)
  case (n, GExp.Eq(v, AExp.V(vb)) :: t) =>
    GExp.Eq(v, AExp.V(vb)) :: fold_into(n, t)
  case (n, GExp.Eq(v, AExp.Plus(vb, vc)) :: t) =>
    GExp.Eq(v, AExp.Plus(vb, vc)) :: fold_into(n, t)
  case (n, GExp.Eq(v, AExp.Minus(vb, vc)) :: t) =>
    GExp.Eq(v, AExp.Minus(vb, vc)) :: fold_into(n, t)
  case (n, GExp.Gt(v, va) :: t) => GExp.Gt(v, va) :: fold_into(n, t)
  case (n, GExp.Null(v) :: t) => GExp.Null(v) :: fold_into(n, t)
  case (n, GExp.In(VName.R(vb), va) :: t) =>
    GExp.In(VName.R(vb), va) :: fold_into(n, t)
  case (n, GExp.Nor(v, va) :: t) => GExp.Nor(v, va) :: fold_into(n, t)
}

def get_by_id(e: FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))],
               u: Nat.nat):
      Transition.transition_ext[Unit]
  =
  ((FSet.fthe_elem[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit]))](FSet.ffilter[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))](((a:
                                  (Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])))
                                 =>
                                {
                                  val (uid, _):
(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                    = a;
                                  Nat.equal_nata(uid, u)
                                }),
                               e)))._2)._2

def replaceAll(e: FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
                old: Transition.transition_ext[Unit],
                newa: Transition.transition_ext[Unit]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (Nat.nat,
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, aa):
                        (Nat.nat,
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

def literal_args(x0: GExp.gexp): Boolean = x0 match {
  case GExp.Bc(v) => false
  case GExp.Eq(AExp.V(uu), AExp.L(uv)) => true
  case GExp.In(uw, ux) => true
  case GExp.Eq(AExp.L(v), uz) => false
  case GExp.Eq(AExp.Plus(v, va), uz) => false
  case GExp.Eq(AExp.Minus(v, va), uz) => false
  case GExp.Eq(uy, AExp.V(v)) => false
  case GExp.Eq(uy, AExp.Plus(v, va)) => false
  case GExp.Eq(uy, AExp.Minus(v, va)) => false
  case GExp.Gt(v, va) => false
  case GExp.Null(v) => false
  case GExp.Nor(v, va) => (literal_args(v)) && (literal_args(va))
}

def satisfiable_list(l: List[GExp.gexp]): Boolean =
  Dirties.satisfiable(Lista.fold[GExp.gexp,
                                  GExp.gexp](((v: GExp.gexp) =>
       (va: GExp.gexp) => GExp.Nor(GExp.Nor(v, v), GExp.Nor(va, va))),
      l, GExp.Bc(true)))

def smart_not_null(x0: List[Nat.nat], g: List[GExp.gexp]): List[GExp.gexp] =
  (x0, g) match {
  case (Nil, g) => g
  case (h :: t, g) => fold_into(h, smart_not_null(t, g))
}

def simple_mutex(ta: Transition.transition_ext[Unit],
                  t: Transition.transition_ext[Unit]):
      Boolean
  =
  (Transition.Label[Unit](ta) ==
    Transition.Label[Unit](t)) && ((Nat.equal_nata(Transition.Arity[Unit](ta),
            Transition.Arity[Unit](t))) && ((Optiona.is_none[Nat.nat](GExp.max_reg_list(Transition.Guard[Unit](ta)))) && ((Option_Lexorder.less_option[Nat.nat](GExp.max_input_list(Transition.Guard[Unit](ta)),
 Some[Nat.nat](Transition.Arity[Unit](ta)))) && ((satisfiable_list(smart_not_null(Lista.upt(Nat.zero_nata,
             Transition.Arity[Unit](ta)),
   Transition.Guard[Unit](ta)))) && (! (EFSM.choice(t, ta)))))))

def null_modifier(uu: Nat.nat, uv: Nat.nat, uw: Nat.nat,
                   ux: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   uy: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                   uz: (FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
                         FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       ((Transition.transition_ext[Unit],
  Nat.nat),
 (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  None

def total_max_reg(e: FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  (FSet.fMax[Option[Nat.nat]](FSet.fimage[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
   Option[Nat.nat]](((a: (Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])))
                       =>
                      {
                        val (_, aa):
                              (Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))
                          = a
                        val (_, ab):
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])
                          = aa;
                        Transition.max_reg(ab)
                      }),
                     e))
     match {
     case None => Nat.zero_nata
     case Some(r) => r
   })

def inference_step(uu: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                    x1: List[(Nat.nat, (Nat.nat, Nat.nat))],
                    uv: Nat.nat =>
                          Nat.nat =>
                            Nat.nat =>
                              (FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                (FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                  ((FSet.fset[(Nat.nat,
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                    FSet.fset[(Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], Nat.nat),
            (Transition.transition_ext[Unit], Nat.nat))))]) =>
                                    Option[FSet.fset[(Nat.nat,
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                    uw: (FSet.fset[((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])]) =>
                          Boolean,
                    ux: (FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], Nat.nat),
  (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (uu, x1, uv, uw, ux) match {
  case (uu, Nil, uv, uw, ux) => None
  case (e, (uy, (s_1, s_2)) :: t, m, check, np) =>
    (merge(e, s_1, s_2, m, check, np) match {
       case None => inference_step(e, t, m, check, np)
       case Some(a) =>
         Some[FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]](a)
     })
}

def try_heuristics(x0: List[Nat.nat =>
                              Nat.nat =>
                                Nat.nat =>
                                  (FSet.fset[(Nat.nat,
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                    (FSet.fset[(Nat.nat,
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                      ((FSet.fset[(Nat.nat,
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
FSet.fset[(Nat.nat,
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[Unit], Nat.nat),
                (Transition.transition_ext[Unit], Nat.nat))))]) =>
Option[FSet.fset[(Nat.nat,
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]],
                    uu: (FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], Nat.nat),
  (Transition.transition_ext[Unit], Nat.nat))))]):
      Nat.nat =>
        Nat.nat =>
          Nat.nat =>
            (FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                ((FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit], Nat.nat),
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))))]) =>
                  Option[FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]]
  =
  (x0, uu) match {
  case (Nil, uu) =>
    ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
      (d: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (e: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (f: (FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]) =>
            FSet.fset[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          ((Transition.transition_ext[Unit], Nat.nat),
                            (Transition.transition_ext[Unit], Nat.nat))))])
        =>
      null_modifier(a, b, c, d, e, f))
  case (h :: t, np) =>
    ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
      (d: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (e: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (npa: (FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            ((Transition.transition_ext[Unit], Nat.nat),
                              (Transition.transition_ext[Unit], Nat.nat))))])
        =>
      ((((((h(a))(b))(c))(d))(e))(npa) match {
         case None =>
           (try_heuristics(t, npa)).apply(a).apply(b).apply(c).apply(d).apply(e).apply(npa)
         case Some(aa) =>
           Some[FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](aa)
       }))
}

def drop_transitions(e: FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      t: FSet.fset[Nat.nat]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, _):
                        (Nat.nat,
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a;
                  ! (FSet.fmember[Nat.nat](uid, t))
                }),
               e)

def nondeterministic(t: FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      np: (FSet.fset[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]) =>
                            FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat),
  ((Transition.transition_ext[Unit], Nat.nat),
    (Transition.transition_ext[Unit], Nat.nat))))]):
      Boolean
  =
  ! (deterministic(t, np))

def make_outputs_abstract(x0: List[Value.value], uu: Nat.nat,
                           uv: Map[String, Option[Nat.nat]],
                           p: List[AExp.aexp]):
      List[AExp.aexp]
  =
  (x0, uu, uv, p) match {
  case (Nil, uu, uv, p) => p.reverse
  case (h :: t, maxR, r, p) =>
    (h match {
       case Value.Numa(_) => make_outputs_abstract(t, maxR, r, AExp.L(h) :: p)
       case Value.Str(s) =>
         (if (s.startsWith("$"))
           {
             val (Some(reg)): Option[Nat.nat] = r(s);
             make_outputs_abstract(t, maxR, r, AExp.V(VName.R(reg)) :: p)
           }
           else make_outputs_abstract(t, maxR, r, AExp.L(h) :: p))
     })
}

def make_guard_abstract(x0: List[Value.value], uu: Nat.nat, uv: Nat.nat,
                         r: Map[String, Option[Nat.nat]], g: List[GExp.gexp],
                         u: List[(Nat.nat, AExp.aexp)]):
      (List[GExp.gexp],
        (List[(Nat.nat, AExp.aexp)], Map[String, Option[Nat.nat]]))
  =
  (x0, uu, uv, r, g, u) match {
  case (Nil, uu, uv, r, g, u) => (g, (u, r))
  case (h :: t, i, maxR, r, g, u) =>
    (h match {
       case Value.Numa(_) =>
         make_guard_abstract(t, Nat.plus_nata(i, Nat.Nata((1))), maxR, r,
                              GExp.Eq(AExp.V(VName.I(i)), AExp.L(h)) :: g, u)
       case Value.Str(s) =>
         (if (s == "_")
           make_guard_abstract(t, Nat.plus_nata(i, Nat.Nata((1))), maxR, r, g,
                                u)
           else (if (s.startsWith("$"))
                  (r(s) match {
                     case None =>
                       make_guard_abstract(t, Nat.plus_nata(i, Nat.Nata((1))),
    Nat.plus_nata(maxR, Nat.Nata((1))), r + (s -> (Some[Nat.nat](maxR))), g,
    (maxR, AExp.V(VName.I(i))) :: u)
                     case Some(reg) =>
                       make_guard_abstract(t, Nat.plus_nata(i, Nat.Nata((1))),
    maxR, r, GExp.Eq(AExp.V(VName.I(i)), AExp.V(VName.R(reg))) :: g, u)
                   })
                  else (if (s.startsWith("<"))
                         (if ((s.substring(Code_Numeral.integer_of_nat(Nat.Nata((1))).toInt)).startsWith("$"))
                           {
                             val (Some(reg)): Option[Nat.nat] =
                               r(s.substring(Code_Numeral.integer_of_nat(Nat.Nata((1))).toInt));
                             make_guard_abstract(t,
          Nat.plus_nata(i, Nat.Nata((1))), maxR, r,
          GExp.Gt(AExp.V(VName.I(i)), AExp.V(VName.R(reg))) :: g, u)
                           }
                           else make_guard_abstract(t,
             Nat.plus_nata(i, Nat.Nata((1))), maxR, r,
             GExp.Gt(AExp.V(VName.I(i)),
                      AExp.L(Value.Numa(Int.int_of_integer(BigInt((s.substring(Code_Numeral.integer_of_nat(Code_Numeral.nat_of_integer(BigInt(2))).toInt)).toInt))))) ::
               g,
             u))
                         else (if (s.startsWith("/="))
                                (if ((s.substring(Code_Numeral.integer_of_nat(Nat.Nata((1))).toInt)).startsWith("$"))
                                  {
                                    val (Some(reg)): Option[Nat.nat] =
                                      r(s.substring(Code_Numeral.integer_of_nat(Code_Numeral.nat_of_integer(BigInt(2))).toInt));
                                    make_guard_abstract(t,
                 Nat.plus_nata(i, Nat.Nata((1))), maxR, r,
                 GExp.Gt(AExp.V(VName.I(i)), AExp.V(VName.R(reg))) :: g, u)
                                  }
                                  else make_guard_abstract(t,
                    Nat.plus_nata(i, Nat.Nata((1))), maxR, r,
                    GExp.Gt(AExp.V(VName.I(i)),
                             AExp.L(Value.Numa(Int.int_of_integer(BigInt((s.substring(Code_Numeral.integer_of_nat(Code_Numeral.nat_of_integer(BigInt(3))).toInt)).toInt))))) ::
                      g,
                    u))
                                else make_guard_abstract(t,
                  Nat.plus_nata(i, Nat.Nata((1))), maxR, r,
                  GExp.Eq(AExp.V(VName.I(i)), AExp.L(h)) :: g, u)))))
     })
}

def add_transition_abstract(e: FSet.fset[((Nat.nat, Nat.nat),
   Transition.transition_ext[Unit])],
                             r: Map[String, Option[Nat.nat]], s: Nat.nat,
                             label: String, inputs: List[Value.value],
                             outputs: List[Value.value]):
      (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
        Map[String, Option[Nat.nat]])
  =
  {
    val regs: FSet.fset[Nat.nat] =
      FSet.fimage[((Nat.nat, Nat.nat), Transition.transition_ext[Unit]),
                   Nat.nat](Fun.comp[Transition.transition_ext[Unit], Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])](((a: Transition.transition_ext[Unit]) =>
                                    Transition.total_max_reg(a)),
                                   ((a: ((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit]))
                                      =>
                                     a._2)),
                             e)
    val maxR: Nat.nat =
      (if (FSet.equal_fseta[Nat.nat](regs, FSet.bot_fset[Nat.nat]))
        Nat.Nata((1)) else FSet.fMax[Nat.nat](regs))
    val (g, (u1, ra)):
          (List[GExp.gexp],
            (List[(Nat.nat, AExp.aexp)], Map[String, Option[Nat.nat]]))
      = make_guard_abstract(inputs, Nat.zero_nata, maxR, r, Nil, Nil)
    val p: List[AExp.aexp] = make_outputs_abstract(outputs, maxR, ra, Nil);
    (if (label.endsWith("*"))
      (FSet.finsert[((Nat.nat, Nat.nat),
                      Transition.transition_ext[Unit])](((s, s),
                  Transition.transition_exta[Unit](label.dropRight(Code_Numeral.integer_of_nat(Nat.Nata((1))).toInt),
            Nat.Nata(inputs.length), g, p, u1, ())),
                 e),
        ra)
      else (FSet.finsert[((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit])](((s,
                        Nat.plus_nata(maxS(e), Nat.Nata((1)))),
                       Transition.transition_exta[Unit](label,
                 Nat.Nata(inputs.length), g, p, u1, ())),
                      e),
             ra))
  }

def make_branch_abstract(x0: (FSet.fset[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])],
                               Map[String, Option[Nat.nat]]),
                          uu: Nat.nat, uv: Map[Nat.nat, Option[Value.value]],
                          x3: List[(String,
                                     (List[Value.value], List[Value.value]))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  (x0, uu, uv, x3) match {
  case ((e, r), uu, uv, Nil) => e
  case ((e, r1), s, r, (label, (inputs, outputs)) :: t) =>
    (EFSM.step(e, s, r, label, inputs) match {
       case None =>
         make_branch_abstract(add_transition_abstract(e, r1, s, label, inputs,
               outputs),
                               Nat.plus_nata(maxS(e), Nat.Nata((1))), r, t)
       case Some((_, (sa, (outputsa, updated)))) =>
         (if (Lista.equal_lista[Option[Value.value]](outputsa,
              Lista.map[Value.value,
                         Option[Value.value]](((a: Value.value) =>
        Some[Value.value](a)),
       outputs)))
           make_branch_abstract((e, r1), sa, updated, t)
           else make_branch_abstract(add_transition_abstract(e, r1, s, label,
                      inputs, outputs),
                                      Nat.plus_nata(maxS(e), Nat.Nata((1))), r,
                                      t))
     })
}

def make_pta_abstract(l: List[List[(String,
                                     (List[Value.value], List[Value.value]))]],
                       e: FSet.fset[((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  Lista.fold[List[(String, (List[Value.value], List[Value.value]))],
              FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit])]](((h:
                         List[(String, (List[Value.value], List[Value.value]))])
                        =>
                       (ea: FSet.fset[((Nat.nat, Nat.nat),
Transition.transition_ext[Unit])])
                         =>
                       make_branch_abstract((ea, Map().withDefaultValue(None)),
     Nat.zero_nata, Map().withDefaultValue(None), h)),
                      l, e)

def state_nondeterminism(origin: Nat.nat,
                          nt: FSet.fset[(Nat.nat,
  (Transition.transition_ext[Unit], Nat.nat))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (Transition.transition_ext[Unit], Nat.nat))))]
  =
  (if (Nat.less_nat(FSet.size_fset[(Nat.nat,
                                     (Transition.transition_ext[Unit],
                                       Nat.nat))](nt),
                     Code_Numeral.nat_of_integer(BigInt(2))))
    FSet.bot_fset[(Nat.nat,
                    ((Nat.nat, Nat.nat),
                      ((Transition.transition_ext[Unit], Nat.nat),
                        (Transition.transition_ext[Unit], Nat.nat))))]
    else FSet.ffUnion[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          ((Transition.transition_ext[Unit], Nat.nat),
                            (Transition.transition_ext[Unit],
                              Nat.nat))))](FSet.fimage[(Nat.nat,
                 (Transition.transition_ext[Unit], Nat.nat)),
                FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              ((Transition.transition_ext[Unit], Nat.nat),
                                (Transition.transition_ext[Unit],
                                  Nat.nat))))]](((x:
            (Nat.nat, (Transition.transition_ext[Unit], Nat.nat)))
           =>
          {
            val (dest, t): (Nat.nat, (Transition.transition_ext[Unit], Nat.nat))
              = x;
            FSet.fimage[(Nat.nat, (Transition.transition_ext[Unit], Nat.nat)),
                         (Nat.nat,
                           ((Nat.nat, Nat.nat),
                             ((Transition.transition_ext[Unit], Nat.nat),
                               (Transition.transition_ext[Unit],
                                 Nat.nat))))](((y:
          (Nat.nat, (Transition.transition_ext[Unit], Nat.nat)))
         =>
        {
          val (desta, ta): (Nat.nat, (Transition.transition_ext[Unit], Nat.nat))
            = y;
          (origin, ((dest, desta), (t, ta)))
        }),
       FSet_Utils.fremove[(Nat.nat,
                            (Transition.transition_ext[Unit], Nat.nat))](x, nt))
          }),
         nt)))

def try_heuristics_check(uu: (FSet.fset[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])]) =>
                               Boolean,
                          x1: List[Nat.nat =>
                                     Nat.nat =>
                                       Nat.nat =>
 (FSet.fset[(Nat.nat,
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
   (FSet.fset[(Nat.nat,
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
     ((FSet.fset[(Nat.nat,
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
       FSet.fset[(Nat.nat,
                   ((Nat.nat, Nat.nat),
                     ((Transition.transition_ext[Unit], Nat.nat),
                       (Transition.transition_ext[Unit], Nat.nat))))]) =>
       Option[FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]]],
                          uv: (FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat),
      ((Transition.transition_ext[Unit], Nat.nat),
        (Transition.transition_ext[Unit], Nat.nat))))]):
      Nat.nat =>
        Nat.nat =>
          Nat.nat =>
            (FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                ((FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit], Nat.nat),
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))))]) =>
                  Option[FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]]
  =
  (uu, x1, uv) match {
  case (uu, Nil, uv) =>
    ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
      (d: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (e: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (f: (FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]) =>
            FSet.fset[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          ((Transition.transition_ext[Unit], Nat.nat),
                            (Transition.transition_ext[Unit], Nat.nat))))])
        =>
      null_modifier(a, b, c, d, e, f))
  case (check, h :: t, np) =>
    ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
      (d: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (e: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (npa: (FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            ((Transition.transition_ext[Unit], Nat.nat),
                              (Transition.transition_ext[Unit], Nat.nat))))])
        =>
      ((((((h(a))(b))(c))(d))(e))(npa) match {
         case None =>
           (try_heuristics_check(check, t,
                                  npa)).apply(a).apply(b).apply(c).apply(d).apply(e).apply(npa)
         case Some(ea) =>
           (if (check(tm(ea)))
             Some[FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]](ea)
             else (try_heuristics_check(check, t,
 npa)).apply(a).apply(b).apply(c).apply(d).apply(e).apply(npa))
       }))
}

def nondeterministic_pairs(t: FSet.fset[(Nat.nat,
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (Transition.transition_ext[Unit], Nat.nat))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (Transition.transition_ext[Unit],
                       Nat.nat))))](((a:
(Nat.nat,
  ((Nat.nat, Nat.nat),
    ((Transition.transition_ext[Unit], Nat.nat),
      (Transition.transition_ext[Unit], Nat.nat)))))
                                       =>
                                      {
val (_, aa):
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], Nat.nat),
            (Transition.transition_ext[Unit], Nat.nat))))
  = a
val (_, ab):
      ((Nat.nat, Nat.nat),
        ((Transition.transition_ext[Unit], Nat.nat),
          (Transition.transition_ext[Unit], Nat.nat)))
  = aa
val (ac, b):
      ((Transition.transition_ext[Unit], Nat.nat),
        (Transition.transition_ext[Unit], Nat.nat))
  = ab;
({
   val (ta, _): (Transition.transition_ext[Unit], Nat.nat) = ac;
   ((ad: (Transition.transition_ext[Unit], Nat.nat)) =>
     {
       val (taa, _): (Transition.transition_ext[Unit], Nat.nat) = ad;
       (Transition.Label[Unit](ta) ==
         Transition.Label[Unit](taa)) && ((Nat.equal_nata(Transition.Arity[Unit](ta),
                   Transition.Arity[Unit](taa))) && (EFSM.choice(ta, taa)))
     })
 })(b)
                                      }),
                                     FSet.ffUnion[(Nat.nat,
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[Unit], Nat.nat),
                (Transition.transition_ext[Unit],
                  Nat.nat))))](FSet.fimage[Nat.nat,
    FSet.fset[(Nat.nat,
                ((Nat.nat, Nat.nat),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (Transition.transition_ext[Unit],
                      Nat.nat))))]](((s: Nat.nat) =>
                                      state_nondeterminism(s,
                    outgoing_transitions(s, t))),
                                     S(t))))

def nondeterministic_pairs_labar(t: FSet.fset[(Nat.nat,
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (Transition.transition_ext[Unit], Nat.nat))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (Transition.transition_ext[Unit],
                       Nat.nat))))](((a:
(Nat.nat,
  ((Nat.nat, Nat.nat),
    ((Transition.transition_ext[Unit], Nat.nat),
      (Transition.transition_ext[Unit], Nat.nat)))))
                                       =>
                                      {
val (_, aa):
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], Nat.nat),
            (Transition.transition_ext[Unit], Nat.nat))))
  = a
val (ab, b):
      ((Nat.nat, Nat.nat),
        ((Transition.transition_ext[Unit], Nat.nat),
          (Transition.transition_ext[Unit], Nat.nat)))
  = aa;
({
   val (_, _): (Nat.nat, Nat.nat) = ab;
   ((ac: ((Transition.transition_ext[Unit], Nat.nat),
           (Transition.transition_ext[Unit], Nat.nat)))
      =>
     {
       val (ad, ba):
             ((Transition.transition_ext[Unit], Nat.nat),
               (Transition.transition_ext[Unit], Nat.nat))
         = ac;
       ({
          val (ta, _): (Transition.transition_ext[Unit], Nat.nat) = ad;
          ((ae: (Transition.transition_ext[Unit], Nat.nat)) =>
            {
              val (taa, _): (Transition.transition_ext[Unit], Nat.nat) = ae;
              (Transition.Label[Unit](ta) ==
                Transition.Label[Unit](taa)) && ((Nat.equal_nata(Transition.Arity[Unit](ta),
                          Transition.Arity[Unit](taa))) && ((EFSM.choice(ta,
                                  taa)) || (Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](ta),
                                  Transition.Outputs[Unit](taa)))))
            })
        })(ba)
     })
 })(b)
                                      }),
                                     FSet.ffUnion[(Nat.nat,
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[Unit], Nat.nat),
                (Transition.transition_ext[Unit],
                  Nat.nat))))](FSet.fimage[Nat.nat,
    FSet.fset[(Nat.nat,
                ((Nat.nat, Nat.nat),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (Transition.transition_ext[Unit],
                      Nat.nat))))]](((s: Nat.nat) =>
                                      state_nondeterminism(s,
                    outgoing_transitions(s, t))),
                                     S(t))))

def nondeterministic_pairs_labar_dest(t:
FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (Transition.transition_ext[Unit], Nat.nat))))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (Transition.transition_ext[Unit],
                       Nat.nat))))](((a:
(Nat.nat,
  ((Nat.nat, Nat.nat),
    ((Transition.transition_ext[Unit], Nat.nat),
      (Transition.transition_ext[Unit], Nat.nat)))))
                                       =>
                                      {
val (_, aa):
      (Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], Nat.nat),
            (Transition.transition_ext[Unit], Nat.nat))))
  = a
val (ab, b):
      ((Nat.nat, Nat.nat),
        ((Transition.transition_ext[Unit], Nat.nat),
          (Transition.transition_ext[Unit], Nat.nat)))
  = aa;
({
   val (d, da): (Nat.nat, Nat.nat) = ab;
   ((ac: ((Transition.transition_ext[Unit], Nat.nat),
           (Transition.transition_ext[Unit], Nat.nat)))
      =>
     {
       val (ad, ba):
             ((Transition.transition_ext[Unit], Nat.nat),
               (Transition.transition_ext[Unit], Nat.nat))
         = ac;
       ({
          val (ta, _): (Transition.transition_ext[Unit], Nat.nat) = ad;
          ((ae: (Transition.transition_ext[Unit], Nat.nat)) =>
            {
              val (taa, _): (Transition.transition_ext[Unit], Nat.nat) = ae;
              (Transition.Label[Unit](ta) ==
                Transition.Label[Unit](taa)) && ((Nat.equal_nata(Transition.Arity[Unit](ta),
                          Transition.Arity[Unit](taa))) && ((EFSM.choice(ta,
                                  taa)) || ((Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](ta),
                                   Transition.Outputs[Unit](taa))) && (Nat.equal_nata(d,
       da)))))
            })
        })(ba)
     })
 })(b)
                                      }),
                                     FSet.ffUnion[(Nat.nat,
            ((Nat.nat, Nat.nat),
              ((Transition.transition_ext[Unit], Nat.nat),
                (Transition.transition_ext[Unit],
                  Nat.nat))))](FSet.fimage[Nat.nat,
    FSet.fset[(Nat.nat,
                ((Nat.nat, Nat.nat),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (Transition.transition_ext[Unit],
                      Nat.nat))))]](((s: Nat.nat) =>
                                      state_nondeterminism(s,
                    outgoing_transitions(s, t))),
                                     S(t))))

} /* object Inference */

object Code_Generation {

def And: GExp.gexp => GExp.gexp => GExp.gexp =
  ((v: GExp.gexp) => (va: GExp.gexp) =>
    GExp.Nor(GExp.Nor(v, v), GExp.Nor(va, va)))

def mutex(uu: GExp.gexp, uv: GExp.gexp): Boolean = (uu, uv) match {
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.Eq(AExp.V(v), AExp.L(l))) =>
    (if (VName.equal_vnamea(va, v)) ! (Value.equal_valuea(la, l)) else false)
  case (GExp.In(va, la), GExp.Eq(AExp.V(v), AExp.L(l))) =>
    (VName.equal_vnamea(va, v)) && (! (la contains l))
  case (GExp.Eq(AExp.V(va), AExp.L(la)), GExp.In(v, l)) =>
    (VName.equal_vnamea(v, va)) && (! (l contains la))
  case (GExp.In(va, la), GExp.In(v, l)) =>
    (VName.equal_vnamea(va, v)) && (Set.equal_set[Value.value](Set.inf_set[Value.value](Set.seta[Value.value](la),
         Set.seta[Value.value](l)),
                        Set.bot_set[Value.value]))
  case (GExp.Bc(v), uv) => false
  case (GExp.Eq(AExp.L(vb), va), uv) => false
  case (GExp.Eq(AExp.Plus(vb, vc), va), uv) => false
  case (GExp.Eq(AExp.Minus(vb, vc), va), uv) => false
  case (GExp.Eq(v, AExp.V(vb)), uv) => false
  case (GExp.Eq(v, AExp.Plus(vb, vc)), uv) => false
  case (GExp.Eq(v, AExp.Minus(vb, vc)), uv) => false
  case (GExp.Gt(v, va), uv) => false
  case (GExp.Null(v), uv) => false
  case (GExp.In(v, va), GExp.Bc(vb)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.L(vd), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Plus(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(AExp.Minus(vd, ve), vc)) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.V(vd))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Plus(vd, ve))) => false
  case (GExp.In(v, va), GExp.Eq(vb, AExp.Minus(vd, ve))) => false
  case (GExp.In(v, va), GExp.Gt(vb, vc)) => false
  case (GExp.In(v, va), GExp.Null(vb)) => false
  case (GExp.In(v, va), GExp.Nor(vb, vc)) => false
  case (GExp.Nor(v, va), uv) => false
  case (uu, GExp.Bc(v)) => false
  case (uu, GExp.Eq(AExp.L(vb), va)) => false
  case (uu, GExp.Eq(AExp.Plus(vb, vc), va)) => false
  case (uu, GExp.Eq(AExp.Minus(vb, vc), va)) => false
  case (uu, GExp.Eq(v, AExp.V(vb))) => false
  case (uu, GExp.Eq(v, AExp.Plus(vb, vc))) => false
  case (uu, GExp.Eq(v, AExp.Minus(vb, vc))) => false
  case (uu, GExp.Gt(v, va)) => false
  case (uu, GExp.Null(v)) => false
  case (uu, GExp.Nor(v, va)) => false
}

def choice_cases(t1: Transition.transition_ext[Unit],
                  t2: Transition.transition_ext[Unit]):
      Boolean
  =
  (if (Lista.list_ex[(GExp.gexp,
                       GExp.gexp)](((a: (GExp.gexp, GExp.gexp)) =>
                                     {
                                       val (aa, b): (GExp.gexp, GExp.gexp) = a;
                                       mutex(aa, b)
                                     }),
                                    Lista.product[GExp.gexp,
           GExp.gexp](Transition.Guard[Unit](t1), Transition.Guard[Unit](t2))))
    false
    else (if (Lista.equal_lista[GExp.gexp](Transition.Guard[Unit](t1),
    Transition.Guard[Unit](t2)))
           Dirties.satisfiable(Lista.foldr[GExp.gexp,
    GExp.gexp](((v: GExp.gexp) => (va: GExp.gexp) =>
                 GExp.Nor(GExp.Nor(v, v), GExp.Nor(va, va))),
                Transition.Guard[Unit](t1), GExp.Bc(true)))
           else Dirties.satisfiable(Lista.foldr[GExp.gexp,
         GExp.gexp](((v: GExp.gexp) => (va: GExp.gexp) =>
                      GExp.Nor(GExp.Nor(v, v), GExp.Nor(va, va))),
                     Transition.Guard[Unit](t1) ++ Transition.Guard[Unit](t2),
                     GExp.Bc(true)))))

def infer_with_log(stepNo: Nat.nat, k: Nat.nat,
                    e: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                    r: Nat.nat =>
                         Nat.nat =>
                           (FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                             Nat.nat,
                    m: Nat.nat =>
                         Nat.nat =>
                           Nat.nat =>
                             (FSet.fset[(Nat.nat,
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                               (FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 ((FSet.fset[(Nat.nat,
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                   FSet.fset[(Nat.nat,
       ((Nat.nat, Nat.nat),
         ((Transition.transition_ext[Unit], Nat.nat),
           (Transition.transition_ext[Unit], Nat.nat))))]) =>
                                   Option[FSet.fset[(Nat.nat,
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                    check:
                      (FSet.fset[((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])]) =>
                        Boolean,
                    np: (FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], Nat.nat),
  (Transition.transition_ext[Unit], Nat.nat))))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (Inference.inference_step(e, (FSet.sorted_list_of_fset[(Nat.nat,
                   (Nat.nat, Nat.nat))](Inference.k_score(k, e, r))).reverse,
                             m, check, np)
     match {
     case None => e
     case Some(newa) =>
       {
         PrettyPrinter.iEFSM2dot(e, stepNo);
         Log.logStates((FSet.size_fset[Nat.nat](Inference.S(newa))), (FSet.size_fset[Nat.nat](Inference.S(e))));
         (if (FSet.less_fset[Nat.nat](Inference.S(newa), Inference.S(e)))
           infer_with_log(Nat.plus_nata(stepNo, Nat.Nata((1))), k, newa, r, m,
                           check, np)
           else e)
       }
   })

def guardMatch_code(uu: List[GExp.gexp], uv: List[GExp.gexp]): Boolean =
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
  case (GExp.Eq(vb, AExp.L(Value.Str(ve))) :: va, uv) => false
  case (GExp.Eq(vb, AExp.V(vd)) :: va, uv) => false
  case (GExp.Eq(vb, AExp.Plus(vd, ve)) :: va, uv) => false
  case (GExp.Eq(vb, AExp.Minus(vd, ve)) :: va, uv) => false
  case (GExp.Gt(vb, vc) :: va, uv) => false
  case (GExp.Null(vb) :: va, uv) => false
  case (GExp.In(vb, vc) :: va, uv) => false
  case (GExp.Nor(vb, vc) :: va, uv) => false
  case (v :: vb :: vc, uv) => false
  case (uu, Nil) => false
  case (uu, GExp.Bc(vb) :: va) => false
  case (uu, GExp.Eq(AExp.L(vd), vc) :: va) => false
  case (uu, GExp.Eq(AExp.V(VName.R(ve)), vc) :: va) => false
  case (uu, GExp.Eq(AExp.Plus(vd, ve), vc) :: va) => false
  case (uu, GExp.Eq(AExp.Minus(vd, ve), vc) :: va) => false
  case (uu, GExp.Eq(vb, AExp.L(Value.Str(ve))) :: va) => false
  case (uu, GExp.Eq(vb, AExp.V(vd)) :: va) => false
  case (uu, GExp.Eq(vb, AExp.Plus(vd, ve)) :: va) => false
  case (uu, GExp.Eq(vb, AExp.Minus(vd, ve)) :: va) => false
  case (uu, GExp.Gt(vb, vc) :: va) => false
  case (uu, GExp.Null(vb) :: va) => false
  case (uu, GExp.In(vb, vc) :: va) => false
  case (uu, GExp.Nor(vb, vc) :: va) => false
  case (uu, v :: vb :: vc) => false
}

def outputMatch_code(uu: List[AExp.aexp], uv: List[AExp.aexp]): Boolean =
  (uu, uv) match {
  case (List(AExp.L(Value.Numa(na))), List(AExp.L(Value.Numa(n)))) => true
  case (Nil, uv) => false
  case (AExp.L(Value.Str(vc)) :: va, uv) => false
  case (AExp.V(vb) :: va, uv) => false
  case (AExp.Plus(vb, vc) :: va, uv) => false
  case (AExp.Minus(vb, vc) :: va, uv) => false
  case (v :: vb :: vc, uv) => false
  case (uu, Nil) => false
  case (uu, AExp.L(Value.Str(vc)) :: va) => false
  case (uu, AExp.V(vb) :: va) => false
  case (uu, AExp.Plus(vb, vc) :: va) => false
  case (uu, AExp.Minus(vb, vc) :: va) => false
  case (uu, v :: vb :: vc) => false
}

def tests_input_equality(ia: Nat.nat, x1: GExp.gexp): Boolean = (ia, x1) match {
  case (ia, GExp.Eq(AExp.V(VName.I(i)), AExp.L(uu))) => Nat.equal_nata(ia, i)
  case (uv, GExp.Bc(v)) => false
  case (uv, GExp.Eq(AExp.L(vb), va)) => false
  case (uv, GExp.Eq(AExp.V(VName.R(vc)), va)) => false
  case (uv, GExp.Eq(AExp.Plus(vb, vc), va)) => false
  case (uv, GExp.Eq(AExp.Minus(vb, vc), va)) => false
  case (uv, GExp.Eq(v, AExp.V(vb))) => false
  case (uv, GExp.Eq(v, AExp.Plus(vb, vc))) => false
  case (uv, GExp.Eq(v, AExp.Minus(vb, vc))) => false
  case (uv, GExp.Gt(v, va)) => false
  case (uv, GExp.Null(v)) => false
  case (uv, GExp.In(v, va)) => false
  case (uv, GExp.Nor(v, va)) => false
}

def is_generalisation_of(ta: Transition.transition_ext[Unit],
                          t: Transition.transition_ext[Unit], i: Nat.nat,
                          r: Nat.nat):
      Boolean
  =
  (Transition.equal_transition_exta[Unit](ta,
   Store_Reuse.remove_guard_add_update(t, i,
r))) && ((Nat.less_nat(i, Transition.Arity[Unit](t))) && ((! ((Lista.map[(Nat.nat,
                                   AExp.aexp),
                                  Nat.nat](((a: (Nat.nat, AExp.aexp)) => a._1),
    Transition.Updates[Unit](t))) contains r)) && (Nat.less_eq_nat(Nat.Nata((1)),
                            Nat.Nata((Lista.filter[GExp.gexp](((a: GExp.gexp) =>
                        tests_input_equality(i, a)),
                       Transition.Guard[Unit](t))).length)))))

def input_updates_register_aux(x0: List[(Nat.nat, AExp.aexp)]): Option[Nat.nat]
  =
  x0 match {
  case (na, AExp.V(VName.I(n))) :: uu => Some[Nat.nat](n)
  case (v, AExp.L(vb)) :: t => input_updates_register_aux(t)
  case (v, AExp.V(VName.R(vc))) :: t => input_updates_register_aux(t)
  case (v, AExp.Plus(vb, vc)) :: t => input_updates_register_aux(t)
  case (v, AExp.Minus(vb, vc)) :: t => input_updates_register_aux(t)
  case Nil => None
}

def input_updates_register(e: FSet.fset[(Nat.nat,
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      (Nat.nat, String)
  =
  {
    val (_, (_, t)):
          (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
      = FSet.fthe_elem[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))](FSet.ffilter[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))](((a:
                                      (Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                                     =>
                                    {
                                      val
(_, (_, t)): (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])) =
a;
                                      ! (Optiona.is_none[Nat.nat](input_updates_register_aux(Transition.Updates[Unit](t))))
                                    }),
                                   e))
    val (Some(n)): Option[Nat.nat] =
      input_updates_register_aux(Transition.Updates[Unit](t));
    (n, Transition.Label[Unit](t))
  }

def always_different_outputs_direct_subsumption(m1:
          FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
         m2: FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
         sa: Nat.nat, s: Nat.nat, t: Transition.transition_ext[Unit]):
      Boolean
  =
  (if ((Transition.Guard[Unit](t)).isEmpty)
    Dirties.acceptsAndGetsUsToBoth(m1, m2, sa, s)
    else Dirties.alwaysDifferentOutputsDirectSubsumption(m1, m2, sa, s, t))

def guard_subset_eq_outputs_updates[A, B](t1: Transition.transition_ext[A],
   t2: Transition.transition_ext[B]):
      Boolean
  =
  (Transition.Label[A](t1) ==
    Transition.Label[B](t2)) && ((Nat.equal_nata(Transition.Arity[A](t1),
          Transition.Arity[B](t2))) && ((Lista.equal_lista[AExp.aexp](Transition.Outputs[A](t1),
                               Transition.Outputs[B](t2))) && ((Lista.equal_lista[(Nat.nat,
    AExp.aexp)](Transition.Updates[A](t1),
                 Transition.Updates[B](t2))) && (Lista.list_all[GExp.gexp](((a:
                                       GExp.gexp)
                                      =>
                                     (Transition.Guard[A](t1)) contains a),
                                    Transition.Guard[B](t2))))))

def always_different_outputs(x0: List[AExp.aexp], x1: List[AExp.aexp]): Boolean
  =
  (x0, x1) match {
  case (Nil, Nil) => false
  case (Nil, a :: uu) => true
  case (a :: uv, Nil) => true
  case (AExp.L(va) :: ta, AExp.L(v) :: t) =>
    (if (Value.equal_valuea(va, v)) always_different_outputs(ta, t) else true)
  case (AExp.V(v) :: ta, h :: t) => always_different_outputs(ta, t)
  case (AExp.Plus(v, va) :: ta, h :: t) => always_different_outputs(ta, t)
  case (AExp.Minus(v, va) :: ta, h :: t) => always_different_outputs(ta, t)
  case (h :: ta, AExp.V(v) :: t) => always_different_outputs(ta, t)
  case (h :: ta, AExp.Plus(v, va) :: t) => always_different_outputs(ta, t)
  case (h :: ta, AExp.Minus(v, va) :: t) => always_different_outputs(ta, t)
}

def directly_subsumes_cases(m1: FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                             m2: FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                             sa: Nat.nat, s: Nat.nat,
                             t1: Transition.transition_ext[Unit],
                             t2: Transition.transition_ext[Unit]):
      Boolean
  =
  (if (Transition.equal_transition_exta[Unit](t1, t2)) true
    else (if (Inference.simple_mutex(t2, t1)) false
           else (if ((always_different_outputs(Transition.Outputs[Unit](t1),
        Transition.Outputs[Unit](t2))) && (always_different_outputs_direct_subsumption(m1,
        m2, sa, s, t2)))
                  false
                  else (if (guard_subset_eq_outputs_updates[Unit, Unit](t2, t1))
                         true
                         else (if (Least_Upper_Bound.in_not_subset[Unit,
                            Unit](t1, t2))
                                false
                                else (if (Least_Upper_Bound.opposite_gob(t1,
                                  t2))
                                       false
                                       else (if ((always_different_outputs_direct_subsumption(m1,
               m2, sa, s,
               t2)) && (Least_Upper_Bound.lob_distinguished_2[Unit,
                       Unit](t1, t2)))
      false
      else (if ((always_different_outputs_direct_subsumption(m1, m2, sa, s,
                      t2)) && (Least_Upper_Bound.lob_distinguished_3[Unit,
                              Unit](t1, t2)))
             false
             else (if (Least_Upper_Bound.is_lob[Unit, Unit](t2, t1)) true
                    else (if (Store_Reuse_Subsumption.drop_guard_add_update_direct_subsumption(t1,
                t2, m2, s))
                           true
                           else (if (Store_Reuse_Subsumption.drop_update_add_guard_direct_subsumption(m1,
                       m2, sa, s, t1, t2))
                                  false
                                  else (if (Store_Reuse_Subsumption.generalise_output_direct_subsumption(t1,
                          t2, m1, m2, sa, s))
 true
 else (if (Store_Reuse_Subsumption.possibly_not_value(m1, m2, sa, s, t1, t2))
        false
        else (if (Transition.equal_transition_exta[Unit](t1,
                  Ignore_Inputs.drop_guards(t2)))
               true
               else Dirties.scalaDirectlySubsumes(m1, m2, sa, s, t1,
           t2)))))))))))))))

def no_illegal_updates_code(x0: List[(Nat.nat, AExp.aexp)], uu: Nat.nat):
      Boolean
  =
  (x0, uu) match {
  case (Nil, uu) => true
  case ((ra, u) :: t, r) =>
    (! (Nat.equal_nata(r, ra))) && (no_illegal_updates_code(t, r))
}

} /* object Code_Generation */

object Store_Reuse_Subsumption {

def stored_reused_aux_per_reg(ta: Transition.transition_ext[Unit],
                               t: Transition.transition_ext[Unit], r: Nat.nat,
                               p: Nat.nat):
      Option[(Nat.nat, Nat.nat)]
  =
  (if (Nat.equal_nata(r, Nat.zero_nata))
    (if (Store_Reuse.is_generalised_output_of(ta, t, Nat.zero_nata, p))
      Some[(Nat.nat, Nat.nat)]((Nat.zero_nata, p)) else None)
    else (if (Store_Reuse.is_generalised_output_of(ta, t,
            Nat.Suc(Nat.minus_nat(r, Nat.Nata((1)))), p))
           Some[(Nat.nat,
                  Nat.nat)]((Nat.Suc(Nat.minus_nat(r, Nat.Nata((1)))), p))
           else stored_reused_aux_per_reg(ta, t,
   Nat.minus_nat(r, Nat.Nata((1))), p)))

def stored_reused_aux(ta: Transition.transition_ext[Unit],
                       t: Transition.transition_ext[Unit], r: Nat.nat,
                       p: Nat.nat):
      Option[(Nat.nat, Nat.nat)]
  =
  (if (Nat.equal_nata(p, Nat.zero_nata))
    stored_reused_aux_per_reg(ta, t, r, Nat.zero_nata)
    else (stored_reused_aux_per_reg(ta, t, r,
                                     Nat.Suc(Nat.minus_nat(p, Nat.Nata((1)))))
            match {
            case None =>
              stored_reused_aux(ta, t, r, Nat.minus_nat(p, Nat.Nata((1))))
            case Some(a) => Some[(Nat.nat, Nat.nat)](a)
          }))

def stored_reused(ta: Transition.transition_ext[Unit],
                   t: Transition.transition_ext[Unit]):
      Option[(Nat.nat, Nat.nat)]
  =
  stored_reused_aux(ta, t,
                     Orderings.max[Nat.nat](Transition.total_max_reg(t),
     Transition.total_max_reg(ta)),
                     Orderings.max[Nat.nat](Nat.Nata((Transition.Outputs[Unit](t)).length),
     Nat.Nata((Transition.Outputs[Unit](ta)).length)))

def input_i_stored_in_reg(ta: Transition.transition_ext[Unit],
                           t: Transition.transition_ext[Unit], i: Nat.nat,
                           r: Nat.nat):
      Option[(Nat.nat, Nat.nat)]
  =
  (if (Nat.equal_nata(r, Nat.zero_nata))
    (if (Store_Reuse.is_generalisation_of(ta, t, i, Nat.zero_nata))
      Some[(Nat.nat, Nat.nat)]((i, Nat.zero_nata)) else None)
    else (if (Store_Reuse.is_generalisation_of(ta, t, i,
        Nat.Suc(Nat.minus_nat(r, Nat.Nata((1))))))
           Some[(Nat.nat,
                  Nat.nat)]((i, Nat.Suc(Nat.minus_nat(r, Nat.Nata((1))))))
           else input_i_stored_in_reg(ta, t, i,
                                       Nat.minus_nat(r, Nat.Nata((1))))))

def input_stored_in_reg_aux(ta: Transition.transition_ext[Unit],
                             t: Transition.transition_ext[Unit], i: Nat.nat,
                             r: Nat.nat):
      Option[(Nat.nat, Nat.nat)]
  =
  (if (Nat.equal_nata(i, Nat.zero_nata))
    input_i_stored_in_reg(ta, t, Nat.zero_nata, r)
    else (input_i_stored_in_reg(ta, t, Nat.Suc(Nat.minus_nat(i, Nat.Nata((1)))),
                                 r)
            match {
            case None =>
              input_i_stored_in_reg(ta, t, Nat.minus_nat(i, Nat.Nata((1))), r)
            case Some((ia, ra)) => Some[(Nat.nat, Nat.nat)]((ia, ra))
          }))

def input_stored_in_reg(ta: Transition.transition_ext[Unit],
                         t: Transition.transition_ext[Unit],
                         e: FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Option[(Nat.nat, Nat.nat)]
  =
  (input_stored_in_reg_aux(ta, t, Inference.total_max_reg(e),
                            Orderings.max[Nat.nat](Transition.Arity[Unit](t),
            Transition.Arity[Unit](ta)))
     match {
     case None => None
     case Some((i, r)) =>
       (if (Nat.equal_nata(Nat.Nata((Lista.filter[(Nat.nat,
            AExp.aexp)](((a: (Nat.nat, AExp.aexp)) =>
                          {
                            val (ra, _): (Nat.nat, AExp.aexp) = a;
                            Nat.equal_nata(ra, r)
                          }),
                         Transition.Updates[Unit](ta))).length),
                            Nat.Nata((1))))
         Some[(Nat.nat, Nat.nat)]((i, r)) else None)
   })

def updates_subset(ta: Transition.transition_ext[Unit],
                    t: Transition.transition_ext[Unit],
                    e: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]):
      Boolean
  =
  (input_stored_in_reg(t, ta, e) match {
     case None => false
     case Some((i, r)) =>
       (Nat.equal_nata(Transition.Arity[Unit](t),
                        Transition.Arity[Unit](ta))) && ((Set.less_set[GExp.gexp](Set.seta[GExp.gexp](Transition.Guard[Unit](t)),
   Set.seta[GExp.gexp](Transition.Guard[Unit](ta)))) && ((! ((Lista.map[(Nat.nat,
                                  AExp.aexp),
                                 Nat.nat](((a: (Nat.nat, AExp.aexp)) => a._1),
   Lista.removeAll[(Nat.nat,
                     AExp.aexp)]((r, AExp.V(VName.I(i))),
                                  Transition.Updates[Unit](t)))) contains r)) && ((! ((Lista.map[(Nat.nat,
                   AExp.aexp),
                  Nat.nat](((a: (Nat.nat, AExp.aexp)) => a._1),
                            Transition.Updates[Unit](ta))) contains r)) && ((Option_Lexorder.less_option[Nat.nat](GExp.max_input_list(Transition.Guard[Unit](ta)),
                                   Some[Nat.nat](Transition.Arity[Unit](ta)))) && ((Inference.satisfiable_list(Inference.smart_not_null(Lista.upt(Nat.zero_nata,
                           Transition.Arity[Unit](ta)),
                 Transition.Guard[Unit](ta)))) && ((Optiona.is_none[Nat.nat](GExp.max_reg_list(Transition.Guard[Unit](ta)))) && (Nat.less_nat(i,
                       Transition.Arity[Unit](ta)))))))))
   })

def no_illegal_updates[A](t: Transition.transition_ext[A], r: Nat.nat): Boolean
  =
  Code_Generation.no_illegal_updates_code(Transition.Updates[A](t), r)

def possibly_not_value(e_1: FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                        e_2: FSet.fset[(Nat.nat,
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                        s_1: Nat.nat, s_2: Nat.nat,
                        t_2: Transition.transition_ext[Unit],
                        t_1: Transition.transition_ext[Unit]):
      Boolean
  =
  (stored_reused(t_2, t_1) match {
     case None => false
     case Some((r, p)) =>
       ((Transition.Outputs[Unit](t_1))(Code_Numeral.integer_of_nat(p).toInt)
          match {
          case AExp.L(v) =>
            (Nat.less_nat(p, Nat.Nata((Transition.Outputs[Unit](t_1)).length))) && (Dirties.possiblyNotValueCtx[Unit](v,
                                       r, t_1, s_2, e_2, s_1, e_1))
          case AExp.V(_) => false
          case AExp.Plus(_, _) => false
          case AExp.Minus(_, _) => false
        })
   })

def initially_undefined_context_check(e:
FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                       r: Nat.nat, s: Nat.nat):
      Boolean
  =
  (if ((Nat.equal_nata(s, Nat.zero_nata)) && (FSet.fBall[(Nat.nat,
                   ((Nat.nat, Nat.nat),
                     Transition.transition_ext[Unit]))](e,
                 ((a: (Nat.nat,
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                    =>
                   {
                     val (_, aa):
                           (Nat.nat,
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))
                       = a
                     val (ab, b):
                           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                       = aa;
                     ({
                        val (_, to): (Nat.nat, Nat.nat) = ab;
                        ((_: Transition.transition_ext[Unit]) =>
                          ! (Nat.equal_nata(to, Nat.zero_nata)))
                      })(b)
                   }))))
    true else Dirties.initiallyUndefinedContextCheck(e, r, s))

def generalise_output_direct_subsumption(ta: Transition.transition_ext[Unit],
  t: Transition.transition_ext[Unit],
  ea: FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
  e: FSet.fset[(Nat.nat,
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
  sa: Nat.nat, s: Nat.nat):
      Boolean
  =
  (stored_reused(ta, t) match {
     case None => false
     case Some((r, p)) =>
       ((Transition.Outputs[Unit](t))(Code_Numeral.integer_of_nat(p).toInt)
          match {
          case AExp.L(v) =>
            Dirties.generaliseOutputContextCheck(v, r, sa, s, ea, e)
          case AExp.V(_) => false
          case AExp.Plus(_, _) => false
          case AExp.Minus(_, _) => false
        })
   })

def drop_guard_add_update_direct_subsumption(ta:
       Transition.transition_ext[Unit],
      t: Transition.transition_ext[Unit],
      e: FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
      s: Nat.nat):
      Boolean
  =
  (input_stored_in_reg(ta, t, e) match {
     case None => false
     case Some((_, r)) =>
       (if (no_illegal_updates[Unit](t, r))
         initially_undefined_context_check(e, r, s) else false)
   })

def drop_update_add_guard_direct_subsumption(a:
       FSet.fset[(Nat.nat,
                   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
      b: FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
      sa: Nat.nat, s: Nat.nat, t1: Transition.transition_ext[Unit],
      t2: Transition.transition_ext[Unit]):
      Boolean
  =
  (input_stored_in_reg(t2, t1, a) match {
     case None => false
     case Some((_, r)) =>
       (Dirties.acceptsAndGetsUsToBoth(a, b, sa,
s)) && ((initially_undefined_context_check(b, r,
    s)) && (updates_subset(t1, t2, a)))
   })

} /* object Store_Reuse_Subsumption */

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

def i_possible_steps(e: FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      s: Nat.nat, r: Map[Nat.nat, Option[Value.value]],
                      l: String, i: List[Value.value]):
      FSet.fset[(Nat.nat, (Nat.nat, Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (Nat.nat,
                 (Nat.nat,
                   Transition.transition_ext[Unit]))](((a:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, aa):
                        (Nat.nat,
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
               FSet.ffilter[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))](((a:
                               (Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])))
                              =>
                             {
                               val (_, aa):
                                     (Nat.nat,
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

def i_step(tr: List[(String, List[Value.value])],
            e: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))],
            s: Nat.nat, r: Map[Nat.nat, Option[Value.value]], l: String,
            i: List[Value.value]):
      Option[(Transition.transition_ext[Unit],
               (Nat.nat, (Nat.nat, Map[Nat.nat, Option[Value.value]])))]
  =
  {
    val poss_steps:
          FSet.fset[(Nat.nat, (Nat.nat, Transition.transition_ext[Unit]))]
      = i_possible_steps(e, s, r, l, i)
    val possibilities:
          FSet.fset[(Nat.nat, (Nat.nat, Transition.transition_ext[Unit]))]
      = FSet.ffilter[(Nat.nat,
                       (Nat.nat,
                         Transition.transition_ext[Unit]))](((a:
                        (Nat.nat, (Nat.nat, Transition.transition_ext[Unit])))
                       =>
                      {
                        val (_, (sa, t)):
                              (Nat.nat,
                                (Nat.nat, Transition.transition_ext[Unit]))
                          = a;
                        EFSM.accepts(Inference.tm(e), sa,
                                      EFSM.apply_updates(Transition.Updates[Unit](t),
                  AExp.join_ir(i, r), r),
                                      tr)
                      }),
                     poss_steps);
    (Dirties.randomMember[(Nat.nat,
                            (Nat.nat,
                              Transition.transition_ext[Unit]))](possibilities)
       match {
       case None => None
       case Some((u, (sa, t))) =>
         Some[(Transition.transition_ext[Unit],
                (Nat.nat,
                  (Nat.nat,
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
                                    Lista.filter[GExp.gexp](((g: GExp.gexp) =>
                      ! (GExp.gexp_constrains(g, AExp.V(VName.I(inputX))))),
                     Transition.Guard[Unit](t)),
                                    Transition.Outputs[Unit](t),
                                    (outputX, AExp.V(VName.I(inputX))) ::
                                      Transition.Updates[Unit](t),
                                    ())

def generalise_transitions(x0: List[((((Transition.transition_ext[Unit],
 Nat.nat),
(ioTag, Nat.nat)),
                                       ((Transition.transition_ext[Unit],
  Nat.nat),
 (ioTag, Nat.nat))),
                                      (((Transition.transition_ext[Unit],
  Nat.nat),
 (ioTag, Nat.nat)),
((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))],
                            e: FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (x0, e) match {
  case (Nil, e) => e
  case (h :: t, e) =>
    {
      val a: ((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))),
               (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], Nat.nat),
                   (ioTag, Nat.nat))))
        = h
      val (aa, b):
            ((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
               ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))),
              (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
        = a;
      ({
         val (ab, ba):
               (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
           = aa;
         ({
            val (ac, bb):
                  ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
              = ab;
            ({
               val (orig1, _): (Transition.transition_ext[Unit], Nat.nat) = ac;
               ((_: (ioTag, Nat.nat)) =>
                 (ad: ((Transition.transition_ext[Unit], Nat.nat),
                        (ioTag, Nat.nat)))
                   =>
                 {
                   val (ae, bc):
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (ioTag, Nat.nat))
                     = ad;
                   ({
                      val (orig2, _): (Transition.transition_ext[Unit], Nat.nat)
                        = ae;
                      ((_: (ioTag, Nat.nat)) =>
                        (af: (((Transition.transition_ext[Unit], Nat.nat),
                                (ioTag, Nat.nat)),
                               ((Transition.transition_ext[Unit], Nat.nat),
                                 (ioTag, Nat.nat))))
                          =>
                        {
                          val (ag, bd):
                                (((Transition.transition_ext[Unit], Nat.nat),
                                   (ioTag, Nat.nat)),
                                  ((Transition.transition_ext[Unit], Nat.nat),
                                    (ioTag, Nat.nat)))
                            = af;
                          ({
                             val (ah, be):
                                   ((Transition.transition_ext[Unit], Nat.nat),
                                     (ioTag, Nat.nat))
                               = ag;
                             ({
                                val (gen1, _):
                                      (Transition.transition_ext[Unit], Nat.nat)
                                  = ah;
                                ((_: (ioTag, Nat.nat)) =>
                                  (ai: ((Transition.transition_ext[Unit],
  Nat.nat),
 (ioTag, Nat.nat)))
                                    =>
                                  {
                                    val (aj, bf):
  ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
                                      = ai;
                                    ({
                                       val
 (gen2, _): (Transition.transition_ext[Unit], Nat.nat) = aj;
                                       ((_: (ioTag, Nat.nat)) =>
 generalise_transitions(t, Inference.replaceAll(Inference.replaceAll(e, orig1,
                              gen1),
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

def generalise_output(t: Transition.transition_ext[Unit], regX: Nat.nat,
                       outputX: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    Transition.Guard[Unit](t),
                                    Lista.list_update[AExp.aexp](Transition.Outputs[Unit](t),
                          outputX, AExp.V(VName.R(regX))),
                                    Transition.Updates[Unit](t), ())

def strip_uids(x: (((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat)))):
      ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
        (Transition.transition_ext[Unit], (ioTag, Nat.nat)))
  =
  {
    val a: (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
             ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
      = x
    val (aa, b):
          (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
            ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
      = a;
    ({
       val (ab, ba):
             ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
         = aa;
       ({
          val (t1, _): (Transition.transition_ext[Unit], Nat.nat) = ab;
          ((ac: (ioTag, Nat.nat)) =>
            {
              val (io1, in1): (ioTag, Nat.nat) = ac;
              ((ad: ((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat)))
                 =>
                {
                  val (ae, bb):
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (ioTag, Nat.nat))
                    = ad;
                  ({
                     val (t2, _): (Transition.transition_ext[Unit], Nat.nat) =
                       ae;
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
             List[(((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat)))],
            u1: Nat.nat, u2: Nat.nat,
            old: FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val relevant:
          List[(((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], Nat.nat),
                   (ioTag, Nat.nat)))]
      = Lista.filter[(((Transition.transition_ext[Unit], Nat.nat),
                        (ioTag, Nat.nat)),
                       ((Transition.transition_ext[Unit], Nat.nat),
                         (ioTag,
                           Nat.nat)))](((a:
   (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
     ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
  =>
 {
   val (aa, b):
         (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
           ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
     = a;
   ({
      val (ab, ba):
            ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
        = aa;
      ({
         val (_, u1a): (Transition.transition_ext[Unit], Nat.nat) = ab;
         ((ac: (ioTag, Nat.nat)) =>
           {
             val (io, _): (ioTag, Nat.nat) = ac;
             ((ad: ((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)))
                =>
               {
                 val (ae, bb):
                       ((Transition.transition_ext[Unit], Nat.nat),
                         (ioTag, Nat.nat))
                   = ad;
                 ({
                    val (_, u2a): (Transition.transition_ext[Unit], Nat.nat) =
                      ae;
                    ((af: (ioTag, Nat.nat)) =>
                      {
                        val (ioa, _): (ioTag, Nat.nat) = af;
                        (equal_ioTaga(io, In())) && ((equal_ioTaga(ioa,
                            Out())) && ((Nat.equal_nata(u1,
                 u1a)) || ((Nat.equal_nata(u2,
    u1a)) || ((Nat.equal_nata(u1, u2a)) || (Nat.equal_nata(u2, u2a))))))
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
          List[(((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], Nat.nat),
                   (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat))),
                   (((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat)),
                     ((Transition.transition_ext[Unit], Nat.nat),
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
   ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
=>
                                       {
 val (aa, b):
       (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
         ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
   = a;
 ({
    val (ab, ba): ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
      = aa;
    ({
       val (t1, u1a): (Transition.transition_ext[Unit], Nat.nat) = ab;
       ((ac: (ioTag, Nat.nat)) =>
         {
           val (io1, inx1): (ioTag, Nat.nat) = ac;
           ((ad: ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
              =>
             {
               val (ae, bb):
                     ((Transition.transition_ext[Unit], Nat.nat),
                       (ioTag, Nat.nat))
                 = ad;
               ({
                  val (t2, u2a): (Transition.transition_ext[Unit], Nat.nat) =
                    ae;
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
          List[((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat))))]
      = (relevant zip replacements)
    val stripped_replacements:
          List[((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                 (Transition.transition_ext[Unit], (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat))),
                   ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                     (Transition.transition_ext[Unit],
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
   ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
=>
                                       strip_uids(a)),
                                      replacements)
    val to_replace:
          List[((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat))))]
      = Lista.filter[((((Transition.transition_ext[Unit], Nat.nat),
                         (ioTag, Nat.nat)),
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (ioTag, Nat.nat))),
                       (((Transition.transition_ext[Unit], Nat.nat),
                          (ioTag, Nat.nat)),
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (ioTag,
                             Nat.nat))))](((a:
      ((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
         ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))),
        (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
          ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))))
     =>
    {
      val (_, s):
            ((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
               ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))),
              (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
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
      else Some[FSet.fset[(Nat.nat,
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
                                    (outputX, AExp.V(VName.I(inputX))) ::
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
                                    Lista.map[GExp.gexp,
       GExp.gexp](((g: GExp.gexp) =>
                    (g match {
                       case GExp.Bc(_) => g
                       case GExp.Eq(AExp.L(_), _) => g
                       case GExp.Eq(AExp.V(VName.I(ia)), AExp.L(_)) =>
                         (if (Nat.equal_nata(i, ia))
                           GExp.Eq(AExp.V(VName.I(i)), AExp.V(VName.R(r)))
                           else g)
                       case GExp.Eq(AExp.V(VName.I(_)), AExp.V(_)) => g
                       case GExp.Eq(AExp.V(VName.I(_)), AExp.Plus(_, _)) => g
                       case GExp.Eq(AExp.V(VName.I(_)), AExp.Minus(_, _)) => g
                       case GExp.Eq(AExp.V(VName.R(_)), _) => g
                       case GExp.Eq(AExp.Plus(_, _), _) => g
                       case GExp.Eq(AExp.Minus(_, _), _) => g
                       case GExp.Gt(_, _) => g
                       case GExp.Null(_) => g
                       case GExp.In(_, _) => g
                       case GExp.Nor(_, _) => g
                     })),
                   Transition.Guard[Unit](t)),
                                    Transition.Outputs[Unit](t),
                                    Transition.Updates[Unit](t), ())

def modify_2(matches:
               List[(((Transition.transition_ext[Unit], Nat.nat),
                       (ioTag, Nat.nat)),
                      ((Transition.transition_ext[Unit], Nat.nat),
                        (ioTag, Nat.nat)))],
              u1: Nat.nat, u2: Nat.nat,
              old: FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val relevant:
          List[(((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], Nat.nat),
                   (ioTag, Nat.nat)))]
      = Lista.filter[(((Transition.transition_ext[Unit], Nat.nat),
                        (ioTag, Nat.nat)),
                       ((Transition.transition_ext[Unit], Nat.nat),
                         (ioTag,
                           Nat.nat)))](((a:
   (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
     ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
  =>
 {
   val (aa, b):
         (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
           ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
     = a;
   ({
      val (ab, ba):
            ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
        = aa;
      ({
         val (_, u1a): (Transition.transition_ext[Unit], Nat.nat) = ab;
         ((ac: (ioTag, Nat.nat)) =>
           {
             val (io, _): (ioTag, Nat.nat) = ac;
             ((ad: ((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)))
                =>
               {
                 val (ae, bb):
                       ((Transition.transition_ext[Unit], Nat.nat),
                         (ioTag, Nat.nat))
                   = ad;
                 ({
                    val (_, u2a): (Transition.transition_ext[Unit], Nat.nat) =
                      ae;
                    ((af: (ioTag, Nat.nat)) =>
                      {
                        val (ioa, _): (ioTag, Nat.nat) = af;
                        (equal_ioTaga(io, In())) && ((equal_ioTaga(ioa,
                            In())) && ((Nat.equal_nata(u1,
                u1a)) || ((Nat.equal_nata(u2,
   u1a)) || ((Nat.equal_nata(u1, u2a)) || (Nat.equal_nata(u2, u2a))))))
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
          List[(((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], Nat.nat),
                   (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat))),
                   (((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat)),
                     ((Transition.transition_ext[Unit], Nat.nat),
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
   ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
=>
                                       {
 val (aa, b):
       (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
         ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
   = a;
 ({
    val (ab, ba): ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
      = aa;
    ({
       val (t1, u1a): (Transition.transition_ext[Unit], Nat.nat) = ab;
       ((ac: (ioTag, Nat.nat)) =>
         {
           val (io1, inx1): (ioTag, Nat.nat) = ac;
           ((ad: ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
              =>
             {
               val (ae, bb):
                     ((Transition.transition_ext[Unit], Nat.nat),
                       (ioTag, Nat.nat))
                 = ad;
               ({
                  val (t2, u2a): (Transition.transition_ext[Unit], Nat.nat) =
                    ae;
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
          List[((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat))))]
      = (relevant zip replacements)
    val stripped_replacements:
          List[((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                 (Transition.transition_ext[Unit], (ioTag, Nat.nat)))]
      = Lista.map[(((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat))),
                   ((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                     (Transition.transition_ext[Unit],
                       (ioTag,
                         Nat.nat)))](((a:
 (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
   ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
=>
                                       strip_uids(a)),
                                      replacements)
    val to_replace:
          List[((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat))),
                 (((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat)),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat))))]
      = Lista.filter[((((Transition.transition_ext[Unit], Nat.nat),
                         (ioTag, Nat.nat)),
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (ioTag, Nat.nat))),
                       (((Transition.transition_ext[Unit], Nat.nat),
                          (ioTag, Nat.nat)),
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (ioTag,
                             Nat.nat))))](((a:
      ((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
         ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))),
        (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
          ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))))
     =>
    {
      val (_, s):
            ((((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
               ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))),
              (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
        = a;
      Nat.less_nat(Nat.Nata((1)),
                    structural_count(strip_uids(s), stripped_replacements))
    }),
   comparisons);
    (if (to_replace.isEmpty) None
      else Some[FSet.fset[(Nat.nat,
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
                e: FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                s: Nat.nat, r: Map[Nat.nat, Option[Value.value]],
                x4: List[(String, (List[Value.value], List[Value.value]))]):
      (Transition.transition_ext[Unit], Nat.nat)
  =
  (n, e, s, r, x4) match {
  case (n, e, s, r, h :: t) =>
    {
      val (Some((transition, (sa, (uid, updated))))):
            Option[(Transition.transition_ext[Unit],
                     (Nat.nat, (Nat.nat, Map[Nat.nat, Option[Value.value]])))]
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
                                 e: FSet.fset[(Nat.nat,
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                 t: List[(String,
   (List[Value.value], List[Value.value]))]):
      FSet.fset[(((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (ioTag, Nat.nat)))]
  =
  FSet.fimage[((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat))),
               (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], Nat.nat),
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
                             e: FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      List[(((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
             ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))]
  =
  Lista.filter[(((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
                 ((Transition.transition_ext[Unit], Nat.nat),
                   (ioTag,
                     Nat.nat)))](((a: (((Transition.transition_ext[Unit],
  Nat.nat),
 (ioTag, Nat.nat)),
((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))))
                                    =>
                                   {
                                     val (aa, b):
   (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
     ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)))
                                       = a;
                                     ({
val (e1, (_, _)): ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
  = aa;
((ab: ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))) =>
  {
    val (e2, (_, _)):
          ((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat))
      = ab;
    ! (Product_Type.equal_proda[Transition.transition_ext[Unit],
                                 Nat.nat](e1, e2))
  })
                                      })(b)
                                   }),
                                  Lista.maps[(List[(String,
             (List[Value.value], List[Value.value]))],
       FSet.fset[((Nat.nat, (ioTag, Nat.nat)), (Nat.nat, (ioTag, Nat.nat)))]),
      (((Transition.transition_ext[Unit], Nat.nat), (ioTag, Nat.nat)),
        ((Transition.transition_ext[Unit], Nat.nat),
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
                 Nat.nat),
                (ioTag, Nat.nat)),
               ((Transition.transition_ext[Unit], Nat.nat),
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
      Nat.nat =>
        Nat.nat =>
          Nat.nat =>
            (FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                ((FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit], Nat.nat),
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))))]) =>
                  Option[FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]]
  =
  ((t1: Nat.nat) => (t2: Nat.nat) => (_: Nat.nat) =>
    (newa: FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (old: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (np: (FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))]) =>
           FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (Transition.transition_ext[Unit], Nat.nat))))])
      =>
    (modify(find_intertrace_matches(l, old), t1, t2, newa) match {
       case None => None
       case Some(newEFSM) =>
         Inference.resolve_nondeterminism(Nil,
   FSet.sorted_list_of_fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit], Nat.nat),
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))))](np(newEFSM)),
   old, newEFSM,
   ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
     (d: FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
       =>
     (e: FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
       =>
     (f: (FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))]) =>
           FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (Transition.transition_ext[Unit], Nat.nat))))])
       =>
     Inference.null_modifier(a, b, c, d, e, f)),
   ((_: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
     true),
   np)
     }))

def heuristic_2(l: List[List[(String,
                               (List[Value.value], List[Value.value]))]]):
      Nat.nat =>
        Nat.nat =>
          Nat.nat =>
            (FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                ((FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit], Nat.nat),
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))))]) =>
                  Option[FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]]
  =
  ((t1: Nat.nat) => (t2: Nat.nat) => (_: Nat.nat) =>
    (newa: FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (old: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (np: (FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))]) =>
           FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (Transition.transition_ext[Unit], Nat.nat))))])
      =>
    (modify_2(find_intertrace_matches(l, old), t1, t2, newa) match {
       case None => None
       case Some(newEFSM) =>
         Inference.resolve_nondeterminism(Nil,
   FSet.sorted_list_of_fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit], Nat.nat),
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))))](Inference.nondeterministic_pairs(newEFSM)),
   old, newEFSM,
   ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
     (d: FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
       =>
     (e: FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
       =>
     (f: (FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit]))]) =>
           FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (Transition.transition_ext[Unit], Nat.nat))))])
       =>
     Inference.null_modifier(a, b, c, d, e, f)),
   ((_: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
     true),
   np)
     }))

def is_generalisation_of(x: Transition.transition_ext[Unit],
                          xa: Transition.transition_ext[Unit], xb: Nat.nat,
                          xc: Nat.nat):
      Boolean
  =
  Code_Generation.is_generalisation_of(x, xa, xb, xc)

def is_generalised_output_of(ta: Transition.transition_ext[Unit],
                              t: Transition.transition_ext[Unit], r: Nat.nat,
                              p: Nat.nat):
      Boolean
  =
  Transition.equal_transition_exta[Unit](ta, generalise_output(t, r, p))

} /* object Store_Reuse */

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

def apply_updates(x0: List[(Nat.nat, AExp.aexp)],
                   uu: VName.vname => Option[Value.value],
                   newa: Map[Nat.nat, Option[Value.value]]):
      Map[Nat.nat, Option[Value.value]]
  =
  (x0, uu, newa) match {
  case (Nil, uu, newa) => newa
  case (h :: t, old, newa) =>
    (apply_updates(t, old, newa)) + ((h._1) -> (AExp.aval(h._2, old)))
}

def apply_outputs(p: List[AExp.aexp], s: VName.vname => Option[Value.value]):
      List[Option[Value.value]]
  =
  Lista.map[AExp.aexp,
             Option[Value.value]](((pa: AExp.aexp) => AExp.aval(pa, s)), p)

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
                  (sa, (apply_outputs(Transition.Outputs[Unit](t),
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

} /* object EFSM */

object Equals {

def equality_pairs(x0: List[GExp.gexp]): List[(Nat.nat, Value.value)] = x0 match
  {
  case Nil => Nil
  case GExp.Eq(AExp.V(VName.I(n)), AExp.L(l)) :: t =>
    (n, l) :: equality_pairs(t)
  case GExp.Bc(v) :: t => equality_pairs(t)
  case GExp.Eq(AExp.L(vb), va) :: t => equality_pairs(t)
  case GExp.Eq(AExp.V(VName.R(vc)), va) :: t => equality_pairs(t)
  case GExp.Eq(AExp.Plus(vb, vc), va) :: t => equality_pairs(t)
  case GExp.Eq(AExp.Minus(vb, vc), va) :: t => equality_pairs(t)
  case GExp.Eq(v, AExp.V(vb)) :: t => equality_pairs(t)
  case GExp.Eq(v, AExp.Plus(vb, vc)) :: t => equality_pairs(t)
  case GExp.Eq(v, AExp.Minus(vb, vc)) :: t => equality_pairs(t)
  case GExp.Gt(v, va) :: t => equality_pairs(t)
  case GExp.Null(v) :: t => equality_pairs(t)
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
  Nat.Nata((1))))) && (Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](t),
             List(AExp.L(EFSM.Str(List(String.Char(false, false, true, false,
            true, true, true, false),
String.Char(false, true, false, false, true, true, true, false),
String.Char(true, false, true, false, true, true, true, false),
String.Char(true, false, true, false, false, true, true, false))))))))))
  }

def gen_eq: Transition.transition_ext[Unit] =
  Transition.transition_exta[Unit]("equals",
                                    Code_Numeral.nat_of_integer(BigInt(2)),
                                    List(GExp.Eq(AExp.V(VName.I(Nat.zero_nata)),
          AExp.V(VName.I(Nat.Nata((1)))))),
                                    List(AExp.L(EFSM.Str(List(String.Char(false,
                                   false, true, false, true, true, true, false),
                       String.Char(false, true, false, false, true, true, true,
                                    false),
                       String.Char(true, false, true, false, true, true, true,
                                    false),
                       String.Char(true, false, true, false, false, true, true,
                                    false))))),
                                    Nil, ())

def equals(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
            newa: FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))],
            old: FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))],
            uu: (FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))]) =>
                  FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                ((Transition.transition_ext[Unit], Nat.nat),
                                  (Transition.transition_ext[Unit],
                                    Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID);
    (if ((is_equals(t1)) && (is_equals(t2)))
      Some[FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](Inference.replace(Inference.drop_transitions(newa,
                           FSet.finsert[Nat.nat](t2ID, FSet.bot_fset[Nat.nat])),
t1ID, gen_eq))
      else None)
  }

def gen_neq: Transition.transition_ext[Unit] =
  Transition.transition_exta[Unit]("equals",
                                    Code_Numeral.nat_of_integer(BigInt(2)),
                                    List(GExp.Eq(AExp.V(VName.I(Nat.zero_nata)),
          AExp.V(VName.I(Nat.Nata((1)))))),
                                    List(AExp.L(EFSM.Str(List(String.Char(false,
                                   false, true, false, true, true, true, false),
                       String.Char(false, true, false, false, true, true, true,
                                    false),
                       String.Char(true, false, true, false, true, true, true,
                                    false),
                       String.Char(true, false, true, false, false, true, true,
                                    false))))),
                                    Nil, ())

def not_equals(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
                newa: FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                old: FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))],
                uu: (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    ((Transition.transition_ext[Unit], Nat.nat),
                                      (Transition.transition_ext[Unit],
Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID);
    (if ((is_equals(t1)) && (is_equals(t2)))
      Some[FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](Inference.replace(Inference.drop_transitions(newa,
                           FSet.finsert[Nat.nat](t2ID, FSet.bot_fset[Nat.nat])),
t1ID, gen_neq))
      else None)
  }

} /* object Equals */

object EFSM_Dot {

def vname2dot(x0: VName.vname): String = x0 match {
  case VName.I(n) =>
    "i<sub>" +
      Code_Numeral.integer_of_nat(Nat.plus_nata(n, Nat.Nata((1)))).toString() +
      "</sub>"
  case VName.R(n) =>
    "r<sub>" + Code_Numeral.integer_of_nat(n).toString() + "</sub>"
}

def value2dot(x0: Value.value): String = x0 match {
  case Value.Str(s) => "\"" + s.replace("\\", "\\\\") + "\""
  case Value.Numa(n) => Code_Numeral.integer_of_int(n).toString()
}

def aexp2dot(x0: AExp.aexp): String = x0 match {
  case AExp.L(v) => value2dot(v)
  case AExp.V(v) => vname2dot(v)
  case AExp.Plus(a1, a2) => aexp2dot(a1) + " + " + aexp2dot(a2)
  case AExp.Minus(a1, a2) => aexp2dot(a1) + " - " + aexp2dot(a2)
}

def updates2dot_aux(l: List[(Nat.nat, AExp.aexp)]): List[String] =
  Lista.map[(Nat.nat, AExp.aexp),
             String](((a: (Nat.nat, AExp.aexp)) =>
                       {
                         val (r, u): (Nat.nat, AExp.aexp) = a;
                         vname2dot(VName.R(r)) + " := " + aexp2dot(u)
                       }),
                      l)

def updates2dot(x0: List[(Nat.nat, AExp.aexp)]): String = x0 match {
  case Nil => ""
  case v :: va => "&#91;" + (updates2dot_aux(v :: va)).mkString(", ") + "&#93;"
}

def outputs2dot(x0: List[AExp.aexp], uu: Nat.nat): List[String] = (x0, uu) match
  {
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

def gexp2dot(x0: GExp.gexp): String = x0 match {
  case GExp.Bc(true) => "True"
  case GExp.Bc(false) => "False"
  case GExp.Eq(a1, a2) => aexp2dot(a1) + " = " + aexp2dot(a2)
  case GExp.Gt(a2, a1) => aexp2dot(a1) + " &lt; " + aexp2dot(a2)
  case GExp.In(v, l) =>
    vname2dot(v) + "&isin;{" +
      (Lista.map[Value.value,
                  String](((a: Value.value) => value2dot(a)),
                           l)).mkString(", ") +
      "}"
  case GExp.Nor(g1, g2) => "!(" + gexp2dot(g1) + "&or;" + gexp2dot(g2) + ")"
  case GExp.Null(v) => aexp2dot(v) + " = NULL"
}

def guards2dot_aux(l: List[GExp.gexp]): List[String] =
  Lista.map[GExp.gexp, String](((a: GExp.gexp) => gexp2dot(a)), l)

def guards2dot(x0: List[GExp.gexp]): String = x0 match {
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

def iefsm2dot(e: FSet.fset[(Nat.nat,
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
    (Lista.map[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
                String](((a: (Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])))
                           =>
                          {
                            val (uid, aa):
                                  (Nat.nat,
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
                                   "[label=<<i> (" +
                                   Code_Numeral.integer_of_nat(uid).toString() +
                                   ")" +
                                   transition2dot(t) +
                                   "</i>>];")
                             })(b)
                          }),
                         FSet.sorted_list_of_fset[(Nat.nat,
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

def aexp2sal(x0: AExp.aexp): String = x0 match {
  case AExp.L(Value.Numa(n)) =>
    "Some(Num(" + Code_Numeral.integer_of_int(n).toString() + "))"
  case AExp.L(Value.Str(n)) =>
    "Some(Str(String__" +
      (if (n == "") "_EMPTY__" else escape(n, replacements)) +
      "))"
  case AExp.V(VName.I(i)) =>
    "Some(i(" +
      Code_Numeral.integer_of_nat(Nat.plus_nata(i, Nat.Nata((1)))).toString() +
      "))"
  case AExp.V(VName.R(i)) =>
    "r(" + Code_Numeral.integer_of_nat(i).toString() + ")"
  case AExp.Plus(a1, a2) =>
    "value_plus(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
  case AExp.Minus(a1, a2) =>
    "value_minus(" + aexp2sal(a1) + ", " + aexp2sal(a2) + ")"
}

def gexp2sal(x0: GExp.gexp): String = x0 match {
  case GExp.Bc(true) => "True"
  case GExp.Bc(false) => "False"
  case GExp.Eq(a1, a2) =>
    "gval(value_eq(" + aexp2sal(a1) + ", " + aexp2sal(a2) + "))"
  case GExp.Gt(a2, a1) =>
    "gval(value_lt(" + aexp2sal(a1) + ", " + aexp2sal(a2) + "))"
  case GExp.In(v, l) =>
    (Lista.map[Value.value,
                String](((la: Value.value) =>
                          "gval(value_eq(" + aexp2sal(AExp.V(v)) + ", " +
                            aexp2sal(AExp.L(la)) +
                            "))"),
                         l)).mkString(" OR ")
  case GExp.Nor(g1, g2) =>
    "NOT (gval(" + gexp2sal(g1) + ") OR gval( " + gexp2sal(g2) + "))"
  case GExp.Null(a1) => "a1 = None"
}

def guards2sal(x0: List[GExp.gexp]): String = x0 match {
  case Nil => "TRUE"
  case v :: va =>
    (Lista.map[GExp.gexp,
                String](((a: GExp.gexp) => gexp2sal(a)),
                         v :: va)).mkString(" AND ")
}

} /* object efsm2sal */

object Finite_Set {

def card[A : HOL.equal](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.seta(xs) => Nat.Nata((xs.distinct).length)
}

} /* object Finite_Set */

object Same_Register {

def updates(x0: List[(Nat.nat, AExp.aexp)]): Option[VName.vname] = x0 match {
  case List((n, a)) => Some[VName.vname](VName.R(n))
  case Nil => None
  case v :: vb :: vc => None
}

def a_replace_with(x0: AExp.aexp, uu: Nat.nat, uv: Nat.nat): AExp.aexp =
  (x0, uu, uv) match {
  case (AExp.L(v), uu, uv) => AExp.L(v)
  case (AExp.V(v), r1, r2) =>
    (if (VName.equal_vnamea(v, VName.R(r1))) AExp.V(VName.R(r2)) else AExp.V(v))
  case (AExp.Plus(a1, a2), r1, r2) =>
    AExp.Plus(a_replace_with(a1, r1, r2), a_replace_with(a2, r1, r2))
  case (AExp.Minus(a1, a2), r1, r2) =>
    AExp.Plus(a_replace_with(a1, r1, r2), a_replace_with(a2, r1, r2))
}

def u_replace_with(x0: (Nat.nat, AExp.aexp), r1: Nat.nat, r2: Nat.nat):
      (Nat.nat, AExp.aexp)
  =
  (x0, r1, r2) match {
  case ((r, a), r1, r2) =>
    ((if (Nat.equal_nata(r, r1)) r2 else r), a_replace_with(a, r1, r2))
}

def g_replace_with(x0: GExp.gexp, uu: Nat.nat, uv: Nat.nat): GExp.gexp =
  (x0, uu, uv) match {
  case (GExp.Bc(x), uu, uv) => GExp.Bc(x)
  case (GExp.Eq(a1, a2), r1, r2) =>
    GExp.Eq(a_replace_with(a1, r1, r2), a_replace_with(a2, r1, r2))
  case (GExp.Gt(a1, a2), r1, r2) =>
    GExp.Eq(a_replace_with(a1, r1, r2), a_replace_with(a2, r1, r2))
  case (GExp.Nor(g1, g2), r1, r2) =>
    GExp.Nor(g_replace_with(g1, r1, r2), g_replace_with(g2, r1, r2))
  case (GExp.Null(a1), r1, r2) => GExp.Null(a_replace_with(a1, r1, r2))
}

def t_replace_with(t: Transition.transition_ext[Unit], r1: Nat.nat,
                    r2: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    Lista.map[GExp.gexp,
       GExp.gexp](((g: GExp.gexp) => g_replace_with(g, r1, r2)),
                   Transition.Guard[Unit](t)),
                                    Lista.map[AExp.aexp,
       AExp.aexp](((p: AExp.aexp) => a_replace_with(p, r1, r2)),
                   Transition.Outputs[Unit](t)),
                                    Lista.map[(Nat.nat, AExp.aexp),
       (Nat.nat,
         AExp.aexp)](((u: (Nat.nat, AExp.aexp)) => u_replace_with(u, r1, r2)),
                      Transition.Updates[Unit](t)),
                                    ())

def replace_with(e: FSet.fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))],
                  r1: Nat.nat, r2: Nat.nat):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (Nat.nat,
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (u, (tf, t)):
                        (Nat.nat,
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a;
                  (u, (tf, t_replace_with(t, r1, r2)))
                }),
               e)

def same_register(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
                   newa: FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                   old: FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                   uu: (FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]) =>
                         FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       ((Transition.transition_ext[Unit],
  Nat.nat),
 (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID)
    val ut1: Option[VName.vname] = updates(Transition.Updates[Unit](t1))
    val ut2: Option[VName.vname] = updates(Transition.Updates[Unit](t2));
    (if (Transition.same_structure(t1, t2))
      ((ut1, ut2) match {
         case (None, _) => None
         case (Some(VName.I(_)), _) => None
         case (Some(VName.R(_)), None) => None
         case (Some(VName.R(_)), Some(VName.I(_))) => None
         case (Some(VName.R(r1)), Some(VName.R(r2))) =>
           Some[FSet.fset[(Nat.nat,
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
                                      AExp.L(Value.Numa(Int.zero_int))) ::
                                      Transition.Updates[Unit](t),
                                    ())

def struct_replace_all(e: FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                        old: Transition.transition_ext[Unit],
                        newa: Transition.transition_ext[Unit]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.fimage[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
               (Nat.nat,
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((a:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                {
                  val (uid, aa):
                        (Nat.nat,
                          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                    = a
                  val (ab, b):
                        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])
                    = aa;
                  ({
                     val (from, dest): (Nat.nat, Nat.nat) = ab;
                     ((t: Transition.transition_ext[Unit]) =>
                       (if (Transition.same_structure(t, old))
                         (uid, ((from, dest), newa))
                         else (uid, ((from, dest), t))))
                   })(b)
                }),
               e)

def insert_increment_2(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
                        newa: FSet.fset[(Nat.nat,
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                        old: FSet.fset[(Nat.nat,
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                        np: (FSet.fset[(Nat.nat,
 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                              FSet.fset[(Nat.nat,
  ((Nat.nat, Nat.nat),
    ((Transition.transition_ext[Unit], Nat.nat),
      (Transition.transition_ext[Unit], Nat.nat))))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID);
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
    List(AExp.Plus(AExp.V(newReg), AExp.V(VName.I(Nat.zero_nata)))),
    (r, AExp.Plus(AExp.V(newReg), AExp.V(VName.I(Nat.zero_nata)))) ::
      Transition.Updates[Unit](t1),
    ())
        val newT2: Transition.transition_ext[Unit] =
          Transition.transition_exta[Unit](Transition.Label[Unit](t2),
    Transition.Arity[Unit](t2), Nil,
    List(AExp.Plus(AExp.V(newReg), AExp.V(VName.I(Nat.zero_nata)))),
    (r, AExp.Plus(AExp.V(newReg), AExp.V(VName.I(Nat.zero_nata)))) ::
      Transition.Updates[Unit](t2),
    ())
        val initialised:
              FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
          = FSet.fimage[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])),
                         (Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))](((a:
                            (Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])))
                           =>
                          {
                            val (uid, aa):
                                  (Nat.nat,
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
                                 (uid, ((from, to),
 (if (((Nat.equal_nata(to, Inference.dest(t1ID,
   newa))) || (Nat.equal_nata(to, Inference.dest(t2ID,
          newa)))) && ((! (Transition.equal_transition_exta[Unit](t,
                           t1))) && (! (Transition.equal_transition_exta[Unit](t,
t2)))))
   initialiseReg(t, r) else t))))
                             })(b)
                          }),
                         newa)
        val newEFSM:
              FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))]
          = struct_replace_all(struct_replace_all(initialised, t2, newT2), t1,
                                newT1);
        Inference.resolve_nondeterminism(Nil,
  FSet.sorted_list_of_fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit], Nat.nat),
                                 (Transition.transition_ext[Unit],
                                   Nat.nat))))](np(newEFSM)),
  old, newEFSM,
  ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
    (d: FSet.fset[(Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (e: FSet.fset[(Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (f: (FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
          FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (Transition.transition_ext[Unit], Nat.nat))))])
      =>
    Inference.null_modifier(a, b, c, d, e, f)),
  ((_: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]) =>
    true),
  np)
      }
      else None)
  }

} /* object Increment_Reset */

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

object SelectionStrategies {

def bool2nat(x0: Boolean): Nat.nat = x0 match {
  case true => Nat.Nata((1))
  case false => Nat.zero_nata
}

def naive_score(t1ID: Nat.nat, t2ID: Nat.nat,
                 e: FSet.fset[(Nat.nat,
                                ((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(e, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(e, t2ID);
    bool2nat((Transition.Label[Unit](t1) ==
               Transition.Label[Unit](t2)) && (Nat.equal_nata(Transition.Arity[Unit](t1),
                       Transition.Arity[Unit](t2))))
  }

def origin_states(t1ID: Nat.nat, t2ID: Nat.nat,
                   e: FSet.fset[(Nat.nat,
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

def naive_score_eq(t1ID: Nat.nat, t2ID: Nat.nat,
                    e: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  bool2nat(Transition.equal_transition_exta[Unit](Inference.get_by_id(e, t1ID),
           Inference.get_by_id(e, t2ID)))

def naive_score_outputs(t1ID: Nat.nat, t2ID: Nat.nat,
                         e: FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val x: Transition.transition_ext[Unit] = Inference.get_by_id(e, t1ID)
    val y: Transition.transition_ext[Unit] = Inference.get_by_id(e, t2ID);
    Nat.plus_nata(Nat.plus_nata(bool2nat(Transition.Label[Unit](x) ==
   Transition.Label[Unit](y)),
                                 bool2nat(Nat.equal_nata(Transition.Arity[Unit](x),
                  Transition.Arity[Unit](y)))),
                   bool2nat(Lista.equal_lista[AExp.aexp](Transition.Outputs[Unit](x),
                  Transition.Outputs[Unit](y))))
  }

def naive_score_comprehensive(t1ID: Nat.nat, t2ID: Nat.nat,
                               e: FSet.fset[(Nat.nat,
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val x: Transition.transition_ext[Unit] = Inference.get_by_id(e, t1ID)
    val y: Transition.transition_ext[Unit] = Inference.get_by_id(e, t2ID);
    (if ((Transition.Label[Unit](x) ==
           Transition.Label[Unit](y)) && (Nat.equal_nata(Transition.Arity[Unit](x),
                  Transition.Arity[Unit](y))))
      (if (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](x)).length),
                           Nat.Nata((Transition.Outputs[Unit](y)).length)))
        Nat.plus_nata(Finite_Set.card[GExp.gexp](Set.inf_set[GExp.gexp](Set.seta[GExp.gexp](Transition.Guard[Unit](x)),
                                 Set.seta[GExp.gexp](Transition.Guard[Unit](y)))),
                       Nat.Nata((Lista.filter[(AExp.aexp,
        AExp.aexp)](((a: (AExp.aexp, AExp.aexp)) =>
                      {
                        val (aa, b): (AExp.aexp, AExp.aexp) = a;
                        AExp.equal_aexpa(aa, b)
                      }),
                     ((Transition.Outputs[Unit](x)) zip (Transition.Outputs[Unit](y))))).length))
        else Nat.zero_nata)
      else Nat.zero_nata)
  }

def naive_score_comprehensive_eq_high(t1ID: Nat.nat, t2ID: Nat.nat,
                                       e:
 FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  {
    val x: Transition.transition_ext[Unit] = Inference.get_by_id(e, t1ID)
    val y: Transition.transition_ext[Unit] = Inference.get_by_id(e, t2ID);
    (if (Transition.equal_transition_exta[Unit](x, y))
      Code_Numeral.nat_of_integer(BigInt(100))
      else (if ((Transition.Label[Unit](x) ==
                  Transition.Label[Unit](y)) && (Nat.equal_nata(Transition.Arity[Unit](x),
                         Transition.Arity[Unit](y))))
             (if (Nat.equal_nata(Nat.Nata((Transition.Outputs[Unit](x)).length),
                                  Nat.Nata((Transition.Outputs[Unit](y)).length)))
               Nat.plus_nata(Finite_Set.card[GExp.gexp](Set.inf_set[GExp.gexp](Set.seta[GExp.gexp](Transition.Guard[Unit](x)),
Set.seta[GExp.gexp](Transition.Guard[Unit](y)))),
                              Nat.Nata((Lista.filter[(AExp.aexp,
               AExp.aexp)](((a: (AExp.aexp, AExp.aexp)) =>
                             {
                               val (aa, b): (AExp.aexp, AExp.aexp) = a;
                               AExp.equal_aexpa(aa, b)
                             }),
                            ((Transition.Outputs[Unit](x)) zip (Transition.Outputs[Unit](y))))).length))
               else Nat.zero_nata)
             else Nat.zero_nata))
  }

} /* object SelectionStrategies */
