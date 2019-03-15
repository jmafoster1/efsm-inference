object Fun {

def id[A]: A => A = ((x: A) => x)

def comp[A, B, C](f: A => B, g: C => A): C => B = ((x: C) => f(g(x)))

} /* object Fun */

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
  implicit def `Type_Inference.equal_type`: equal[Type_Inference.typea] = new
    equal[Type_Inference.typea] {
    val `HOL.equal` = (a: Type_Inference.typea, b: Type_Inference.typea) =>
      Type_Inference.equal_typea(a, b)
  }
  implicit def `Trace_Matches.equal_ioTag`: equal[Trace_Matches.ioTag] = new
    equal[Trace_Matches.ioTag] {
    val `HOL.equal` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag) =>
      Trace_Matches.equal_ioTaga(a, b)
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
  implicit def `GExp.equal_gexp`: equal[GExp.gexp] = new equal[GExp.gexp] {
    val `HOL.equal` = (a: GExp.gexp, b: GExp.gexp) => GExp.equal_gexpa(a, b)
  }
  implicit def `AExp.equal_aexp`: equal[AExp.aexp] = new equal[AExp.aexp] {
    val `HOL.equal` = (a: AExp.aexp, b: AExp.aexp) => AExp.equal_aexpa(a, b)
  }
  implicit def `Nat.equal_nat`: equal[Nat.nat] = new equal[Nat.nat] {
    val `HOL.equal` = (a: Nat.nat, b: Nat.nat) => Nat.equal_nata(a, b)
  }
}

def eq[A : equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

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
  implicit def `Trace_Matches.ord_ioTag`: ord[Trace_Matches.ioTag] = new
    ord[Trace_Matches.ioTag] {
    val `Orderings.less_eq` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag)
      => Trace_Matches.less_eq_ioTag(a, b)
    val `Orderings.less` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag) =>
      Trace_Matches.less_ioTag(a, b)
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
  implicit def `Trace_Matches.preorder_ioTag`: preorder[Trace_Matches.ioTag] =
    new preorder[Trace_Matches.ioTag] {
    val `Orderings.less_eq` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag)
      => Trace_Matches.less_eq_ioTag(a, b)
    val `Orderings.less` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag) =>
      Trace_Matches.less_ioTag(a, b)
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
  implicit def `Trace_Matches.order_ioTag`: order[Trace_Matches.ioTag] = new
    order[Trace_Matches.ioTag] {
    val `Orderings.less_eq` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag)
      => Trace_Matches.less_eq_ioTag(a, b)
    val `Orderings.less` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag) =>
      Trace_Matches.less_ioTag(a, b)
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
  implicit def `Trace_Matches.linorder_ioTag`: linorder[Trace_Matches.ioTag] =
    new linorder[Trace_Matches.ioTag] {
    val `Orderings.less_eq` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag)
      => Trace_Matches.less_eq_ioTag(a, b)
    val `Orderings.less` = (a: Trace_Matches.ioTag, b: Trace_Matches.ioTag) =>
      Trace_Matches.less_ioTag(a, b)
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
  implicit def `Nat.linorder_nat`: linorder[Nat.nat] = new linorder[Nat.nat] {
    val `Orderings.less_eq` = (a: Nat.nat, b: Nat.nat) => Nat.less_eq_nat(a, b)
    val `Orderings.less` = (a: Nat.nat, b: Nat.nat) => Nat.less_nat(a, b)
  }
}

def max[A : ord](a: A, b: A): A = (if (less_eq[A](a, b)) b else a)

def less_bool(x0: Boolean, b: Boolean): Boolean = (x0, b) match {
  case (true, b) => false
  case (false, b) => b
}

} /* object Orderings */

object Optiona {

def equal_optiona[A : HOL.equal](x0: Option[A], x1: Option[A]): Boolean =
  (x0, x1) match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => HOL.eq[A](x2, y2)
  case (None, None) => true
}

} /* object Optiona */

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

def fst[A, B](x0: (A, B)): A = x0 match {
  case (x1, x2) => x1
}

def snd[A, B](x0: (A, B)): B = x0 match {
  case (x1, x2) => x2
}

def equal_bool(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

} /* object Product_Type */

object Set {

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

def Ball[A](x0: set[A], p: A => Boolean): Boolean = (x0, p) match {
  case (seta(xs), p) => Lista.list_all[A](p, xs)
}

def image[A, B](f: A => B, x1: set[A]): set[B] = (f, x1) match {
  case (f, seta(xs)) => seta[B](Lista.map[A, B](f, xs))
}

def filter[A](p: A => Boolean, x1: set[A]): set[A] = (p, x1) match {
  case (p, seta(xs)) => seta[A](Lista.filter[A](p, xs))
}

def insert[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](Lista.removeAll[A](x, xs))
  case (x, seta(xs)) => seta[A](Lista.insert[A](x, xs))
}

def member[A : HOL.equal](x: A, xa1: set[A]): Boolean = (x, xa1) match {
  case (x, coset(xs)) => ! (xs contains x)
  case (x, seta(xs)) => xs contains x
}

def remove[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](Lista.insert[A](x, xs))
  case (x, seta(xs)) => seta[A](Lista.removeAll[A](x, xs))
}

def the_elem[A](x0: set[A]): A = x0 match {
  case seta(x::Nil) => x
}

def bot_set[A]: set[A] = seta[A](Nil)

def sup_set[A : HOL.equal](x0: set[A], a: set[A]): set[A] = (x0, a) match {
  case (coset(xs), a) =>
    coset[A](Lista.filter[A](((x: A) => ! (member[A](x, a))), xs))
  case (seta(xs), a) =>
    Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => insert[A](aa, b)), xs, a)
}

def minus_set[A : HOL.equal](a: set[A], x1: set[A]): set[A] = (a, x1) match {
  case (a, coset(xs)) =>
    seta[A](Lista.filter[A](((x: A) => member[A](x, a)), xs))
  case (a, seta(xs)) =>
    Lista.fold[A, set[A]](((aa: A) => (b: set[A]) => remove[A](aa, b)), xs, a)
}

def less_eq_set[A : HOL.equal](a: set[A], b: set[A]): Boolean = (a, b) match {
  case (coset(xs), seta(ys)) =>
    (if ((Lista.nulla[A](xs)) && (Lista.nulla[A](ys))) false
      else { sys.error("subset_eq (List.coset _) (List.set _) requires type class instance card_UNIV");
             (((_: Unit) =>
                less_eq_set[A](coset[A](xs), seta[A](ys)))).apply(())
             })
  case (a, coset(ys)) => Lista.list_all[A](((y: A) => ! (member[A](y, a))), ys)
  case (seta(xs), b) => Lista.list_all[A](((x: A) => member[A](x, b)), xs)
}

} /* object Set */

object Lista {

def nth[A](x0: List[A], n: Nat.nat): A = (x0, n) match {
  case (x::xs, n) =>
    (if (Nat.equal_nata(n, Nat.zero_nata)) x
      else nth[A](xs, Nat.minus_nat(n, Nat.one_nat)))
}

def zip[A, B](xs: List[A], ys: List[B]): List[(A, B)] = (xs, ys) match {
  case (x::xs, y::ys) => (x, y)::(zip[A, B](xs, ys))
  case (xs, Nil) => Nil
  case (Nil, ys) => Nil
}

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x::xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x::xs) => f(x) ++ maps[A, B](f, xs)
}

def nulla[A](x0: List[A]): Boolean = x0 match {
  case Nil => true
  case x::xs => false
}

def foldl[A, B](f: A => B => A, a: A, x2: List[B]): A = (f, a, x2) match {
  case (f, a, Nil) => a
  case (f, a, x::xs) => foldl[A, B](f, (f(a))(x), xs)
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => Fun.id[B]
  case (f, x::xs) => Fun.comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x::xs) => (if (p(x)) x::(filter[A](p, xs)) else filter[A](p, xs))
}

def insert[A : HOL.equal](x: A, xs: List[A]): List[A] =
  (if (xs contains x) xs else x::xs)

def ListMem[A : HOL.equal](x: A, xs: List[A]): Boolean = xs contains x

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21::x22) => (f(x21))::(map[A, B](f, x22))
}

def enumerate[A](n: Nat.nat, x1: List[A]): List[(Nat.nat, A)] = (n, x1) match {
  case (n, x::xs) => (n, x)::(enumerate[A](Nat.Suc(n), xs))
  case (n, Nil) => Nil
}

def removeAll[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y::xs) =>
    (if (HOL.eq[A](x, y)) removeAll[A](x, xs) else y::(removeAll[A](x, xs)))
}

def map_filter[A, B](f: A => Option[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x::xs) => (f(x) match {
                        case None => map_filter[A, B](f, xs)
                        case Some(y) => y::(map_filter[A, B](f, xs))
                      })
}

def list_update[A](x0: List[A], i: Nat.nat, y: A): List[A] = (x0, i, y) match {
  case (Nil, i, y) => Nil
  case (x::xs, i, y) =>
    (if (Nat.equal_nata(i, Nat.zero_nata)) y::xs
      else x::(list_update[A](xs, Nat.minus_nat(i, Nat.one_nat), y)))
}

def list_all[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x::xs) => (p(x)) && (list_all[A](p, xs))
}

def insort_key[A, B : Orderings.linorder](f: A => B, x: A, xa2: List[A]):
      List[A]
  =
  (f, x, xa2) match {
  case (f, x, Nil) => x::Nil
  case (f, x, y::ys) =>
    (if (Orderings.less_eq[B](f(x), f(y))) x::(y::ys)
      else y::(insort_key[A, B](f, x, ys)))
}

def sort_key[A, B : Orderings.linorder](f: A => B, xs: List[A]): List[A] =
  (foldr[A, List[A]](((a: A) => (b: List[A]) => insort_key[A, B](f, a, b)),
                      xs)).apply(Nil)

def equal_list[A : HOL.equal](x0: List[A], x1: List[A]): Boolean = (x0, x1)
  match {
  case (Nil, x21::x22) => false
  case (x21::x22, Nil) => false
  case (x21::x22, y21::y22) =>
    (HOL.eq[A](x21, y21)) && (equal_list[A](x22, y22))
  case (Nil, Nil) => true
}

def sorted_list_of_set[A : HOL.equal : Orderings.linorder](x0: Set.set[A]):
      List[A]
  =
  x0 match {
  case Set.seta(xs) => sort_key[A, A](((x: A) => x), xs.distinct)
}

} /* object Lista */

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

def one_nat: nat = Nata(BigInt(1))

def Suc(n: nat): nat = plus_nata(n, one_nat)

def minus_nat(m: nat, n: nat): nat =
  Nata(Orderings.max[BigInt](BigInt(0),
                              Code_Numeral.integer_of_nat(m) -
                                Code_Numeral.integer_of_nat(n)))

} /* object Nat */

object Code_Numeral {

def sgn_integer(k: BigInt): BigInt =
  (if (k == BigInt(0)) BigInt(0)
    else (if (k < BigInt(0)) BigInt(-1) else BigInt(1)))

def divmod_integer(k: BigInt, l: BigInt): (BigInt, BigInt) =
  (if (k == BigInt(0)) (BigInt(0), BigInt(0))
    else (if (l == BigInt(0)) (BigInt(0), k)
           else (Fun.comp[BigInt, ((BigInt, BigInt)) => (BigInt, BigInt),
                           BigInt](Fun.comp[BigInt => BigInt,
     ((BigInt, BigInt)) => (BigInt, BigInt),
     BigInt](((a: BigInt => BigInt) => (b: (BigInt, BigInt)) =>
               Product_Type.apsnd[BigInt, BigInt, BigInt](a, b)),
              ((a: BigInt) => (b: BigInt) => a * b)),
                                    ((a: BigInt) =>
                                      sgn_integer(a)))).apply(l).apply((if (sgn_integer(k) ==
                                      sgn_integer(l))
                                 ((k: BigInt) => (l: BigInt) => if (l == 0)
                                   (BigInt(0), k) else
                                   (k.abs /% l.abs)).apply(k).apply(l)
                                 else {
val (r, s): (BigInt, BigInt) =
  ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
    (k.abs /% l.abs)).apply(k).apply(l);
(if (s == BigInt(0)) ((- r), BigInt(0)) else ((- r) - BigInt(1), l.abs - s))
                                      }))))

def integer_of_nat(x0: Nat.nat): BigInt = x0 match {
  case Nat.Nata(x) => x
}

def nat_of_integer(k: BigInt): Nat.nat =
  Nat.Nata(Orderings.max[BigInt](BigInt(0), k))

def integer_of_int(x0: Int.int): BigInt = x0 match {
  case Int.int_of_integer(k) => k
}

def divide_integer(k: BigInt, l: BigInt): BigInt =
  Product_Type.fst[BigInt, BigInt](divmod_integer(k, l))

def modulo_integer(k: BigInt, l: BigInt): BigInt =
  Product_Type.snd[BigInt, BigInt](divmod_integer(k, l))

} /* object Code_Numeral */

object Int {

abstract sealed class int
final case class int_of_integer(a: BigInt) extends int

def nat(k: int): Nat.nat =
  Nat.Nata(Orderings.max[BigInt](BigInt(0), Code_Numeral.integer_of_int(k)))

def less_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) < Code_Numeral.integer_of_int(l)

def plus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) +
                   Code_Numeral.integer_of_int(l))

def zero_int: int = int_of_integer(BigInt(0))

def equal_int(k: int, l: int): Boolean =
  Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

def minus_int(k: int, l: int): int =
  int_of_integer(Code_Numeral.integer_of_int(k) -
                   Code_Numeral.integer_of_int(l))

def uminus_int(k: int): int =
  int_of_integer((- (Code_Numeral.integer_of_int(k))))

} /* object Int */

object Option_Logic {

abstract sealed class trilean
final case class truea() extends trilean
final case class falsea() extends trilean
final case class invalid() extends trilean

def maybe_or(x0: trilean, uu: trilean): trilean = (x0, uu) match {
  case (invalid(), uu) => invalid()
  case (truea(), invalid()) => invalid()
  case (falsea(), invalid()) => invalid()
  case (truea(), truea()) => truea()
  case (truea(), falsea()) => truea()
  case (falsea(), truea()) => truea()
  case (falsea(), falsea()) => falsea()
}

def maybe_not(x0: trilean): trilean = x0 match {
  case truea() => falsea()
  case falsea() => truea()
  case invalid() => invalid()
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

} /* object Option_Logic */

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

def ValueEq(a: Option[value], b: Option[value]): Option_Logic.trilean =
  (if (Optiona.equal_optiona[value](a, b)) Option_Logic.truea()
    else Option_Logic.falsea())

def MaybeBoolInt(f: Int.int => Int.int => Boolean, uv: Option[value],
                  uw: Option[value]):
      Option_Logic.trilean
  =
  (f, uv, uw) match {
  case (f, Some(Numa(a)), Some(Numa(b))) =>
    (if ((f(a))(b)) Option_Logic.truea() else Option_Logic.falsea())
  case (uu, None, uw) => Option_Logic.invalid()
  case (uu, Some(Str(va)), uw) => Option_Logic.invalid()
  case (uu, uv, None) => Option_Logic.invalid()
  case (uu, uv, Some(Str(va))) => Option_Logic.invalid()
}

def ValueGt(a: Option[value], b: Option[value]): Option_Logic.trilean =
  MaybeBoolInt(((x: Int.int) => (y: Int.int) => Int.less_int(y, x)), a, b)

def less_value(x0: value, x1: value): Boolean = (x0, x1) match {
  case (Numa(n), Str(s)) => true
  case (Str(s), Numa(n)) => false
  case (Str(n), Str(s)) => n < s
  case (Numa(n), Numa(s)) => Int.less_int(n, s)
}

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

def value_minus(uu: Option[Value.value], uv: Option[Value.value]):
      Option[Value.value]
  =
  (uu, uv) match {
  case (Some(Value.Numa(x)), Some(Value.Numa(y))) =>
    Some[Value.value](Value.Numa(Int.minus_int(x, y)))
  case (None, uv) => None
  case (Some(Value.Str(va)), uv) => None
  case (uu, None) => None
  case (uu, Some(Value.Str(va))) => None
}

def value_plus(uu: Option[Value.value], uv: Option[Value.value]):
      Option[Value.value]
  =
  (uu, uv) match {
  case (Some(Value.Numa(x)), Some(Value.Numa(y))) =>
    Some[Value.value](Value.Numa(Int.plus_int(x, y)))
  case (None, uv) => None
  case (Some(Value.Str(va)), uv) => None
  case (uu, None) => None
  case (uu, Some(Value.Str(va))) => None
}

def aval(x0: aexp, s: VName.vname => Option[Value.value]): Option[Value.value] =
  (x0, s) match {
  case (L(x), s) => Some[Value.value](x)
  case (V(x), s) => s(x)
  case (Plus(a_1, a_2), s) => value_plus(aval(a_1, s), aval(a_2, s))
  case (Minus(a_1, a_2), s) => value_minus(aval(a_1, s), aval(a_2, s))
}

def null_state[A, B]: A => Option[B] = ((_: A) => None)

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

} /* object AExp */

object GExp {

abstract sealed class gexp
final case class Bc(a: Boolean) extends gexp
final case class Eq(a: AExp.aexp, b: AExp.aexp) extends gexp
final case class Gt(a: AExp.aexp, b: AExp.aexp) extends gexp
final case class Nor(a: gexp, b: gexp) extends gexp
final case class Null(a: AExp.aexp) extends gexp

def equal_gexpa(x0: gexp, x1: gexp): Boolean = (x0, x1) match {
  case (Nor(x41, x42), Null(x5)) => false
  case (Null(x5), Nor(x41, x42)) => false
  case (Gt(x31, x32), Null(x5)) => false
  case (Null(x5), Gt(x31, x32)) => false
  case (Gt(x31, x32), Nor(x41, x42)) => false
  case (Nor(x41, x42), Gt(x31, x32)) => false
  case (Eq(x21, x22), Null(x5)) => false
  case (Null(x5), Eq(x21, x22)) => false
  case (Eq(x21, x22), Nor(x41, x42)) => false
  case (Nor(x41, x42), Eq(x21, x22)) => false
  case (Eq(x21, x22), Gt(x31, x32)) => false
  case (Gt(x31, x32), Eq(x21, x22)) => false
  case (Bc(x1), Null(x5)) => false
  case (Null(x5), Bc(x1)) => false
  case (Bc(x1), Nor(x41, x42)) => false
  case (Nor(x41, x42), Bc(x1)) => false
  case (Bc(x1), Gt(x31, x32)) => false
  case (Gt(x31, x32), Bc(x1)) => false
  case (Bc(x1), Eq(x21, x22)) => false
  case (Eq(x21, x22), Bc(x1)) => false
  case (Null(x5), Null(y5)) => AExp.equal_aexpa(x5, y5)
  case (Nor(x41, x42), Nor(y41, y42)) =>
    (equal_gexpa(x41, y41)) && (equal_gexpa(x42, y42))
  case (Gt(x31, x32), Gt(y31, y32)) =>
    (AExp.equal_aexpa(x31, y31)) && (AExp.equal_aexpa(x32, y32))
  case (Eq(x21, x22), Eq(y21, y22)) =>
    (AExp.equal_aexpa(x21, y21)) && (AExp.equal_aexpa(x22, y22))
  case (Bc(x1), Bc(y1)) => Product_Type.equal_bool(x1, y1)
}

def gval(x0: gexp, uu: VName.vname => Option[Value.value]): Option_Logic.trilean
  =
  (x0, uu) match {
  case (Bc(true), uu) => Option_Logic.truea()
  case (Bc(false), uv) => Option_Logic.falsea()
  case (Gt(a_1, a_2), s) => Value.ValueGt(AExp.aval(a_1, s), AExp.aval(a_2, s))
  case (Eq(a_1, a_2), s) => Value.ValueEq(AExp.aval(a_1, s), AExp.aval(a_2, s))
  case (Nor(a_1, a_2), s) =>
    Option_Logic.maybe_not(Option_Logic.maybe_or(gval(a_1, s), gval(a_2, s)))
  case (Null(v), s) => Value.ValueEq(AExp.aval(v, s), None)
}

def gexp_constrains(x0: gexp, uv: AExp.aexp): Boolean = (x0, uv) match {
  case (Bc(uu), uv) => false
  case (Null(a), v) => AExp.aexp_constrains(a, v)
  case (Eq(a1, a2), v) =>
    (AExp.aexp_constrains(a1, v)) || (AExp.aexp_constrains(a2, v))
  case (Gt(a1, a2), v) =>
    (AExp.aexp_constrains(a1, v)) || (AExp.aexp_constrains(a2, v))
  case (Nor(g1, g2), v) => (gexp_constrains(g1, v)) || (gexp_constrains(g2, v))
}

} /* object GExp */

object Transition {

abstract sealed class transition_ext[A]
final case class
  transition_exta[A](a: String, b: Nat.nat, c: List[GExp.gexp],
                      d: List[AExp.aexp], e: List[(VName.vname, AExp.aexp)],
                      f: A)
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
                                     arity)) && ((Lista.equal_list[GExp.gexp](guarda,
                                       guard)) && ((Lista.equal_list[AExp.aexp](outputsa,
 outputs)) && ((Lista.equal_list[(VName.vname,
                                   AExp.aexp)](updatesa,
        updates)) && (HOL.eq[A](morea, more))))))
}

def more[A](x0: transition_ext[A]): A = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => more
}

def Arity[A](x0: transition_ext[A]): Nat.nat = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => arity
}

def Guard[A](x0: transition_ext[A]): List[GExp.gexp] = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => guard
}

def Label[A](x0: transition_ext[A]): String = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => label
}

def Outputs[A](x0: transition_ext[A]): List[AExp.aexp] = x0 match {
  case transition_exta(label, arity, guard, outputs, updates, more) => outputs
}

def Updates[A](x0: transition_ext[A]): List[(VName.vname, AExp.aexp)] = x0 match
  {
  case transition_exta(label, arity, guard, outputs, updates, more) => updates
}

} /* object Transition */

object Complete_Lattices {

def Sup_set[A : HOL.equal](x0: Set.set[Set.set[A]]): Set.set[A] = x0 match {
  case Set.seta(xs) =>
    Lista.fold[Set.set[A],
                Set.set[A]](((a: Set.set[A]) => (b: Set.set[A]) =>
                              Set.sup_set[A](a, b)),
                             xs, Set.bot_set[A])
}

} /* object Complete_Lattices */

object Lattices_Big {

def Max[A : Orderings.linorder](x0: Set.set[A]): A = x0 match {
  case Set.seta(x::xs) =>
    Lista.fold[A, A](((a: A) => (b: A) => Orderings.max[A](a, b)), xs, x)
}

} /* object Lattices_Big */

object Groups_List {

def sum_list[A : Groups.monoid_add](xs: List[A]): A =
  (Lista.foldr[A, A](((a: A) => (b: A) => Groups.plus[A](a, b)),
                      xs)).apply(Groups.zero[A])

} /* object Groups_List */

object Groups_Big {

def sum[A : HOL.equal, B : Groups.comm_monoid_add](g: A => B, x1: Set.set[A]): B
  =
  (g, x1) match {
  case (g, Set.seta(xs)) =>
    Groups_List.sum_list[B](Lista.map[A, B](g, xs.distinct))
}

} /* object Groups_Big */

object FSet {

abstract sealed class fset[A]
final case class Abs_fset[A](a: Set.set[A]) extends fset[A]

def fset[A](x0: fset[A]): Set.set[A] = x0 match {
  case Abs_fset(x) => x
}

def fimage[B, A](xb: B => A, xc: fset[B]): fset[A] =
  Abs_fset[A](Set.image[B, A](xb, fset[B](xc)))

def ffUnion[A : HOL.equal](xa: fset[fset[A]]): fset[A] =
  Abs_fset[A](Complete_Lattices.Sup_set[A](Set.image[fset[A],
              Set.set[A]](((a: fset[A]) => fset[A](a)), fset[fset[A]](xa))))

def ffilter[A](xb: A => Boolean, xc: fset[A]): fset[A] =
  Abs_fset[A](Set.filter[A](xb, fset[A](xc)))

def finsert[A : HOL.equal](xb: A, xc: fset[A]): fset[A] =
  Abs_fset[A](Set.insert[A](xb, fset[A](xc)))

def fmember[A : HOL.equal](x: A, xc: fset[A]): Boolean =
  Set.member[A](x, fset[A](xc))

def fthe_elem[A](xa: fset[A]): A = Set.the_elem[A](fset[A](xa))

def size_fset[A : HOL.equal](x: A => Nat.nat, xc: fset[A]): Nat.nat =
  Groups_Big.sum[A, Nat.nat](Fun.comp[Nat.nat, Nat.nat,
                                       A](((a: Nat.nat) => Nat.Suc(a)), x),
                              fset[A](xc))

def fset_of_list[A](xa: List[A]): fset[A] = Abs_fset[A](Set.seta[A](xa))

def fMax[A : Orderings.linorder](xa: fset[A]): A =
  Lattices_Big.Max[A](fset[A](xa))

def sorted_list_of_fset[A : HOL.equal : Orderings.linorder](xa: fset[A]):
      List[A]
  =
  Lista.sorted_list_of_set[A](fset[A](xa))

def bot_fset[A]: fset[A] = Abs_fset[A](Set.bot_set[A])

def sup_fset[A : HOL.equal](xb: fset[A], xc: fset[A]): fset[A] =
  Abs_fset[A](Set.sup_set[A](fset[A](xb), fset[A](xc)))

def size_fseta[A : HOL.equal]: (fset[A]) => Nat.nat =
  ((a: fset[A]) => size_fset[A](((_: A) => Nat.zero_nata), a))

def less_eq_fset[A : HOL.equal](xa: fset[A], xc: fset[A]): Boolean =
  Set.less_eq_set[A](fset[A](xa), fset[A](xc))

def equal_fset[A : HOL.equal](a: fset[A], b: fset[A]): Boolean =
  (less_eq_fset[A](a, b)) && (less_eq_fset[A](b, a))

def minus_fset[A : HOL.equal](xb: fset[A], xc: fset[A]): fset[A] =
  Abs_fset[A](Set.minus_set[A](fset[A](xb), fset[A](xc)))

} /* object FSet */

object EFSM {

def apply_guards(x0: List[GExp.gexp], uu: VName.vname => Option[Value.value]):
      Boolean
  =
  (x0, uu) match {
  case (Nil, uu) => true
  case (h::t, s) =>
    (Option_Logic.equal_trilean(GExp.gval(h, s),
                                 Option_Logic.truea())) && (apply_guards(t, s))
}

def input2state(x0: List[Value.value], uu: Nat.nat):
      VName.vname => Option[Value.value]
  =
  (x0, uu) match {
  case (Nil, uu) => AExp.null_state[VName.vname, Value.value]
  case (h::t, i) =>
    ((x: VName.vname) =>
      (if (VName.equal_vnamea(x, VName.I(i))) Some[Value.value](h)
        else (input2state(t, Nat.plus_nata(i, Nat.one_nat))).apply(x)))
}

def join_ir(i: List[Value.value], r: VName.vname => Option[Value.value]):
      VName.vname => Option[Value.value]
  =
  ((a: VName.vname) =>
    (a match {
       case VName.I(n) => (input2state(i, Nat.one_nat)).apply(VName.I(n))
       case VName.R(n) => r(VName.R(n))
     }))

def possible_steps(e: FSet.fset[((Nat.nat, Nat.nat),
                                  Transition.transition_ext[Unit])],
                    s: Nat.nat, r: VName.vname => Option[Value.value],
                    l: String, i: List[Value.value]):
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
 Transition.Arity[Unit](t))) && (apply_guards(Transition.Guard[Unit](t),
       join_ir(i, r))))))
                          })(b)
                       }),
                      e))

def apply_updates(x0: List[(VName.vname, AExp.aexp)],
                   uu: VName.vname => Option[Value.value],
                   newa: VName.vname => Option[Value.value]):
      VName.vname => Option[Value.value]
  =
  (x0, uu, newa) match {
  case (Nil, uu, newa) => newa
  case (h::t, old, newa) =>
    ((x: VName.vname) =>
      (if (VName.equal_vnamea(x, Product_Type.fst[VName.vname, AExp.aexp](h)))
        AExp.aval(Product_Type.snd[VName.vname, AExp.aexp](h), old)
        else (apply_updates(t, old, newa)).apply(x)))
}

def apply_outputs(x0: List[AExp.aexp], uu: VName.vname => Option[Value.value]):
      List[Option[Value.value]]
  =
  (x0, uu) match {
  case (Nil, uu) => Nil
  case (h::t, s) => (AExp.aval(h, s))::(apply_outputs(t, s))
}

def step(e: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
          s: Nat.nat, r: VName.vname => Option[Value.value], l: String,
          i: List[Value.value]):
      Option[(Transition.transition_ext[Unit],
               (Nat.nat,
                 (List[Option[Value.value]],
                   VName.vname => Option[Value.value])))]
  =
  (if (Nat.equal_nata(FSet.size_fseta[(Nat.nat,
Transition.transition_ext[Unit])].apply(possible_steps(e, s, r, l, i)),
                       Nat.one_nat))
    {
      val (sa, t): (Nat.nat, Transition.transition_ext[Unit]) =
        FSet.fthe_elem[(Nat.nat,
                         Transition.transition_ext[Unit])](possible_steps(e, s,
                                   r, l, i));
      Some[(Transition.transition_ext[Unit],
             (Nat.nat,
               (List[Option[Value.value]],
                 VName.vname =>
                   Option[Value.value])))]((t,
     (sa, (apply_outputs(Transition.Outputs[Unit](t), join_ir(i, r)),
            apply_updates(Transition.Updates[Unit](t), join_ir(i, r), r)))))
    }
    else None)

} /* object EFSM */

object FinFun {

abstract sealed class finfun[A, B]
final case class finfun_const[B, A](a: B) extends finfun[A, B]
final case class finfun_update_code[A, B](a: finfun[A, B], b: A, c: B) extends
  finfun[A, B]

def finfun_update[A : HOL.equal, B : HOL.equal](x0: finfun[A, B], a: A, b: B):
      finfun[A, B]
  =
  (x0, a, b) match {
  case (finfun_update_code(f, aa, ba), a, b) =>
    (if (HOL.eq[A](aa, a)) finfun_update[A, B](f, aa, b)
      else finfun_update_code[A, B](finfun_update[A, B](f, a, b), aa, ba))
  case (finfun_const(ba), a, b) =>
    (if (HOL.eq[B](ba, b)) finfun_const[B, A](ba)
      else finfun_update_code[A, B](finfun_const[B, A](ba), a, b))
}

def finfun_apply[A : HOL.equal, B](x0: finfun[A, B], a: A): B = (x0, a) match {
  case (finfun_const(b), a) => b
  case (finfun_update_code(f, aa, b), a) =>
    (if (HOL.eq[A](aa, a)) b else finfun_apply[A, B](f, a))
}

} /* object FinFun */

object Euclidean_Division {

def divide_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Code_Numeral.divide_integer(Code_Numeral.integer_of_nat(m),
Code_Numeral.integer_of_nat(n)))

def modulo_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Code_Numeral.modulo_integer(Code_Numeral.integer_of_nat(m),
Code_Numeral.integer_of_nat(n)))

} /* object Euclidean_Division */

object EFSM_Dot {

def join(x0: List[String], uu: String): String = (x0, uu) match {
  case (Nil, uu) => ""
  case (a::Nil, uv) => a
  case (h::(v::va), s) => h + s + join(v::va, s)
}

def string_of_digit(n: Nat.nat): String =
  (if (Nat.equal_nata(n, Nat.zero_nata)) "0"
    else (if (Nat.equal_nata(n, Nat.one_nat)) "1"
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

def shows_string: String => String => String =
  ((a: String) => (b: String) => a + b)

def showsp_nat(p: String, n: Nat.nat): String => String =
  (if (Nat.less_nat(n, Code_Numeral.nat_of_integer(BigInt(10))))
    shows_string.apply(string_of_digit(n))
    else Fun.comp[String, String,
                   String](showsp_nat(p, Euclidean_Division.divide_nat(n,
                                Code_Numeral.nat_of_integer(BigInt(10)))),
                            shows_string.apply(string_of_digit(Euclidean_Division.modulo_nat(n,
              Code_Numeral.nat_of_integer(BigInt(10)))))))

def vname2dot(x0: VName.vname): String = x0 match {
  case VName.I(n) => "i<sub>" + (showsp_nat("", n)).apply("") + "</sub>"
  case VName.R(n) => "r<sub>" + (showsp_nat("", n)).apply("") + "</sub>"
}

def showsp_int(p: String, i: Int.int): String => String =
  (if (Int.less_int(i, Int.zero_int))
    Fun.comp[String, String,
              String](shows_string.apply("-"),
                       showsp_nat(p, Int.nat(Int.uminus_int(i))))
    else showsp_nat(p, Int.nat(i)))

def value2dot(x0: Value.value): String = x0 match {
  case Value.Str(s) => s
  case Value.Numa(n) => (showsp_int("", n)).apply("")
}

def aexp2dot(x0: AExp.aexp): String = x0 match {
  case AExp.L(v) => value2dot(v)
  case AExp.V(v) => vname2dot(v)
  case AExp.Plus(a1, a2) => aexp2dot(a1) + " + " + aexp2dot(a2)
  case AExp.Minus(a1, a2) => aexp2dot(a1) + " - " + aexp2dot(a2)
}

def updates2dot_aux(x0: List[(VName.vname, AExp.aexp)]): List[String] = x0 match
  {
  case Nil => Nil
  case h::t =>
    (vname2dot(Product_Type.fst[VName.vname, AExp.aexp](h)) + " := " +
      aexp2dot(Product_Type.snd[VName.vname,
                                 AExp.aexp](h)))::(updates2dot_aux(t))
}

def updates2dot(x0: List[(VName.vname, AExp.aexp)]): String = x0 match {
  case Nil => ""
  case v::va => "&#91;" + join(updates2dot_aux(v::va), ",") + "&#93;"
}

def outputs2dot(x0: List[AExp.aexp], uu: Nat.nat): List[String] = (x0, uu) match
  {
  case (Nil, uu) => Nil
  case (h::t, n) =>
    ("o<sub>" + (showsp_nat("", n)).apply("") + "</sub> := " +
      aexp2dot(h))::(outputs2dot(t, Nat.plus_nata(n, Nat.one_nat)))
}

def latter2dot(t: Transition.transition_ext[Unit]): String =
  {
    val l: String =
      join(outputs2dot(Transition.Outputs[Unit](t), Nat.one_nat), ",") +
        updates2dot(Transition.Updates[Unit](t));
    (if (l == "") "" else "/" + l)
  }

def gexp2dot(x0: GExp.gexp): String = x0 match {
  case GExp.Bc(true) => "True"
  case GExp.Bc(false) => "False"
  case GExp.Eq(a1, a2) => aexp2dot(a1) + " = " + aexp2dot(a2)
  case GExp.Gt(a2, a1) => aexp2dot(a1) + " &lt; " + aexp2dot(a2)
  case GExp.Nor(g1, g2) => "!(" + gexp2dot(g1) + "&or;" + gexp2dot(g2) + ")"
  case GExp.Null(v) => aexp2dot(v) + " = NULL"
}

def guards2dot_aux(x0: List[GExp.gexp]): List[String] = x0 match {
  case Nil => Nil
  case h::t => (gexp2dot(h))::(guards2dot_aux(t))
}

def guards2dot(x0: List[GExp.gexp]): String = x0 match {
  case Nil => ""
  case v::va => "&#91;" + join(guards2dot_aux(v::va), ",") + "&#93;"
}

def transition2dot(t: Transition.transition_ext[Unit]): String =
  Transition.Label[Unit](t) + ":" +
    (showsp_nat("", Transition.Arity[Unit](t))).apply("") +
    guards2dot(Transition.Guard[Unit](t)) +
    latter2dot(t)

def efsm2dot(e: FSet.fset[((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])]):
      String
  =
  "digraph EFSM{" + "\u000A" + "graph [rankdir=" + "\"" + "LR" + "\"" +
    ", fontname=" +
    "\"" +
    "Latin Modern Math" +
    "\"" +
    "];" +
    "\u000A" +
    "node [color=" +
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
    "edge [fontname=" +
    "\"" +
    "Latin Modern Math" +
    "\"" +
    "];" +
    "\u000A" +
    join(FSet.sorted_list_of_fset[String](FSet.fimage[((Nat.nat, Nat.nat),
                Transition.transition_ext[Unit]),
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
                                (showsp_nat("", from)).apply("") + "->" +
                                  (showsp_nat("", to)).apply("") +
                                  "[label=<" +
                                  transition2dot(t) +
                                  ">]")
                            })(b)
                         }),
                        e)),
          "\u000A") +
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
    join(FSet.sorted_list_of_fset[String](FSet.fimage[(Nat.nat,
                ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])),
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
                                "  " + (showsp_nat("", from)).apply("") + "->" +
                                  (showsp_nat("", to)).apply("") +
                                  "[label=<(" +
                                  (showsp_nat("", uid)).apply("") +
                                  ") " +
                                  transition2dot(t) +
                                  ">]")
                            })(b)
                         }),
                        e)),
          "\u000A") +
    "\u000A" +
    "}"

} /* object EFSM_Dot */

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
  case (GExp.Bc(b1), GExp.Eq(e1, e2)) => true
  case (GExp.Bc(b1), GExp.Gt(e1, e2)) => true
  case (GExp.Bc(b1), GExp.Nor(g1, g2)) => true
  case (GExp.Bc(b1), GExp.Null(v)) => true
  case (GExp.Eq(e1, e2), GExp.Bc(b2)) => false
  case (GExp.Eq(e1a, e2a), GExp.Eq(e1, e2)) =>
    (less_aexpr(e1a, e1)) || ((AExp.equal_aexpa(e1a,
         e1)) && (less_aexpr(e2a, e2)))
  case (GExp.Eq(e1a, e2a), GExp.Gt(e1, e2)) => true
  case (GExp.Eq(e1, e2), GExp.Nor(g1, g2)) => true
  case (GExp.Eq(e1, e2), GExp.Null(v)) => true
  case (GExp.Gt(e1, e2), GExp.Bc(b2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Eq(e1, e2)) => false
  case (GExp.Gt(e1a, e2a), GExp.Gt(e1, e2)) =>
    (less_aexpr(e1a, e1)) || ((AExp.equal_aexpa(e1a,
         e1)) && (less_aexpr(e2a, e2)))
  case (GExp.Gt(e1, e2), GExp.Nor(g1, g2)) => true
  case (GExp.Gt(e1, e2), GExp.Null(v)) => true
  case (GExp.Nor(g1, g2), GExp.Bc(b2)) => false
  case (GExp.Nor(g1, g2), GExp.Eq(e1, e2)) => false
  case (GExp.Nor(g1, g2), GExp.Gt(e1, e2)) => false
  case (GExp.Nor(g1a, g2a), GExp.Nor(g1, g2)) =>
    (less_gexpr(g1a, g1)) || ((GExp.equal_gexpa(g1a,
         g1)) && (less_gexpr(g2a, g2)))
  case (GExp.Nor(g1, g2), GExp.Null(v)) => true
  case (GExp.Null(v), GExp.Bc(b2)) => false
  case (GExp.Null(v), GExp.Eq(e1, e2)) => false
  case (GExp.Null(v), GExp.Gt(e1, e2)) => false
  case (GExp.Null(v), GExp.Nor(g1, g2)) => false
  case (GExp.Null(va), GExp.Null(v)) => less_aexp(va, v)
}

def less_eq_gexp(e1: GExp.gexp, e2: GExp.gexp): Boolean =
  (less_gexpr(e1, e2)) || (GExp.equal_gexpa(e1, e2))

def less_gexp(e1: GExp.gexp, e2: GExp.gexp): Boolean = less_gexpr(e1, e2)

} /* object GExp_Orderings */

object List_Lexorder {

def less_list[A : HOL.equal : Orderings.order](xs: List[A], x1: List[A]):
      Boolean
  =
  (xs, x1) match {
  case (x::xs, y::ys) =>
    (Orderings.less[A](x, y)) || ((HOL.eq[A](x, y)) && (less_list[A](xs, ys)))
  case (Nil, x::xs) => true
  case (xs, Nil) => false
}

} /* object List_Lexorder */

object Transition_Ordering {

def less_transition_ext[A : Orderings.linorder](t1:
          Transition.transition_ext[A],
         t2: Transition.transition_ext[A]):
      Boolean
  =
  (if (Transition.Label[A](t1) == Transition.Label[A](t2))
    (if (Nat.equal_nata(Transition.Arity[A](t1), Transition.Arity[A](t2)))
      (if (Lista.equal_list[GExp.gexp](Transition.Guard[A](t1),
Transition.Guard[A](t2)))
        (if (Lista.equal_list[AExp.aexp](Transition.Outputs[A](t1),
  Transition.Outputs[A](t2)))
          (if (Lista.equal_list[(VName.vname,
                                  AExp.aexp)](Transition.Updates[A](t1),
       Transition.Updates[A](t2)))
            Orderings.less[A](Transition.more[A](t1), Transition.more[A](t2))
            else List_Lexorder.less_list[(VName.vname,
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

object Predicate {

abstract sealed class pred[A]
final case class Seq[A](a: Unit => seq[A]) extends pred[A]

abstract sealed class seq[A]
final case class Empty[A]() extends seq[A]
final case class Insert[A](a: A, b: pred[A]) extends seq[A]
final case class Join[A](a: pred[A], b: seq[A]) extends seq[A]

def applya[A, B](f: A => pred[B], x1: seq[A]): seq[B] = (f, x1) match {
  case (f, Empty()) => Empty[B]()
  case (f, Insert(x, p)) => Join[B](f(x), Join[B](bind[A, B](p, f), Empty[B]()))
  case (f, Join(p, xq)) => Join[B](bind[A, B](p, f), applya[A, B](f, xq))
}

def bind[A, B](x0: pred[A], f: A => pred[B]): pred[B] = (x0, f) match {
  case (Seq(g), f) => Seq[B](((_: Unit) => applya[A, B](f, g(()))))
}

def member[A : HOL.equal](xa0: seq[A], x: A): Boolean = (xa0, x) match {
  case (Empty(), x) => false
  case (Insert(y, p), x) => (HOL.eq[A](x, y)) || (eval[A](p)).apply(x)
  case (Join(p, xq), x) => (eval[A](p)).apply(x) || (member[A](xq, x))
}

def eval[A : HOL.equal](x0: pred[A]): A => Boolean = x0 match {
  case Seq(f) => ((a: A) => member[A](f(()), a))
}

def holds(p: pred[Unit]): Boolean = (eval[Unit](p)).apply(())

def bot_pred[A]: pred[A] = Seq[A](((_: Unit) => Empty[A]()))

def single[A](x: A): pred[A] = Seq[A](((_: Unit) => Insert[A](x, bot_pred[A])))

def sup_pred[A](x0: pred[A], x1: pred[A]): pred[A] = (x0, x1) match {
  case (Seq(f), Seq(g)) =>
    Seq[A](((_: Unit) =>
             (f(()) match {
                case Empty() => g(())
                case Insert(x, p) => Insert[A](x, sup_pred[A](p, Seq[A](g)))
                case Join(p, xq) => adjunct[A](Seq[A](g), Join[A](p, xq))
              })))
}

def adjunct[A](p: pred[A], x1: seq[A]): seq[A] = (p, x1) match {
  case (p, Empty()) => Join[A](p, Empty[A]())
  case (p, Insert(x, q)) => Insert[A](x, sup_pred[A](q, p))
  case (p, Join(q, xq)) => Join[A](q, adjunct[A](p, xq))
}

} /* object Predicate */

object Code_Generation {

def eq_i_o[A](xa: A): Predicate.pred[A] =
  Predicate.bind[A, A](Predicate.single[A](xa),
                        ((a: A) => Predicate.single[A](a)))

def guardMatch_alt(uu: List[GExp.gexp], uv: List[GExp.gexp]): Boolean = (uu, uv)
  match {
  case ((GExp.Eq(AExp.V(VName.I(ia)), AExp.L(Value.Numa(na))))::Nil,
         (GExp.Eq(AExp.V(VName.I(i)), AExp.L(Value.Numa(n))))::Nil)
    => (Nat.equal_nata(ia, Nat.one_nat)) && (Nat.equal_nata(i, Nat.one_nat))
  case (Nil, uv) => false
  case ((GExp.Bc(vb))::va, uv) => false
  case ((GExp.Eq(AExp.L(vd), vc))::va, uv) => false
  case ((GExp.Eq(AExp.V(VName.R(ve)), vc))::va, uv) => false
  case ((GExp.Eq(AExp.Plus(vd, ve), vc))::va, uv) => false
  case ((GExp.Eq(AExp.Minus(vd, ve), vc))::va, uv) => false
  case ((GExp.Eq(vb, AExp.L(Value.Str(ve))))::va, uv) => false
  case ((GExp.Eq(vb, AExp.V(vd)))::va, uv) => false
  case ((GExp.Eq(vb, AExp.Plus(vd, ve)))::va, uv) => false
  case ((GExp.Eq(vb, AExp.Minus(vd, ve)))::va, uv) => false
  case ((GExp.Gt(vb, vc))::va, uv) => false
  case ((GExp.Nor(vb, vc))::va, uv) => false
  case ((GExp.Null(vb))::va, uv) => false
  case (v::(vb::vc), uv) => false
  case (uu, Nil) => false
  case (uu, (GExp.Bc(vb))::va) => false
  case (uu, (GExp.Eq(AExp.L(vd), vc))::va) => false
  case (uu, (GExp.Eq(AExp.V(VName.R(ve)), vc))::va) => false
  case (uu, (GExp.Eq(AExp.Plus(vd, ve), vc))::va) => false
  case (uu, (GExp.Eq(AExp.Minus(vd, ve), vc))::va) => false
  case (uu, (GExp.Eq(vb, AExp.L(Value.Str(ve))))::va) => false
  case (uu, (GExp.Eq(vb, AExp.V(vd)))::va) => false
  case (uu, (GExp.Eq(vb, AExp.Plus(vd, ve)))::va) => false
  case (uu, (GExp.Eq(vb, AExp.Minus(vd, ve)))::va) => false
  case (uu, (GExp.Gt(vb, vc))::va) => false
  case (uu, (GExp.Nor(vb, vc))::va) => false
  case (uu, (GExp.Null(vb))::va) => false
  case (uu, v::(vb::vc)) => false
}

def outputMatch_alt(uu: List[AExp.aexp], uv: List[AExp.aexp]): Boolean =
  (uu, uv) match {
  case ((AExp.L(Value.Numa(na)))::Nil, (AExp.L(Value.Numa(n)))::Nil) => true
  case (Nil, uv) => false
  case ((AExp.L(Value.Str(vc)))::va, uv) => false
  case ((AExp.V(vb))::va, uv) => false
  case ((AExp.Plus(vb, vc))::va, uv) => false
  case ((AExp.Minus(vb, vc))::va, uv) => false
  case (v::(vb::vc), uv) => false
  case (uu, Nil) => false
  case (uu, (AExp.L(Value.Str(vc)))::va) => false
  case (uu, (AExp.V(vb))::va) => false
  case (uu, (AExp.Plus(vb, vc))::va) => false
  case (uu, (AExp.Minus(vb, vc))::va) => false
  case (uu, v::(vb::vc)) => false
}

def satisfies_trace_i_i_i_i(x: List[(String,
                                      (List[Value.value], List[Value.value]))],
                             xa: FSet.fset[((Nat.nat, Nat.nat),
     Transition.transition_ext[Unit])],
                             xb: Nat.nat,
                             xc: VName.vname => Option[Value.value]):
      Predicate.pred[Unit]
  =
  Predicate.sup_pred[Unit](Predicate.bind[(List[(String,
          (List[Value.value], List[Value.value]))],
    (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
      (Nat.nat, VName.vname => Option[Value.value]))),
   Unit](Predicate.single[(List[(String,
                                  (List[Value.value], List[Value.value]))],
                            (FSet.fset[((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit])],
                              (Nat.nat,
                                VName.vname =>
                                  Option[Value.value])))]((x, (xa, (xb, xc)))),
          ((a: (List[(String, (List[Value.value], List[Value.value]))],
                 (FSet.fset[((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])],
                   (Nat.nat, VName.vname => Option[Value.value]))))
             =>
            (a match {
               case (Nil, (_, (_, _))) => Predicate.single[Unit](())
               case (_::_, _) => Predicate.bot_pred[Unit]
             }))),
                            Predicate.bind[(List[(String,
           (List[Value.value], List[Value.value]))],
     (FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
       (Nat.nat, VName.vname => Option[Value.value]))),
    Unit](Predicate.single[(List[(String,
                                   (List[Value.value], List[Value.value]))],
                             (FSet.fset[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])],
                               (Nat.nat,
                                 VName.vname =>
                                   Option[Value.value])))]((x, (xa, (xb, xc)))),
           ((a: (List[(String, (List[Value.value], List[Value.value]))],
                  (FSet.fset[((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit])],
                    (Nat.nat, VName.vname => Option[Value.value]))))
              =>
             (a match {
                case (Nil, _) => Predicate.bot_pred[Unit]
                case ((l, (i, p))::ex, (e, (s, d))) =>
                  Predicate.bind[Option[(Transition.transition_ext[Unit],
  (Nat.nat, (List[Option[Value.value]], VName.vname => Option[Value.value])))],
                                  Unit](eq_i_o[Option[(Transition.transition_ext[Unit],
                (Nat.nat,
                  (List[Option[Value.value]],
                    VName.vname =>
                      Option[Value.value])))]](EFSM.step(e, s, d, l, i)),
 ((aa: Option[(Transition.transition_ext[Unit],
                (Nat.nat,
                  (List[Option[Value.value]],
                    VName.vname => Option[Value.value])))])
    =>
   (aa match {
      case None => Predicate.bot_pred[Unit]
      case Some((_, (sa, (xd, da)))) =>
        (if (Lista.equal_list[Option[Value.value]](xd,
            Lista.map[Value.value,
                       Option[Value.value]](((ab: Value.value) =>
      Some[Value.value](ab)),
     p)))
          Predicate.bind[Unit,
                          Unit](satisfies_trace_i_i_i_i(ex, e, sa, da),
                                 ((ab: Unit) => {
          val (): Unit = ab;
          Predicate.single[Unit](())
        }))
          else Predicate.bot_pred[Unit])
    })))
              }))))

} /* object Code_Generation */

object FSet_Utils {

def fprod[A, B](xb: FSet.fset[A], xc: FSet.fset[B]): FSet.fset[(A, B)] =
  FSet.Abs_fset[(A, B)](Product_Type.product[A,
      B](FSet.fset[A](xb), FSet.fset[B](xc)))

} /* object FSet_Utils */

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
             Product_Type.snd[Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])](a)),
            t)

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

def state_nondeterminism(origin: Nat.nat,
                          nt: FSet.fset[(Nat.nat,
  (Transition.transition_ext[Unit], Nat.nat))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (Transition.transition_ext[Unit], Nat.nat))))]
  =
  (if (Nat.less_nat(FSet.size_fseta[(Nat.nat,
                                      (Transition.transition_ext[Unit],
Nat.nat))].apply(nt),
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
       FSet.minus_fset[(Nat.nat,
                         (Transition.transition_ext[Unit],
                           Nat.nat))](nt, FSet.finsert[(Nat.nat,
                 (Transition.transition_ext[Unit],
                   Nat.nat))](x, FSet.bot_fset[(Nat.nat,
         (Transition.transition_ext[Unit], Nat.nat))])))
          }),
         nt)))

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
                                  val (uid, (x, ta)):
(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
                                    = a;
                                  (Product_Type.snd[Nat.nat, Nat.nat](x),
                                    (ta, uid))
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

def choice(ta: Transition.transition_ext[Unit],
            t: Transition.transition_ext[Unit]):
      Boolean
  =
  (Transition.Label[Unit](ta) ==
    Transition.Label[Unit](t)) && ((Nat.equal_nata(Transition.Arity[Unit](ta),
            Transition.Arity[Unit](t))) && (Dirties.satisfiable(Lista.fold[GExp.gexp,
                                    GExp.gexp](((v: GExp.gexp) =>
         (va: GExp.gexp) => GExp.Nor(GExp.Nor(v, v), GExp.Nor(va, va))),
        Transition.Guard[Unit](ta) ++ Transition.Guard[Unit](t),
        GExp.Bc(true)))))

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
       val (tb, ta):
             ((Transition.transition_ext[Unit], Nat.nat),
               (Transition.transition_ext[Unit], Nat.nat))
         = ac;
       choice(Product_Type.fst[Transition.transition_ext[Unit], Nat.nat](tb),
               Product_Type.fst[Transition.transition_ext[Unit], Nat.nat](ta))
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

def replace_transition(t: FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))],
                        uid: Nat.nat, from: Nat.nat, to: Nat.nat,
                        orig: Transition.transition_ext[Unit],
                        newa: Transition.transition_ext[Unit]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.sup_fset[(Nat.nat,
                  ((Nat.nat, Nat.nat),
                    Transition.transition_ext[Unit]))](FSet.ffilter[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))](((x:
                               (Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit])))
                              =>
                             (! (Product_Type.equal_proda[(Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]](Product_Type.snd[Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])](x),
             ((from, to),
               orig)))) && (! (Product_Type.equal_proda[(Nat.nat, Nat.nat),
                 Transition.transition_ext[Unit]](Product_Type.snd[Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])](x),
           ((from, to), newa))))),
                            t),
                FSet.finsert[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]((uid,
                              ((from, to), newa)),
                             FSet.bot_fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]))

def merge_transitions(oldEFSM:
                        FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                       newEFSM:
                         FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))],
                       t1FromOld: Nat.nat, t2FromOld: Nat.nat, newFrom: Nat.nat,
                       t1NewTo: Nat.nat, t2NewTo: Nat.nat,
                       t1: Transition.transition_ext[Unit], u1: Nat.nat,
                       t2: Transition.transition_ext[Unit], u2: Nat.nat,
                       modifier:
                         Nat.nat =>
                           Nat.nat =>
                             Nat.nat =>
                               (FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 (FSet.fset[(Nat.nat,
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                   Option[FSet.fset[(Nat.nat,
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (Dirties.scalaDirectlySubsumes(tm(oldEFSM), tm(newEFSM), t1FromOld, t2,
                                      t1))
    Some[FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       Transition.transition_ext[Unit]))]](replace_transition(newEFSM,
                                       u1, newFrom, t2NewTo, t1, t2))
    else (if (Dirties.scalaDirectlySubsumes(tm(oldEFSM), tm(newEFSM), t2FromOld,
     t1, t2))
           Some[FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](replace_transition(newEFSM,
      u1, newFrom, t1NewTo, t2, t1))
           else ((((modifier(u1))(u2))(newFrom))(newEFSM))(oldEFSM)))

def deterministic(t: FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      Boolean
  =
  FSet.equal_fset[(Nat.nat,
                    ((Nat.nat, Nat.nat),
                      ((Transition.transition_ext[Unit], Nat.nat),
                        (Transition.transition_ext[Unit],
                          Nat.nat))))](nondeterministic_pairs(t),
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

def arrives(uid: Nat.nat,
             t: FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  Product_Type.snd[Nat.nat,
                    Nat.nat](Product_Type.fst[(Nat.nat, Nat.nat),
       Transition.transition_ext[Unit]](Product_Type.snd[Nat.nat,
                  ((Nat.nat, Nat.nat),
                    Transition.transition_ext[Unit])](FSet.fthe_elem[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))](FSet.ffilter[(Nat.nat,
   ((Nat.nat, Nat.nat),
     Transition.transition_ext[Unit]))](((x:
    (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
   =>
  Nat.equal_nata(Product_Type.fst[Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])](x),
                  uid)),
 t)))))

def leaves(uid: Nat.nat,
            t: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  Product_Type.fst[Nat.nat,
                    Nat.nat](Product_Type.fst[(Nat.nat, Nat.nat),
       Transition.transition_ext[Unit]](Product_Type.snd[Nat.nat,
                  ((Nat.nat, Nat.nat),
                    Transition.transition_ext[Unit])](FSet.fthe_elem[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))](FSet.ffilter[(Nat.nat,
   ((Nat.nat, Nat.nat),
     Transition.transition_ext[Unit]))](((x:
    (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
   =>
  Nat.equal_nata(Product_Type.fst[Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])](x),
                  uid)),
 t)))))

def resolve_nondeterminism(x0: List[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
((Transition.transition_ext[Unit], Nat.nat),
  (Transition.transition_ext[Unit], Nat.nat))))],
                            uu: FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            newa: FSet.fset[(Nat.nat,
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            uv: Nat.nat =>
                                  Nat.nat =>
                                    Nat.nat =>
                                      (FSet.fset[(Nat.nat,
           ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
(FSet.fset[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
  Option[FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                            check:
                              (FSet.fset[((Nat.nat, Nat.nat),
   Transition.transition_ext[Unit])]) =>
                                Boolean):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (x0, uu, newa, uv, check) match {
  case (Nil, uu, newa, uv, check) =>
    (if ((deterministic(newa)) && (check(tm(newa))))
      Some[FSet.fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit]))]](newa)
      else None)
  case ((from, ((to1, to2), ((t1, u1), (t2, u2))))::ss, oldEFSM, newEFSM, m,
         check)
    => {
         val destMerge:
               FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]
           = merge_states(arrives(u1, newEFSM), arrives(u2, newEFSM), newEFSM)
         val t1FromOld: Nat.nat = leaves(u1, oldEFSM)
         val t2FromOld: Nat.nat = leaves(u2, oldEFSM)
         val newFrom: Nat.nat = leaves(u1, destMerge)
         val t1NewTo: Nat.nat = arrives(u1, destMerge)
         val t2NewTo: Nat.nat = arrives(u2, destMerge);
         (merge_transitions(oldEFSM, destMerge, t1FromOld, t2FromOld, newFrom,
                             t1NewTo, t2NewTo, t1, u1, t2, u2, m)
            match {
            case None => resolve_nondeterminism(ss, oldEFSM, newEFSM, m, check)
            case Some(newa) =>
              {
                val newScores:
                      List[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               ((Transition.transition_ext[Unit], Nat.nat),
                                 (Transition.transition_ext[Unit], Nat.nat))))]
                  = (FSet.sorted_list_of_fset[(Nat.nat,
        ((Nat.nat, Nat.nat),
          ((Transition.transition_ext[Unit], Nat.nat),
            (Transition.transition_ext[Unit],
              Nat.nat))))](nondeterministic_pairs(newa))).reverse;
                (resolve_nondeterminism(newScores, oldEFSM, newa, m, check)
                   match {
                   case None =>
                     resolve_nondeterminism(ss, oldEFSM, newEFSM, m, check)
                   case Some(a) =>
                     Some[FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]](a)
                 })
              }
          })
       }
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
                        Option[FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
           check:
             (FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit])]) =>
               Boolean):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (Nat.equal_nata(s_1, s_2)) None
    else {
           val t: FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]
             = merge_states(s_1, s_2, e);
           resolve_nondeterminism((FSet.sorted_list_of_fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (Transition.transition_ext[Unit],
                            Nat.nat))))](nondeterministic_pairs(t))).reverse,
                                   e, t, m, check)
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
                                  Option[FSet.fset[(Nat.nat,
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                    uw: (FSet.fset[((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])]) =>
                          Boolean):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (uu, x1, uv, uw) match {
  case (uu, Nil, uv, uw) => None
  case (e, (s, (s_1, s_2))::t, m, check) =>
    (if (Nat.less_nat(Nat.zero_nata, s))
      (merge(e, s_1, s_2, m, check) match {
         case None => inference_step(e, t, m, check)
         case Some(a) =>
           Some[FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](a)
       })
      else None)
}

def score(t: FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
           rank: (FSet.fset[Transition.transition_ext[Unit]]) =>
                   (FSet.fset[Transition.transition_ext[Unit]]) => Nat.nat):
      FSet.fset[(Nat.nat, (Nat.nat, Nat.nat))]
  =
  FSet.ffilter[(Nat.nat,
                 (Nat.nat,
                   Nat.nat))](((a: (Nat.nat, (Nat.nat, Nat.nat))) =>
                                {
                                  val (score, _): (Nat.nat, (Nat.nat, Nat.nat))
                                    = a;
                                  Nat.less_nat(Nat.zero_nata, score)
                                }),
                               FSet.fimage[(Nat.nat, Nat.nat),
    (Nat.nat,
      (Nat.nat,
        Nat.nat))](((a: (Nat.nat, Nat.nat)) =>
                     {
                       val (s1, s2): (Nat.nat, Nat.nat) = a;
                       ((rank(FSet.fimage[(Nat.nat,
    (Transition.transition_ext[Unit], Nat.nat)),
   Transition.transition_ext[Unit]](((aa:
(Nat.nat, (Transition.transition_ext[Unit], Nat.nat)))
                                       =>
                                      {
val (_, (ta, _)): (Nat.nat, (Transition.transition_ext[Unit], Nat.nat)) = aa;
ta
                                      }),
                                     outgoing_transitions(s1,
                   t))))(FSet.fimage[(Nat.nat,
                                       (Transition.transition_ext[Unit],
 Nat.nat)),
                                      Transition.transition_ext[Unit]](((aa:
                                   (Nat.nat,
                                     (Transition.transition_ext[Unit],
                                       Nat.nat)))
                                  =>
                                 {
                                   val (_, (ta, _)):
 (Nat.nat, (Transition.transition_ext[Unit], Nat.nat))
                                     = aa;
                                   ta
                                 }),
                                outgoing_transitions(s2, t))),
                         (s1, s2))
                     }),
                    FSet.ffilter[(Nat.nat,
                                   Nat.nat)](((a: (Nat.nat, Nat.nat)) =>
       {
         val (aa, b): (Nat.nat, Nat.nat) = a;
         Nat.less_nat(aa, b)
       }),
      FSet_Utils.fprod[Nat.nat, Nat.nat](S(t), S(t)))))

def infer(e: FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
           r: (FSet.fset[Transition.transition_ext[Unit]]) =>
                (FSet.fset[Transition.transition_ext[Unit]]) => Nat.nat,
           m: Nat.nat =>
                Nat.nat =>
                  Nat.nat =>
                    (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        Option[FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
           check:
             (FSet.fset[((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit])]) =>
               Boolean):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (inference_step(e, (FSet.sorted_list_of_fset[(Nat.nat,
         (Nat.nat, Nat.nat))](score(e, r))).reverse,
                   m, check)
     match {
     case None => e
     case Some(newa) => infer(newa, r, m, check)
   })

def satisfies_trace(x1: List[(String, (List[Value.value], List[Value.value]))],
                     x2: FSet.fset[((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])],
                     x3: Nat.nat, x4: VName.vname => Option[Value.value]):
      Boolean
  =
  Predicate.holds(Code_Generation.satisfies_trace_i_i_i_i(x1, x2, x3, x4))

def satisfies(t: Set.set[List[(String,
                                (List[Value.value], List[Value.value]))]],
               e: FSet.fset[((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit])]):
      Boolean
  =
  Set.Ball[List[(String,
                  (List[Value.value],
                    List[Value.value]))]](t,
   ((ta: List[(String, (List[Value.value], List[Value.value]))]) =>
     satisfies_trace(ta, e, Nat.zero_nata,
                      AExp.null_state[VName.vname, Value.value])))

def make_outputs(x0: List[Value.value]): List[AExp.aexp] = x0 match {
  case Nil => Nil
  case h::t => (AExp.L(h))::(make_outputs(t))
}

def make_guard(x0: List[Value.value], uu: Nat.nat): List[GExp.gexp] = (x0, uu)
  match {
  case (Nil, uu) => Nil
  case (h::t, n) =>
    (GExp.Eq(AExp.V(VName.I(n)),
              AExp.L(h)))::(make_guard(t, Nat.plus_nata(n, Nat.one_nat)))
}

def make_branch(e: FSet.fset[((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit])],
                 uu: Nat.nat, uv: VName.vname => Option[Value.value],
                 x3: List[(String, (List[Value.value], List[Value.value]))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  (e, uu, uv, x3) match {
  case (e, uu, uv, Nil) => e
  case (e, s, r, (label, (inputs, outputs))::t) =>
    (EFSM.step(e, s, r, label, inputs) match {
       case None =>
         make_branch(FSet.finsert[((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])](((s,
                                 Nat.plus_nata(maxS(e), Nat.one_nat)),
                                Transition.transition_exta[Unit](label,
                          Nat.Nata(inputs.length),
                          make_guard(inputs, Nat.one_nat),
                          make_outputs(outputs), Nil, ())),
                               e),
                      Nat.plus_nata(maxS(e), Nat.one_nat), r, t)
       case Some((_, (sa, (_, updated)))) => make_branch(e, sa, updated, t)
     })
}

def make_pta(x0: List[List[(String, (List[Value.value], List[Value.value]))]],
              e: FSet.fset[((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  (x0, e) match {
  case (Nil, e) => e
  case (h::t, e) =>
    make_pta(t, make_branch(e, Nat.zero_nata,
                             AExp.null_state[VName.vname, Value.value], h))
}

def toiEFSM_aux(uu: Nat.nat,
                 x1: List[((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit])]):
      List[(Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (uu, x1) match {
  case (uu, Nil) => Nil
  case (n, h::t) => (n, h)::(toiEFSM_aux(Nat.plus_nata(n, Nat.one_nat), t))
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

def learn(l: List[List[(String, (List[Value.value], List[Value.value]))]],
           r: (FSet.fset[Transition.transition_ext[Unit]]) =>
                (FSet.fset[Transition.transition_ext[Unit]]) => Nat.nat,
           m: Nat.nat =>
                Nat.nat =>
                  Nat.nat =>
                    (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        Option[FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  tm(infer(toiEFSM(make_pta(l, FSet.bot_fset[((Nat.nat, Nat.nat),
       Transition.transition_ext[Unit])])),
            r, m,
            ((a: FSet.fset[((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])])
               =>
              satisfies(Set.seta[List[(String,
(List[Value.value], List[Value.value]))]](l),
                         a))))

def enumerate_aexp_regs(x0: AExp.aexp): Set.set[Nat.nat] = x0 match {
  case AExp.L(uu) => Set.bot_set[Nat.nat]
  case AExp.V(VName.R(n)) => Set.insert[Nat.nat](n, Set.bot_set[Nat.nat])
  case AExp.V(VName.I(uv)) => Set.bot_set[Nat.nat]
  case AExp.Plus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
  case AExp.Minus(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
}

def enumerate_gexp_regs(x0: GExp.gexp): Set.set[Nat.nat] = x0 match {
  case GExp.Bc(uu) => Set.bot_set[Nat.nat]
  case GExp.Null(v) => enumerate_aexp_regs(v)
  case GExp.Eq(v, va) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
  case GExp.Gt(va, v) =>
    Set.sup_set[Nat.nat](enumerate_aexp_regs(v), enumerate_aexp_regs(va))
  case GExp.Nor(v, va) =>
    Set.sup_set[Nat.nat](enumerate_gexp_regs(v), enumerate_gexp_regs(va))
}

def get_by_id_biggest_t_reg(t: Transition.transition_ext[Unit]): Nat.nat =
  Lattices_Big.Max[Nat.nat](Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Set.sup_set[Nat.nat](Set.insert[Nat.nat](Nat.zero_nata,
             Set.bot_set[Nat.nat]),
                                 Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[GExp.gexp,
                          Set.set[Nat.nat]](((a: GExp.gexp) =>
      enumerate_gexp_regs(a)),
     Transition.Guard[Unit](t))))),
            Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[AExp.aexp,
     Set.set[Nat.nat]](((a: AExp.aexp) => enumerate_aexp_regs(a)),
                        Transition.Outputs[Unit](t))))),
                               Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(VName.vname,
                         AExp.aexp),
                        Set.set[Nat.nat]](((a: (VName.vname, AExp.aexp)) =>
    {
      val (_, aa): (VName.vname, AExp.aexp) = a;
      enumerate_aexp_regs(aa)
    }),
   Transition.Updates[Unit](t))))),
          Complete_Lattices.Sup_set[Nat.nat](Set.seta[Set.set[Nat.nat]](Lista.map[(VName.vname,
    AExp.aexp),
   Set.set[Nat.nat]](((a: (VName.vname, AExp.aexp)) =>
                       {
                         val (r, _): (VName.vname, AExp.aexp) = a;
                         enumerate_aexp_regs(AExp.V(r))
                       }),
                      Transition.Updates[Unit](t))))))

def max_reg(e: FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]):
      Nat.nat
  =
  FSet.fMax[Nat.nat](FSet.fimage[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit])),
                                  Nat.nat](((a:
       (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
      =>
     {
       val (_, aa):
             (Nat.nat, ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))
         = a
       val (_, ab): ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]) = aa;
       get_by_id_biggest_t_reg(ab)
     }),
    e))

def get_by_id(e: FSet.fset[(Nat.nat,
                             ((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit]))],
               u: Nat.nat):
      Transition.transition_ext[Unit]
  =
  Product_Type.snd[(Nat.nat, Nat.nat),
                    Transition.transition_ext[Unit]](Product_Type.snd[Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])](FSet.fthe_elem[(Nat.nat,
    ((Nat.nat, Nat.nat),
      Transition.transition_ext[Unit]))](FSet.ffilter[(Nat.nat,
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
                 Nat.equal_nata(uid, u)
               }),
              e))))

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
                     val (from, to): (Nat.nat, Nat.nat) = ab;
                     ((t: Transition.transition_ext[Unit]) =>
                       (if (Transition.equal_transition_exta[Unit](t, old))
                         (uid, ((from, to), newa)) else (uid, ((from, to), t))))
                   })(b)
                }),
               e)

def null_modifier(a: Nat.nat, b: Nat.nat, c: Nat.nat,
                   d: FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                   e: FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  None

def try_heuristics(x0: List[Nat.nat =>
                              Nat.nat =>
                                Nat.nat =>
                                  (FSet.fset[(Nat.nat,
       ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                    (FSet.fset[(Nat.nat,
         ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                      Option[FSet.fset[(Nat.nat,
                 ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]]):
      Nat.nat =>
        Nat.nat =>
          Nat.nat =>
            (FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]) =>
              (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                Option[FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]]
  =
  x0 match {
  case Nil =>
    ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
      (d: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (e: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      null_modifier(a, b, c, d, e))
  case h::t =>
    ((a: Nat.nat) => (b: Nat.nat) => (c: Nat.nat) =>
      (d: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (e: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
        =>
      (((((h(a))(b))(c))(d))(e) match {
         case None =>
           (try_heuristics(t)).apply(a).apply(b).apply(c).apply(d).apply(e)
         case Some(aa) =>
           Some[FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](aa)
       }))
}

def iterative_learn_aux(x0: List[List[(String,
(List[Value.value], List[Value.value]))]],
                         e: FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                         uu: (FSet.fset[Transition.transition_ext[Unit]]) =>
                               (FSet.fset[Transition.transition_ext[Unit]]) =>
                                 Nat.nat,
                         uv: Nat.nat =>
                               Nat.nat =>
                                 Nat.nat =>
                                   (FSet.fset[(Nat.nat,
        ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                     (FSet.fset[(Nat.nat,
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                       Option[FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]],
                         uw: (FSet.fset[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])]) =>
                               Boolean):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (x0, e, uu, uv, uw) match {
  case (Nil, e, uu, uv, uw) => e
  case (h::t, e, r, m, s) =>
    iterative_learn_aux(t, infer(toiEFSM(make_branch(tm(e), Nat.zero_nata,
              AExp.null_state[VName.vname, Value.value], h)),
                                  r, m, s),
                         r, m, s)
}

def iterative_learn(l: List[List[(String,
                                   (List[Value.value], List[Value.value]))]],
                     r: (FSet.fset[Transition.transition_ext[Unit]]) =>
                          (FSet.fset[Transition.transition_ext[Unit]]) =>
                            Nat.nat,
                     m: Nat.nat =>
                          Nat.nat =>
                            Nat.nat =>
                              (FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                (FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                  Option[FSet.fset[(Nat.nat,
             ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  tm(iterative_learn_aux(l, FSet.bot_fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                          r, m,
                          ((a: FSet.fset[((Nat.nat, Nat.nat),
   Transition.transition_ext[Unit])])
                             =>
                            satisfies(Set.seta[List[(String,
              (List[Value.value], List[Value.value]))]](l),
                                       a))))

def nondeterministic(t: FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))]):
      Boolean
  =
  ! (deterministic(t))

} /* object Inference */

object Finite_Set {

def card[A : HOL.equal](x0: Set.set[A]): Nat.nat = x0 match {
  case Set.coset(xs) =>
    { sys.error("card (List.coset _) requires type class instance card_UNIV");
      (((_: Unit) => card[A](Set.coset[A](xs)))).apply(()) }
  case Set.seta(xs) => Nat.Nata((xs.distinct).length)
}

} /* object Finite_Set */

object Trace_Matches {

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
  case (a, h::t) =>
    (if (HOL.eq[A](a, h)) Nat.plus_nata(Nat.one_nat, count[A](a, t))
      else count[A](a, t))
}

def index(x0: List[Value.value], uu: Nat.nat, uv: ioTag, uw: Nat.nat):
      FSet.fset[(Nat.nat, (ioTag, Nat.nat))]
  =
  (x0, uu, uv, uw) match {
  case (Nil, uu, uv, uw) => FSet.bot_fset[(Nat.nat, (ioTag, Nat.nat))]
  case (h::t, eventNo, io, ind) =>
    FSet.finsert[(Nat.nat,
                   (ioTag,
                     Nat.nat))]((eventNo, (io, ind)),
                                 index(t, eventNo, io,
Nat.plus_nata(ind, Nat.one_nat)))
}

def i_possible_steps(e: FSet.fset[(Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit]))],
                      s: Nat.nat, r: VName.vname => Option[Value.value],
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
       Transition.Arity[Unit](t))) && (EFSM.apply_guards(Transition.Guard[Unit](t),
                  EFSM.join_ir(i, r))))))
                                })(b)
                             }),
                            e))

def i_step(e: FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
            s: Nat.nat, r: VName.vname => Option[Value.value], l: String,
            i: List[Value.value]):
      Option[(Transition.transition_ext[Unit],
               (Nat.nat, (Nat.nat, VName.vname => Option[Value.value])))]
  =
  (if (Nat.equal_nata(FSet.size_fseta[(Nat.nat,
(Nat.nat,
  Transition.transition_ext[Unit]))].apply(i_possible_steps(e, s, r, l, i)),
                       Nat.one_nat))
    {
      val (u, (sa, t)): (Nat.nat, (Nat.nat, Transition.transition_ext[Unit])) =
        FSet.fthe_elem[(Nat.nat,
                         (Nat.nat,
                           Transition.transition_ext[Unit]))](i_possible_steps(e,
s, r, l, i));
      Some[(Transition.transition_ext[Unit],
             (Nat.nat,
               (Nat.nat,
                 VName.vname =>
                   Option[Value.value])))]((t,
     (sa, (u, EFSM.apply_updates(Transition.Updates[Unit](t),
                                  EFSM.join_ir(i, r), r)))))
    }
    else None)

def lookup(x0: (Nat.nat, (ioTag, Nat.nat)),
            t: List[(String, (List[Value.value], List[Value.value]))]):
      Value.value
  =
  (x0, t) match {
  case ((eventNo, (In(), inx)), t) =>
    {
      val (_, (inputs, _)): (String, (List[Value.value], List[Value.value])) =
        Lista.nth[(String, (List[Value.value], List[Value.value]))](t, eventNo);
      Lista.nth[Value.value](inputs, inx)
    }
  case ((eventNo, (Out(), inx)), t) =>
    {
      val (_, (_, outputs)): (String, (List[Value.value], List[Value.value])) =
        Lista.nth[(String, (List[Value.value], List[Value.value]))](t, eventNo);
      Lista.nth[Value.value](outputs, inx)
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
                                    (VName.R(outputX),
                                      AExp.V(VName.I(inputX)))::(Transition.Updates[Unit](t)),
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
  case (h::t, e) =>
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

def distinct_aux(x0: List[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))],
                  d: FSet.fset[((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit])]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (x0, d) match {
  case (Nil, d) => Inference.toiEFSM(d)
  case (h::t, d) =>
    (if (FSet.fmember[((Nat.nat, Nat.nat),
                        Transition.transition_ext[Unit])](Product_Type.snd[Nat.nat,
                                    ((Nat.nat, Nat.nat),
                                      Transition.transition_ext[Unit])](h),
                   d))
      distinct_aux(t, d)
      else distinct_aux(t, FSet.finsert[((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit])](Product_Type.snd[Nat.nat,
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])](h),
                                     d)))
}

def make_distinct(e: FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  distinct_aux(FSet.sorted_list_of_fset[(Nat.nat,
  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))](e),
                FSet.bot_fset[((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit])])

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
    val newReg: Nat.nat = Nat.plus_nata(Inference.max_reg(old), Nat.one_nat)
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
                      (((remove_guard_add_update(t1,
          Nat.plus_nata(inx1, Nat.one_nat), newReg),
                          u1a),
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
      = Lista.zip[(((Transition.transition_ext[Unit], Nat.nat),
                     (ioTag, Nat.nat)),
                    ((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat))),
                   (((Transition.transition_ext[Unit], Nat.nat),
                      (ioTag, Nat.nat)),
                     ((Transition.transition_ext[Unit], Nat.nat),
                       (ioTag, Nat.nat)))](relevant, replacements)
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
      Nat.less_nat(Nat.one_nat,
                    count[((Transition.transition_ext[Unit], (ioTag, Nat.nat)),
                            (Transition.transition_ext[Unit],
                              (ioTag,
                                Nat.nat)))](strip_uids(s),
     stripped_replacements))
    }),
   comparisons);
    (if (Lista.nulla[((((Transition.transition_ext[Unit], Nat.nat),
                         (ioTag, Nat.nat)),
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (ioTag, Nat.nat))),
                       (((Transition.transition_ext[Unit], Nat.nat),
                          (ioTag, Nat.nat)),
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (ioTag, Nat.nat))))](to_replace))
      None
      else Some[FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](make_distinct(generalise_transitions(to_replace,
                        old))))
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
  Lista.foldl[FSet.fset[(Nat.nat, (ioTag, Nat.nat))],
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
                                       val
 (eventNo, aa): (Nat.nat, (String, (List[Value.value], List[Value.value]))) = x
                                       val
 (_, ab): (String, (List[Value.value], List[Value.value])) = aa
                                       val
 (ac, b): (List[Value.value], List[Value.value]) = ab;
                                       io_index(eventNo, ac, b)
                                     })),
    FSet.bot_fset[(Nat.nat, (ioTag, Nat.nat))],
    Lista.enumerate[(String,
                      (List[Value.value],
                        List[Value.value]))](Nat.zero_nata, e))

def walk_up_to(n: Nat.nat,
                e: FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))],
                s: Nat.nat, r: VName.vname => Option[Value.value],
                x4: List[(String, (List[Value.value], List[Value.value]))]):
      (Transition.transition_ext[Unit], Nat.nat)
  =
  (n, e, s, r, x4) match {
  case (n, e, s, r, h::t) =>
    {
      val (Some((transition, (sa, (uid, updated))))):
            Option[(Transition.transition_ext[Unit],
                     (Nat.nat, (Nat.nat, VName.vname => Option[Value.value])))]
        = i_step(e, s, r,
                  Product_Type.fst[String,
                                    (List[Value.value], List[Value.value])](h),
                  Product_Type.fst[List[Value.value],
                                    List[Value.value]](Product_Type.snd[String,
                                 (List[Value.value], List[Value.value])](h)));
      (if (Nat.equal_nata(n, Nat.zero_nata)) (transition, uid)
        else walk_up_to(Nat.minus_nat(n, Nat.one_nat), e, sa, updated, t))
    }
}

def get_by_id_intratrace_matches_alt(e: List[(String,
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
                  lookup(b, e))) && ((Nat.less_eq_nat(Product_Type.fst[Nat.nat,
                                (ioTag, Nat.nat)](aa),
               Product_Type.fst[Nat.nat,
                                 (ioTag,
                                   Nat.nat)](b))) && (! (Product_Type.equal_proda[Nat.nat,
   (ioTag, Nat.nat)](aa, b))))
                                   }),
                                  FSet_Utils.fprod[(Nat.nat, (ioTag, Nat.nat)),
            (Nat.nat, (ioTag, Nat.nat))](indices(e), indices(e)))

def get_by_id_all_intratrace_matches_alt(x0:
   List[List[(String, (List[Value.value], List[Value.value]))]]):
      List[FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
                       (Nat.nat, (ioTag, Nat.nat)))]]
  =
  x0 match {
  case Nil => Nil
  case h::t =>
    (get_by_id_intratrace_matches_alt(h))::(get_by_id_all_intratrace_matches_alt(t))
}

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
    ((walk_up_to(e1, e, Nat.zero_nata,
                  AExp.null_state[VName.vname, Value.value], t),
       (io1, inx1)),
      (walk_up_to(e2, e, Nat.zero_nata,
                   AExp.null_state[VName.vname, Value.value], t),
        (io2, inx2)))
  })
                                      })(b)
                                   }),
                                  intras)

def find_intratrace_matches(l: List[List[(String,
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
                         Lista.zip[List[(String,
  (List[Value.value], List[Value.value]))],
                                    FSet.fset[((Nat.nat, (ioTag, Nat.nat)),
        (Nat.nat,
          (ioTag, Nat.nat)))]](l, get_by_id_all_intratrace_matches_alt(l))))

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
                Option[FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]]
  =
  ((t1: Nat.nat) => (t2: Nat.nat) => (_: Nat.nat) =>
    (_: FSet.fset[(Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    (old: FSet.fset[(Nat.nat,
                      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))])
      =>
    modify(find_intratrace_matches(l, old), t1, t2, old))

} /* object Trace_Matches */

object Type_Inference {

abstract sealed class typea
final case class NULL() extends typea
final case class NUM() extends typea
final case class STRING() extends typea
final case class UNBOUND() extends typea

def equal_typea(x0: typea, x1: typea): Boolean = (x0, x1) match {
  case (STRING(), UNBOUND()) => false
  case (UNBOUND(), STRING()) => false
  case (NUM(), UNBOUND()) => false
  case (UNBOUND(), NUM()) => false
  case (NUM(), STRING()) => false
  case (STRING(), NUM()) => false
  case (NULL(), UNBOUND()) => false
  case (UNBOUND(), NULL()) => false
  case (NULL(), STRING()) => false
  case (STRING(), NULL()) => false
  case (NULL(), NUM()) => false
  case (NUM(), NULL()) => false
  case (UNBOUND(), UNBOUND()) => true
  case (STRING(), STRING()) => true
  case (NUM(), NUM()) => true
  case (NULL(), NULL()) => true
}

def fun_of[A : HOL.equal, B : HOL.equal](x0: List[(A, B)], b: B):
      FinFun.finfun[A, B]
  =
  (x0, b) match {
  case (Nil, b) => FinFun.finfun_const[B, A](b)
  case (h::t, b) =>
    FinFun.finfun_update[A, B](fun_of[A, B](t, b), Product_Type.fst[A, B](h),
                                Product_Type.snd[A, B](h))
}

def assign_all(t: typea, l: List[VName.vname]): List[(VName.vname, typea)] =
  (Lista.map[VName.vname,
              (VName.vname, typea)](((v: VName.vname) => (v, t)), l)).distinct

def type_check_var(v: VName.vname, l: List[(VName.vname, typea)]): Boolean =
  Nat.less_eq_nat(Nat.one_nat,
                   Finite_Set.card[typea](Set.seta[typea](Lista.map_filter[(VName.vname,
                                     typea),
                                    typea](((x: (VName.vname, typea)) =>
     (if ({
            val (va, _): (VName.vname, typea) = x;
            VName.equal_vnamea(va, v)
          })
       Some[typea]({
                     val (_, t): (VName.vname, typea) = x;
                     t
                   })
       else None)),
    l))))

def type_check(l: List[(VName.vname, typea)]): Boolean =
  Lista.list_all[(VName.vname,
                   typea)](((x: (VName.vname, typea)) =>
                             type_check_var(Product_Type.fst[VName.vname,
                      typea](x),
     l)),
                            l)

def get_type_of(uu: VName.vname, x1: List[(VName.vname, typea)]): typea =
  (uu, x1) match {
  case (uu, Nil) => UNBOUND()
  case (v, h::t) =>
    (if (VName.equal_vnamea(Product_Type.fst[VName.vname, typea](h), v))
      Product_Type.snd[VName.vname, typea](h) else get_type_of(v, t))
}

def get_group_type(x0: List[VName.vname], uu: List[(VName.vname, typea)]): typea
  =
  (x0, uu) match {
  case (Nil, uu) => UNBOUND()
  case (h::t, types) =>
    {
      val gt: typea = get_type_of(h, types);
      (if (equal_typea(gt, UNBOUND())) get_group_type(t, types) else gt)
    }
}

def assign_group_types(x0: List[List[VName.vname]],
                        types: List[(VName.vname, typea)]):
      List[(VName.vname, typea)]
  =
  (x0, types) match {
  case (Nil, types) => types
  case (h::t, types) =>
    assign_group_types(t, assign_all(get_group_type(h, types), h))
}

def aexp_get_variables(x0: AExp.aexp): List[VName.vname] = x0 match {
  case AExp.L(uu) => Nil
  case AExp.V(v) => v::Nil
  case AExp.Plus(a1, a2) =>
    (aexp_get_variables(a1) ++ aexp_get_variables(a2)).distinct
  case AExp.Minus(a1, a2) =>
    (aexp_get_variables(a1) ++ aexp_get_variables(a2)).distinct
}

def infer_types_aux(x0: GExp.gexp):
      (List[(VName.vname, typea)], List[(VName.vname, VName.vname)])
  =
  x0 match {
  case GExp.Bc(uu) => (Nil, Nil)
  case GExp.Null(v) => (assign_all(NULL(), aexp_get_variables(v)), Nil)
  case GExp.Gt(a2, a1) =>
    (assign_all(NUM(), aexp_get_variables(a1) ++ aexp_get_variables(a2)), Nil)
  case GExp.Nor(g1, g2) =>
    {
      val (t1, g1a):
            (List[(VName.vname, typea)], List[(VName.vname, VName.vname)])
        = infer_types_aux(g1)
      val (t2, g2a):
            (List[(VName.vname, typea)], List[(VName.vname, VName.vname)])
        = infer_types_aux(g2);
      ((t1 ++ t2).distinct, (g1a ++ g2a).distinct)
    }
  case GExp.Eq(AExp.L(uv), AExp.L(uw)) => (Nil, Nil)
  case GExp.Eq(AExp.V(v1), AExp.V(v2)) => (Nil, (v1, v2)::Nil)
  case GExp.Eq(AExp.V(v), AExp.L(Value.Str(s))) => ((v, STRING())::Nil, Nil)
  case GExp.Eq(AExp.V(v), AExp.L(Value.Numa(s))) => ((v, NUM())::Nil, Nil)
  case GExp.Eq(AExp.L(Value.Str(s)), AExp.V(v)) => ((v, STRING())::Nil, Nil)
  case GExp.Eq(AExp.L(Value.Numa(s)), AExp.V(v)) => ((v, NUM())::Nil, Nil)
  case GExp.Eq(a, AExp.Plus(a1, a2)) =>
    (assign_all(NUM(),
                 aexp_get_variables(AExp.Plus(a1, a2)) ++
                   aexp_get_variables(a)),
      Nil)
  case GExp.Eq(a, AExp.Minus(a1, a2)) =>
    (assign_all(NUM(),
                 aexp_get_variables(AExp.Minus(a1, a2)) ++
                   aexp_get_variables(a)),
      Nil)
  case GExp.Eq(AExp.Plus(a1, a2), AExp.L(v)) =>
    (assign_all(NUM(),
                 aexp_get_variables(AExp.Plus(a1, a2)) ++
                   aexp_get_variables(AExp.L(v))),
      Nil)
  case GExp.Eq(AExp.Plus(a1, a2), AExp.V(v)) =>
    (assign_all(NUM(),
                 aexp_get_variables(AExp.Plus(a1, a2)) ++
                   aexp_get_variables(AExp.V(v))),
      Nil)
  case GExp.Eq(AExp.Minus(a1, a2), AExp.L(v)) =>
    (assign_all(NUM(),
                 aexp_get_variables(AExp.Minus(a1, a2)) ++
                   aexp_get_variables(AExp.L(v))),
      Nil)
  case GExp.Eq(AExp.Minus(a1, a2), AExp.V(v)) =>
    (assign_all(NUM(),
                 aexp_get_variables(AExp.Minus(a1, a2)) ++
                   aexp_get_variables(AExp.V(v))),
      Nil)
}

def collapse_group(x0: (VName.vname, VName.vname), x1: List[List[VName.vname]]):
      List[List[VName.vname]]
  =
  (x0, x1) match {
  case ((v1, v2), Nil) => (v1::(v2::Nil))::Nil
  case ((v1, v2), h::t) =>
    (if ((Lista.ListMem[VName.vname](v1, h)) || (Lista.ListMem[VName.vname](v2,
                                     h)))
      ((v1::(v2::h)).distinct)::t else collapse_group((v1, v2), t))
}

def collapse_groups(x0: List[(VName.vname, VName.vname)],
                     g: List[List[VName.vname]]):
      List[List[VName.vname]]
  =
  (x0, g) match {
  case (Nil, g) => g
  case (h::t, g) => collapse_groups(t, collapse_group(h, g))
}

def infer_types(g: GExp.gexp): Option[FinFun.finfun[VName.vname, typea]] =
  {
    val (types, groups):
          (List[(VName.vname, typea)], List[(VName.vname, VName.vname)])
      = infer_types_aux(g)
    val type_lst: List[(VName.vname, typea)] =
      assign_group_types(collapse_groups(groups, Nil), types);
    (if (type_check(type_lst))
      Some[FinFun.finfun[VName.vname,
                          typea]](fun_of[VName.vname,
  typea](type_lst, UNBOUND()))
      else None)
  }

} /* object Type_Inference */

object Increment_Reset {

def guardMatch[A, B](t1: Transition.transition_ext[A],
                      t2: Transition.transition_ext[B]):
      Boolean
  =
  Code_Generation.guardMatch_alt(Transition.Guard[A](t1),
                                  Transition.Guard[B](t2))

def outputMatch[A, B](t1: Transition.transition_ext[A],
                       t2: Transition.transition_ext[B]):
      Boolean
  =
  Code_Generation.outputMatch_alt(Transition.Outputs[A](t1),
                                   Transition.Outputs[B](t2))

def initialiseReg(t: Transition.transition_ext[Unit], newReg: VName.vname):
      Transition.transition_ext[Unit]
  =
  Transition.transition_exta[Unit](Transition.Label[Unit](t),
                                    Transition.Arity[Unit](t),
                                    Transition.Guard[Unit](t),
                                    Transition.Outputs[Unit](t),
                                    (newReg,
                                      AExp.L(Value.Numa(Int.zero_int)))::(Transition.Updates[Unit](t)),
                                    ())

def drop_transition(e: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                     uid: Nat.nat):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  FSet.ffilter[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   Transition.transition_ext[Unit]))](((x:
                  (Nat.nat,
                    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])))
                 =>
                ! (Nat.equal_nata(Product_Type.fst[Nat.nat,
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit])](x),
                                   uid))),
               e)

def insert_increment(t1ID: Nat.nat, t2ID: Nat.nat, s: Nat.nat,
                      newa: FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                      old: FSet.fset[(Nat.nat,
                                       ((Nat.nat, Nat.nat),
 Transition.transition_ext[Unit]))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  {
    val t1: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t1ID)
    val t2: Transition.transition_ext[Unit] = Inference.get_by_id(newa, t2ID);
    (if ((guardMatch[Unit, Unit](t1, t2)) && (outputMatch[Unit, Unit](t1, t2)))
      {
        val r: Nat.nat = Nat.plus_nata(Inference.max_reg(newa), Nat.one_nat)
        val newReg: VName.vname = VName.R(r)
        val newT1: Transition.transition_ext[Unit] =
          Transition.transition_exta[Unit](Transition.Label[Unit](t1),
    Transition.Arity[Unit](t1), Nil,
    (AExp.Plus(AExp.V(newReg), AExp.V(VName.I(Nat.one_nat))))::Nil,
    (newReg,
      AExp.Plus(AExp.V(newReg),
                 AExp.V(VName.I(Nat.one_nat))))::(Transition.Updates[Unit](t1)),
    ());
        Transition.transition_exta[Unit](Transition.Label[Unit](t2),
  Transition.Arity[Unit](t2), Nil,
  (AExp.Plus(AExp.V(newReg), AExp.V(VName.I(Nat.one_nat))))::Nil,
  (newReg,
    AExp.Plus(AExp.V(newReg),
               AExp.V(VName.I(Nat.one_nat))))::(Transition.Updates[Unit](t2)),
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
                               val (to, from): (Nat.nat, Nat.nat) = ab;
                               ((t: Transition.transition_ext[Unit]) =>
                                 (uid, ((to, from),
 (if ((Nat.equal_nata(to, Inference.arrives(t1ID,
     newa))) || (Nat.equal_nata(to, Inference.arrives(t2ID, newa))))
   initialiseReg(t, newReg) else t))))
                             })(b)
                          }),
                         newa);
        Some[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]](Inference.replaceAll(drop_transition(initialised,
                     t2ID),
     t1, newT1))
      }
      else None)
  }

} /* object Increment_Reset */

object SelectionStrategies {

def naive_score(t1: FSet.fset[Transition.transition_ext[Unit]],
                 t2: FSet.fset[Transition.transition_ext[Unit]]):
      Nat.nat
  =
  FSet.size_fseta[(Transition.transition_ext[Unit],
                    Transition.transition_ext[Unit])].apply(FSet.ffilter[(Transition.transition_ext[Unit],
                                   Transition.transition_ext[Unit])](((a:
                                 (Transition.transition_ext[Unit],
                                   Transition.transition_ext[Unit]))
                                =>
                               {
                                 val (x, y):
                                       (Transition.transition_ext[Unit],
 Transition.transition_ext[Unit])
                                   = a;
                                 (Transition.Label[Unit](x) ==
                                   Transition.Label[Unit](y)) && (Nat.equal_nata(Transition.Arity[Unit](x),
  Transition.Arity[Unit](y)))
                               }),
                              FSet_Utils.fprod[Transition.transition_ext[Unit],
        Transition.transition_ext[Unit]](t1, t2)))

} /* object SelectionStrategies */
