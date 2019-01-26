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
  implicit def `String.equal_char`: equal[String.char] = new equal[String.char]
    {
    val `HOL.equal` = (a: String.char, b: String.char) =>
      String.equal_chara(a, b)
  }
  implicit def `GExp.equal_gexp`: equal[GExp.gexp] = new equal[GExp.gexp] {
    val `HOL.equal` = (a: GExp.gexp, b: GExp.gexp) => GExp.equal_gexpa(a, b)
  }
  implicit def `AExp.equal_aexp`: equal[AExp.aexp] = new equal[AExp.aexp] {
    val `HOL.equal` = (a: AExp.aexp, b: AExp.aexp) => AExp.equal_aexpa(a, b)
  }
  implicit def `Product_Type.equal_bool`: equal[Boolean] = new equal[Boolean] {
    val `HOL.equal` = (a: Boolean, b: Boolean) => Product_Type.equal_boola(a, b)
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
  implicit def `GExp_Orderings.ord_vname`: ord[VName.vname] = new
    ord[VName.vname] {
    val `Orderings.less_eq` = (a: VName.vname, b: VName.vname) =>
      GExp_Orderings.less_eq_vname(a, b)
    val `Orderings.less` = (a: VName.vname, b: VName.vname) =>
      GExp_Orderings.less_vname(a, b)
  }
  implicit def `Char_ord.ord_char`: ord[String.char] = new ord[String.char] {
    val `Orderings.less_eq` = (a: String.char, b: String.char) =>
      Char_ord.less_eq_char(a, b)
    val `Orderings.less` = (a: String.char, b: String.char) =>
      Char_ord.less_char(a, b)
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
  implicit def `GExp_Orderings.preorder_vname`: preorder[VName.vname] = new
    preorder[VName.vname] {
    val `Orderings.less_eq` = (a: VName.vname, b: VName.vname) =>
      GExp_Orderings.less_eq_vname(a, b)
    val `Orderings.less` = (a: VName.vname, b: VName.vname) =>
      GExp_Orderings.less_vname(a, b)
  }
  implicit def `Char_ord.preorder_char`: preorder[String.char] = new
    preorder[String.char] {
    val `Orderings.less_eq` = (a: String.char, b: String.char) =>
      Char_ord.less_eq_char(a, b)
    val `Orderings.less` = (a: String.char, b: String.char) =>
      Char_ord.less_char(a, b)
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
  implicit def `GExp_Orderings.order_vname`: order[VName.vname] = new
    order[VName.vname] {
    val `Orderings.less_eq` = (a: VName.vname, b: VName.vname) =>
      GExp_Orderings.less_eq_vname(a, b)
    val `Orderings.less` = (a: VName.vname, b: VName.vname) =>
      GExp_Orderings.less_vname(a, b)
  }
  implicit def `Char_ord.order_char`: order[String.char] = new
    order[String.char] {
    val `Orderings.less_eq` = (a: String.char, b: String.char) =>
      Char_ord.less_eq_char(a, b)
    val `Orderings.less` = (a: String.char, b: String.char) =>
      Char_ord.less_char(a, b)
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

object Num {

abstract sealed class num
final case class One() extends num
final case class Bit0(a: num) extends num
final case class Bit1(a: num) extends num

} /* object Num */

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

object Product_Type {

def equal_boola(p: Boolean, pa: Boolean): Boolean = (p, pa) match {
  case (p, true) => p
  case (p, false) => ! p
  case (true, p) => p
  case (false, p) => ! p
}

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

} /* object Product_Type */

object Set {

abstract sealed class set[A]
final case class seta[A](a: List[A]) extends set[A]
final case class coset[A](a: List[A]) extends set[A]

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
  case (x, coset(xs)) => ! (Lista.member[A](xs, x))
  case (x, seta(xs)) => Lista.member[A](xs, x)
}

def remove[A : HOL.equal](x: A, xa1: set[A]): set[A] = (x, xa1) match {
  case (x, coset(xs)) => coset[A](Lista.insert[A](x, xs))
  case (x, seta(xs)) => seta[A](Lista.removeAll[A](x, xs))
}

def the_elem[A](x0: set[A]): A = x0 match {
  case seta(List(x)) => x
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
  case (coset(Nil), seta(Nil)) => false
  case (a, coset(ys)) => Lista.list_all[A](((y: A) => ! (member[A](y, a))), ys)
  case (seta(xs), b) => Lista.list_all[A](((x: A) => member[A](x, b)), xs)
}

} /* object Set */

object Lista {

def fold[A, B](f: A => B => B, x1: List[A], s: B): B = (f, x1, s) match {
  case (f, x :: xs, s) => fold[A, B](f, xs, (f(x))(s))
  case (f, Nil, s) => s
}

def rev[A](xs: List[A]): List[A] =
  fold[A, List[A]](((a: A) => (b: List[A]) => a :: b), xs, Nil)

def maps[A, B](f: A => List[B], x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x :: xs) => f(x) ++ maps[A, B](f, xs)
}

def foldr[A, B](f: A => B => B, x1: List[A]): B => B = (f, x1) match {
  case (f, Nil) => Fun.id[B]
  case (f, x :: xs) => Fun.comp[B, B, B](f(x), foldr[A, B](f, xs))
}

def filter[A](p: A => Boolean, x1: List[A]): List[A] = (p, x1) match {
  case (p, Nil) => Nil
  case (p, x :: xs) => (if (p(x)) x :: filter[A](p, xs) else filter[A](p, xs))
}

def member[A : HOL.equal](x0: List[A], y: A): Boolean = (x0, y) match {
  case (Nil, y) => false
  case (x :: xs, y) => (HOL.eq[A](x, y)) || (member[A](xs, y))
}

def insert[A : HOL.equal](x: A, xs: List[A]): List[A] =
  (if (member[A](xs, x)) xs else x :: xs)

def remdups[A : HOL.equal](x0: List[A]): List[A] = x0 match {
  case Nil => Nil
  case x :: xs =>
    (if (member[A](xs, x)) remdups[A](xs) else x :: remdups[A](xs))
}

def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
  case (f, Nil) => Nil
  case (f, x21 :: x22) => f(x21) :: map[A, B](f, x22)
}

def removeAll[A : HOL.equal](x: A, xa1: List[A]): List[A] = (x, xa1) match {
  case (x, Nil) => Nil
  case (x, y :: xs) =>
    (if (HOL.eq[A](x, y)) removeAll[A](x, xs) else y :: removeAll[A](x, xs))
}

def gen_length[A](n: Nat.nat, x1: List[A]): Nat.nat = (n, x1) match {
  case (n, x :: xs) => gen_length[A](Nat.Suc(n), xs)
  case (n, Nil) => n
}

def list_all[A](p: A => Boolean, x1: List[A]): Boolean = (p, x1) match {
  case (p, Nil) => true
  case (p, x :: xs) => (p(x)) && (list_all[A](p, xs))
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
  (foldr[A, List[A]](((a: A) => (b: List[A]) => insort_key[A, B](f, a, b)),
                      xs)).apply(Nil)

def size_list[A]: (List[A]) => Nat.nat =
  ((a: List[A]) => gen_length[A](Nat.zero_nata, a))

def equal_list[A : HOL.equal](x0: List[A], x1: List[A]): Boolean = (x0, x1)
  match {
  case (Nil, x21 :: x22) => false
  case (x21 :: x22, Nil) => false
  case (x21 :: x22, y21 :: y22) =>
    (HOL.eq[A](x21, y21)) && (equal_list[A](x22, y22))
  case (Nil, Nil) => true
}

def sorted_list_of_set[A : HOL.equal : Orderings.linorder](x0: Set.set[A]):
      List[A]
  =
  x0 match {
  case Set.seta(xs) => sort_key[A, A](((x: A) => x), remdups[A](xs))
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

} /* object Nat */

object Code_Numeral {

def one_integera: BigInt = BigInt(1)

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

def bit_cut_integer(k: BigInt): (BigInt, Boolean) =
  (if (k == BigInt(0)) (BigInt(0), false)
    else {
           val (r, s): (BigInt, BigInt) =
             ((k: BigInt) => (l: BigInt) => if (l == 0) (BigInt(0), k) else
               (k.abs /% l.abs)).apply(k).apply(BigInt(2));
           ((if (BigInt(0) < k) r else (- r) - s), s == BigInt(1))
         })

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

object String {

abstract sealed class char
final case class
  Char(a: Boolean, b: Boolean, c: Boolean, d: Boolean, e: Boolean, f: Boolean,
        g: Boolean, h: Boolean)
  extends char

def equal_chara(x0: char, x1: char): Boolean = (x0, x1) match {
  case (Char(x1, x2, x3, x4, x5, x6, x7, x8),
         Char(y1, y2, y3, y4, y5, y6, y7, y8))
    => (Product_Type.equal_boola(x1, y1)) && ((Product_Type.equal_boola(x2,
                                 y2)) && ((Product_Type.equal_boola(x3,
                             y3)) && ((Product_Type.equal_boola(x4,
                         y4)) && ((Product_Type.equal_boola(x5,
                     y5)) && ((Product_Type.equal_boola(x6,
                 y6)) && ((Product_Type.equal_boola(x7,
             y7)) && (Product_Type.equal_boola(x8, y8))))))))
}

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

def char_of_integer(k: BigInt): char =
  {
    val (q0, b0): (BigInt, Boolean) = Code_Numeral.bit_cut_integer(k)
    val (q1, b1): (BigInt, Boolean) = Code_Numeral.bit_cut_integer(q0)
    val (q2, b2): (BigInt, Boolean) = Code_Numeral.bit_cut_integer(q1)
    val (q3, b3): (BigInt, Boolean) = Code_Numeral.bit_cut_integer(q2)
    val (q4, b4): (BigInt, Boolean) = Code_Numeral.bit_cut_integer(q3)
    val (q5, b5): (BigInt, Boolean) = Code_Numeral.bit_cut_integer(q4)
    val (q6, b6): (BigInt, Boolean) = Code_Numeral.bit_cut_integer(q5)
    val a: (BigInt, Boolean) = Code_Numeral.bit_cut_integer(q6)
    val (_, aa): (BigInt, Boolean) = a;
    Char(b0, b1, b2, b3, b4, b5, b6, aa)
  }

def explode(s: String): List[char] =
  Lista.map[BigInt,
             char](((a: BigInt) => char_of_integer(a)),
                    (s.toList.map(c => { val k: Int = c.toInt; if (k < 128) BigInt(k) else sys.error("Non-ASCII character in literal") })))

} /* object String */

object Value {

abstract sealed class value
final case class Numa(a: Int.int) extends value
final case class Str(a: List[String.char]) extends value

def equal_valuea(x0: value, x1: value): Boolean = (x0, x1) match {
  case (Numa(x1), Str(x2)) => false
  case (Str(x2), Numa(x1)) => false
  case (Str(x2), Str(y2)) => Lista.equal_list[String.char](x2, y2)
  case (Numa(x1), Numa(y1)) => Int.equal_int(x1, y1)
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

} /* object AExp */

object Option_Logic {

def MaybeBoolInt(f: Int.int => Int.int => Boolean, uv: Option[Value.value],
                  uw: Option[Value.value]):
      Option[Boolean]
  =
  (f, uv, uw) match {
  case (f, Some(Value.Numa(a)), Some(Value.Numa(b))) => Some[Boolean]((f(a))(b))
  case (uu, None, uw) => None
  case (uu, Some(Value.Str(va)), uw) => None
  case (uu, uv, None) => None
  case (uu, uv, Some(Value.Str(va))) => None
}

} /* object Option_Logic */

object Optiona {

def is_none[A](x0: Option[A]): Boolean = x0 match {
  case Some(x) => false
  case None => true
}

def equal_option[A : HOL.equal](x0: Option[A], x1: Option[A]): Boolean =
  (x0, x1) match {
  case (None, Some(x2)) => false
  case (Some(x2), None) => false
  case (Some(x2), Some(y2)) => HOL.eq[A](x2, y2)
  case (None, None) => true
}

} /* object Optiona */

object GExp {

abstract sealed class gexp
final case class Bc(a: Boolean) extends gexp
final case class Eq(a: AExp.aexp, b: AExp.aexp) extends gexp
final case class Gt(a: AExp.aexp, b: AExp.aexp) extends gexp
final case class Nor(a: gexp, b: gexp) extends gexp
final case class Null(a: VName.vname) extends gexp

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
  case (Null(x5), Null(y5)) => VName.equal_vnamea(x5, y5)
  case (Nor(x41, x42), Nor(y41, y42)) =>
    (equal_gexpa(x41, y41)) && (equal_gexpa(x42, y42))
  case (Gt(x31, x32), Gt(y31, y32)) =>
    (AExp.equal_aexpa(x31, y31)) && (AExp.equal_aexpa(x32, y32))
  case (Eq(x21, x22), Eq(y21, y22)) =>
    (AExp.equal_aexpa(x21, y21)) && (AExp.equal_aexpa(x22, y22))
  case (Bc(x1), Bc(y1)) => Product_Type.equal_boola(x1, y1)
}

def gval(x0: gexp, uu: VName.vname => Option[Value.value]): Option[Boolean] =
  (x0, uu) match {
  case (Bc(b), uu) => Some[Boolean](b)
  case (Gt(a_1, a_2), s) =>
    Option_Logic.MaybeBoolInt(((x: Int.int) => (y: Int.int) =>
                                Int.less_int(y, x)),
                               AExp.aval(a_1, s), AExp.aval(a_2, s))
  case (Eq(a_1, a_2), s) =>
    Some[Boolean](Optiona.equal_option[Value.value](AExp.aval(a_1, s),
             AExp.aval(a_2, s)))
  case (Nor(a_1, a_2), s) =>
    ((gval(a_1, s), gval(a_2, s)) match {
       case (None, _) => None
       case (Some(_), None) => None
       case (Some(x), Some(y)) => Some[Boolean](! (x || y))
     })
  case (Null(v), s) => Some[Boolean](Optiona.is_none[Value.value](s(v)))
}

def conjoin(x0: List[gexp]): gexp = x0 match {
  case Nil => Bc(true)
  case h :: t => Nor(Nor(h, h), Nor(conjoin(t), conjoin(t)))
}

} /* object GExp */

object Transition {

abstract sealed class transition_ext[A]
final case class
  transition_exta[A](a: List[String.char], b: Nat.nat, c: List[GExp.gexp],
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
    => (Lista.equal_list[String.char](labela,
                                       label)) && ((Nat.equal_nata(aritya,
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

def Label[A](x0: transition_ext[A]): List[String.char] = x0 match {
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
  case Set.seta(x :: xs) =>
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
    Groups_List.sum_list[B](Lista.map[A, B](g, Lista.remdups[A](xs)))
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
  case (h :: t, s) =>
    (Optiona.equal_option[Boolean](GExp.gval(h, s),
                                    Some[Boolean](true))) && (apply_guards(t,
                                    s))
}

def input2state(x0: List[Value.value], uu: Nat.nat):
      VName.vname => Option[Value.value]
  =
  (x0, uu) match {
  case (Nil, uu) => AExp.null_state[VName.vname, Value.value]
  case (h :: t, i) =>
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
                    l: List[String.char], i: List[Value.value]):
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
       s)) && ((Lista.equal_list[String.char](Transition.Label[Unit](t),
       l)) && ((Nat.equal_nata(Lista.size_list[Value.value].apply(i),
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
  case (h :: t, old, newa) =>
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
  case (h :: t, s) => AExp.aval(h, s) :: apply_outputs(t, s)
}

def step(e: FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])],
          s: Nat.nat, r: VName.vname => Option[Value.value],
          l: List[String.char], i: List[Value.value]):
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

object Show {

def shows_string:
      (List[String.char]) => (List[String.char]) => List[String.char]
  =
  ((a: List[String.char]) => (b: List[String.char]) => a ++ b)

} /* object Show */

object Code_Target_Nat {

def nat_of_char(c: String.char): Nat.nat = Nat.Nata(String.integer_of_char(c))

} /* object Code_Target_Nat */

object Char_ord {

def less_eq_char(c1: String.char, c2: String.char): Boolean =
  Nat.less_eq_nat(Code_Target_Nat.nat_of_char(c1),
                   Code_Target_Nat.nat_of_char(c2))

def less_char(c1: String.char, c2: String.char): Boolean =
  Nat.less_nat(Code_Target_Nat.nat_of_char(c1), Code_Target_Nat.nat_of_char(c2))

} /* object Char_ord */

object Euclidean_Division {

def divide_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Code_Numeral.divide_integer(Code_Numeral.integer_of_nat(m),
Code_Numeral.integer_of_nat(n)))

def modulo_nat(m: Nat.nat, n: Nat.nat): Nat.nat =
  Nat.Nata(Code_Numeral.modulo_integer(Code_Numeral.integer_of_nat(m),
Code_Numeral.integer_of_nat(n)))

} /* object Euclidean_Division */

object Show_Instances {

def string_of_digit(n: Nat.nat): List[String.char] =
  (if (Nat.equal_nata(n, Nat.zero_nata))
    List(String.Char(false, false, false, false, true, true, false, false))
    else (if (Nat.equal_nata(n, Nat.one_nat))
           List(String.Char(true, false, false, false, true, true, false,
                             false))
           else (if (Nat.equal_nata(n, Code_Numeral.nat_of_integer(BigInt(2))))
                  List(String.Char(false, true, false, false, true, true, false,
                                    false))
                  else (if (Nat.equal_nata(n,
    Code_Numeral.nat_of_integer(BigInt(3))))
                         List(String.Char(true, true, false, false, true, true,
   false, false))
                         else (if (Nat.equal_nata(n,
           Code_Numeral.nat_of_integer(BigInt(4))))
                                List(String.Char(false, false, true, false,
          true, true, false, false))
                                else (if (Nat.equal_nata(n,
                  Code_Numeral.nat_of_integer(BigInt(5))))
                                       List(String.Char(true, false, true,
                 false, true, true, false, false))
                                       else (if (Nat.equal_nata(n,
                         Code_Numeral.nat_of_integer(BigInt(6))))
      List(String.Char(false, true, true, false, true, true, false, false))
      else (if (Nat.equal_nata(n, Code_Numeral.nat_of_integer(BigInt(7))))
             List(String.Char(true, true, true, false, true, true, false,
                               false))
             else (if (Nat.equal_nata(n, Code_Numeral.nat_of_integer(BigInt(8))))
                    List(String.Char(false, false, false, true, true, true,
                                      false, false))
                    else List(String.Char(true, false, false, true, true, true,
   false, false)))))))))))

def showsp_nat(p: Nat.nat, n: Nat.nat): (List[String.char]) => List[String.char]
  =
  (if (Nat.less_nat(n, Code_Numeral.nat_of_integer(BigInt(10))))
    Show.shows_string.apply(string_of_digit(n))
    else Fun.comp[List[String.char], List[String.char],
                   List[String.char]](showsp_nat(p,
          Euclidean_Division.divide_nat(n,
 Code_Numeral.nat_of_integer(BigInt(10)))),
                                       Show.shows_string.apply(string_of_digit(Euclidean_Division.modulo_nat(n,
                              Code_Numeral.nat_of_integer(BigInt(10)))))))

def showsp_int(p: Nat.nat, i: Int.int): (List[String.char]) => List[String.char]
  =
  (if (Int.less_int(i, Int.zero_int))
    Fun.comp[List[String.char], List[String.char],
              List[String.char]](Show.shows_string.apply(List(String.Char(true,
                                   false, true, true, false, true, false,
                                   false))),
                                  showsp_nat(p, Int.nat(Int.uminus_int(i))))
    else showsp_nat(p, Int.nat(i)))

def shows_prec_int:
      Nat.nat => Int.int => (List[String.char]) => List[String.char]
  =
  ((a: Nat.nat) => (b: Int.int) => showsp_int(a, b))

def shows_prec_nat:
      Nat.nat => Nat.nat => (List[String.char]) => List[String.char]
  =
  ((a: Nat.nat) => (b: Nat.nat) => showsp_nat(a, b))

} /* object Show_Instances */

object EFSM_Dot {

def join(x0: List[String], uu: String): String = (x0, uu) match {
  case (Nil, uu) => ""
  case (List(a), uv) => a
  case (h :: v :: va, s) => h + s + join(v :: va, s)
}

def vname2dot(x0: VName.vname): String = x0 match {
  case VName.I(n) =>
    "i<sub>" +
      String.implode(Show_Instances.shows_prec_nat.apply(Nat.zero_nata).apply(n).apply(Nil)) +
      "</sub>"
  case VName.R(n) =>
    "r<sub>" +
      String.implode(Show_Instances.shows_prec_nat.apply(Nat.zero_nata).apply(n).apply(Nil)) +
      "</sub>"
}

def value2dot(x0: Value.value): String = x0 match {
  case Value.Str(s) => String.implode(s)
  case Value.Numa(n) =>
    String.implode(Show_Instances.shows_prec_int.apply(Nat.zero_nata).apply(n).apply(Nil))
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
  case h :: t =>
    vname2dot(Product_Type.fst[VName.vname, AExp.aexp](h)) + " := " +
      aexp2dot(Product_Type.snd[VName.vname, AExp.aexp](h)) ::
      updates2dot_aux(t)
}

def updates2dot(x0: List[(VName.vname, AExp.aexp)]): String = x0 match {
  case Nil => ""
  case v :: va => "&#91;" + join(updates2dot_aux(v :: va), ",") + "&#93;"
}

def outputs2dot(x0: List[AExp.aexp], uu: Nat.nat): List[String] = (x0, uu) match
  {
  case (Nil, uu) => Nil
  case (h :: t, n) =>
    "o<sub>" +
      String.implode(Show_Instances.shows_prec_nat.apply(Nat.zero_nata).apply(n).apply(Nil)) +
      "</sub> := " +
      aexp2dot(h) ::
      outputs2dot(t, Nat.plus_nata(n, Nat.one_nat))
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
  case GExp.Null(v) => vname2dot(v) + " = NULL"
}

def guards2dot_aux(x0: List[GExp.gexp]): List[String] = x0 match {
  case Nil => Nil
  case h :: t => gexp2dot(h) :: guards2dot_aux(t)
}

def guards2dot(x0: List[GExp.gexp]): String = x0 match {
  case Nil => ""
  case v :: va => "&#91;" + join(guards2dot_aux(v :: va), ",") + "&#93;"
}

def transition2dot(t: Transition.transition_ext[Unit]): String =
  String.implode(Transition.Label[Unit](t)) + ":" +
    String.implode(Show_Instances.shows_prec_nat.apply(Nat.zero_nata).apply(Transition.Arity[Unit](t)).apply(Nil)) +
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
                                String.implode(Show_Instances.shows_prec_nat.apply(Nat.zero_nata).apply(from).apply(Nil)) +
                                  "->" +
                                  String.implode(Show_Instances.shows_prec_nat.apply(Nat.zero_nata).apply(to).apply(Nil)) +
                                  "[label=<" +
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

object GExp_Orderings {

def less_vname(x0: VName.vname, x1: VName.vname): Boolean = (x0, x1) match {
  case (VName.I(n1), VName.R(n2)) => true
  case (VName.R(n1), VName.I(n2)) => false
  case (VName.I(n1), VName.I(n2)) => Nat.less_nat(n1, n2)
  case (VName.R(n1), VName.R(n2)) => Nat.less_nat(n1, n2)
}

def less_value(x0: Value.value, x1: Value.value): Boolean = (x0, x1) match {
  case (Value.Numa(n), Value.Str(s)) => true
  case (Value.Str(s), Value.Numa(n)) => false
  case (Value.Str(n), Value.Str(s)) =>
    List_Lexorder.less_list[String.char](n, s)
  case (Value.Numa(n), Value.Numa(s)) => Int.less_int(n, s)
}

def less_aexpr(x0: AExp.aexp, x1: AExp.aexp): Boolean = (x0, x1) match {
  case (AExp.L(l1), AExp.L(l2)) => less_value(l1, l2)
  case (AExp.L(l1), AExp.V(v2)) => true
  case (AExp.L(l1), AExp.Plus(e1, e2)) => true
  case (AExp.L(l1), AExp.Minus(e1, e2)) => true
  case (AExp.V(v1), AExp.L(l1)) => false
  case (AExp.V(v1), AExp.V(v2)) => less_vname(v1, v2)
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
  case (GExp.Null(va), GExp.Null(v)) => less_vname(va, v)
}

def less_eq_gexp(e1: GExp.gexp, e2: GExp.gexp): Boolean =
  (less_gexpr(e1, e2)) || (GExp.equal_gexpa(e1, e2))

def less_gexp(e1: GExp.gexp, e2: GExp.gexp): Boolean = less_gexpr(e1, e2)

def less_eq_vname(x0: VName.vname, x1: VName.vname): Boolean = (x0, x1) match {
  case (VName.I(n1), VName.R(n2)) => true
  case (VName.R(n1), VName.I(n2)) => false
  case (VName.I(n1), VName.I(n2)) => Nat.less_eq_nat(n1, n2)
  case (VName.R(n1), VName.R(n2)) => Nat.less_eq_nat(n1, n2)
}

} /* object GExp_Orderings */

object Transition_Ordering {

def less_transition_ext[A : Orderings.linorder](t1:
          Transition.transition_ext[A],
         t2: Transition.transition_ext[A]):
      Boolean
  =
  (if (Lista.equal_list[String.char](Transition.Label[A](t1),
                                      Transition.Label[A](t2)))
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
    else List_Lexorder.less_list[String.char](Transition.Label[A](t1),
       Transition.Label[A](t2)))

def less_eq_transition_ext[A : HOL.equal : Orderings.linorder](t1:
                         Transition.transition_ext[A],
                        t2: Transition.transition_ext[A]):
      Boolean
  =
  (less_transition_ext[A](t1, t2)) || (Transition.equal_transition_exta[A](t1,
                                    t2))

} /* object Transition_Ordering */

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
  FSet.fimage[(Nat.nat,
                ((Nat.nat, Nat.nat),
                  ((Transition.transition_ext[Unit], Nat.nat),
                    (Transition.transition_ext[Unit], Nat.nat)))),
               (Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (Transition.transition_ext[Unit],
                       Nat.nat))))](((x:
(Nat.nat,
  ((Nat.nat, Nat.nat),
    ((Transition.transition_ext[Unit], Nat.nat),
      (Transition.transition_ext[Unit], Nat.nat)))))
                                       =>
                                      {
val a: (Nat.nat,
         ((Nat.nat, Nat.nat),
           ((Transition.transition_ext[Unit], Nat.nat),
             (Transition.transition_ext[Unit], Nat.nat))))
  = x
val (origina, aa):
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
   val (d1, d2): (Nat.nat, Nat.nat) = ab;
   ((ac: ((Transition.transition_ext[Unit], Nat.nat),
           (Transition.transition_ext[Unit], Nat.nat)))
      =>
     {
       val (t, ta):
             ((Transition.transition_ext[Unit], Nat.nat),
               (Transition.transition_ext[Unit], Nat.nat))
         = ac;
       (if (Nat.less_nat(d2, d1)) (origina, ((d2, d1), (ta, t))) else x)
     })
 })(b)
                                      }),
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
       val (dest, t): (Nat.nat, (Transition.transition_ext[Unit], Nat.nat)) = x;
       FSet.fimage[(Nat.nat, (Transition.transition_ext[Unit], Nat.nat)),
                    (Nat.nat,
                      ((Nat.nat, Nat.nat),
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (Transition.transition_ext[Unit],
                            Nat.nat))))](((y:
     (Nat.nat, (Transition.transition_ext[Unit], Nat.nat)))
    =>
   {
     val (desta, ta): (Nat.nat, (Transition.transition_ext[Unit], Nat.nat)) = y;
     (origin, ((dest, desta), (t, ta)))
   }),
  FSet.minus_fset[(Nat.nat,
                    (Transition.transition_ext[Unit],
                      Nat.nat))](nt, FSet.finsert[(Nat.nat,
            (Transition.transition_ext[Unit],
              Nat.nat))](x, FSet.bot_fset[(Nat.nat,
    (Transition.transition_ext[Unit], Nat.nat))])))
     }),
    nt))))

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

def choice(t1: Transition.transition_ext[Unit],
            t2: Transition.transition_ext[Unit]):
      Boolean
  =
  (Lista.equal_list[String.char](Transition.Label[Unit](t1),
                                  Transition.Label[Unit](t2))) && ((Nat.equal_nata(Transition.Arity[Unit](t1),
    Transition.Arity[Unit](t2))) && (Dirties.satisfiable(GExp.Nor(GExp.Nor(GExp.conjoin(Transition.Guard[Unit](t1)),
                                    GExp.conjoin(Transition.Guard[Unit](t1))),
                           GExp.Nor(GExp.conjoin(Transition.Guard[Unit](t2)),
                                     GExp.conjoin(Transition.Guard[Unit](t2)))))))

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
       (choice(Product_Type.fst[Transition.transition_ext[Unit], Nat.nat](tb),
                Product_Type.fst[Transition.transition_ext[Unit],
                                  Nat.nat](ta))) && (Product_Lexorder.less_eq_prod[Transition.transition_ext[Unit],
    Nat.nat](tb, ta))
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

def maxUID(e: FSet.fset[(Nat.nat,
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
     Product_Type.fst[Nat.nat,
                       ((Nat.nat, Nat.nat),
                         Transition.transition_ext[Unit])](a)),
    e))

def easy_merge(oldEFSM:
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
                maker:
                  (FSet.fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 Transition.transition_ext[Unit]))]) =>
                    Nat.nat =>
                      (Transition.transition_ext[Unit]) =>
                        Nat.nat =>
                          (Transition.transition_ext[Unit]) =>
                            Option[Transition.transition_ext[Unit]]):
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
           else (((((maker(oldEFSM))(t1FromOld))(t1))(t2FromOld))(t2) match {
                   case None => None
                   case Some(t) =>
                     (if ((Dirties.scalaDirectlySubsumes(tm(oldEFSM),
                  tm(newEFSM), t1FromOld, t1,
                  t)) && (Dirties.scalaDirectlySubsumes(tm(oldEFSM),
                 tm(newEFSM), t2FromOld, t2, t)))
                       Some[FSet.fset[(Nat.nat,
((Nat.nat, Nat.nat),
  Transition.transition_ext[Unit]))]](replace_transition(replace_transition(newEFSM,
                                     Nat.plus_nata(maxUID(newEFSM),
            Nat.one_nat),
                                     newFrom, t2NewTo, t2, t),
                  Nat.plus_nata(maxUID(newEFSM),
                                 Code_Numeral.nat_of_integer(BigInt(2))),
                  newFrom, t1NewTo, t1, t))
                       else None)
                 })))

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
                       maker:
                         (FSet.fset[(Nat.nat,
                                      ((Nat.nat, Nat.nat),
Transition.transition_ext[Unit]))]) =>
                           Nat.nat =>
                             (Transition.transition_ext[Unit]) =>
                               Nat.nat =>
                                 (Transition.transition_ext[Unit]) =>
                                   Option[Transition.transition_ext[Unit]],
                       modifier:
                         (Transition.transition_ext[Unit]) =>
                           (Transition.transition_ext[Unit]) =>
                             Nat.nat =>
                               (FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 (FSet.fset[(Nat.nat,
      ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                   Option[(FSet.fset[(Nat.nat,
               ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
    (Nat.nat => Nat.nat, Nat.nat => Nat.nat))],
                       modify: Boolean):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (easy_merge(oldEFSM, newEFSM, t1FromOld, t2FromOld, newFrom, t1NewTo, t2NewTo,
               t1, u1, t2, u2, maker)
     match {
     case None =>
       (if (modify)
         (((((modifier(t1))(t2))(newFrom))(newEFSM))(oldEFSM) match {
            case None => None
            case Some((t, (_, h_o_l_d))) =>
              (if (Dirties.scalaNondeterministicSimulates(tm(t), tm(oldEFSM),
                   h_o_l_d))
                Some[FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]](t)
                else None)
          })
         else None)
     case Some(a) =>
       Some[FSet.fset[(Nat.nat,
                        ((Nat.nat, Nat.nat),
                          Transition.transition_ext[Unit]))]](a)
   })

def nondeterminism(t: FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]):
      Boolean
  =
  ! (FSet.equal_fset[(Nat.nat,
                       ((Nat.nat, Nat.nat),
                         ((Transition.transition_ext[Unit], Nat.nat),
                           (Transition.transition_ext[Unit],
                             Nat.nat))))](nondeterministic_pairs(t),
   FSet.bot_fset[(Nat.nat,
                   ((Nat.nat, Nat.nat),
                     ((Transition.transition_ext[Unit], Nat.nat),
                       (Transition.transition_ext[Unit], Nat.nat))))]))

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

def resolve_nondeterminism(s: FSet.fset[(Nat.nat,
  ((Nat.nat, Nat.nat),
    ((Transition.transition_ext[Unit], Nat.nat),
      (Transition.transition_ext[Unit], Nat.nat))))],
                            e: FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            t: FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                            g: (FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                 Nat.nat =>
                                   (Transition.transition_ext[Unit]) =>
                                     Nat.nat =>
                                       (Transition.transition_ext[Unit]) =>
 Option[Transition.transition_ext[Unit]],
                            m: (Transition.transition_ext[Unit]) =>
                                 (Transition.transition_ext[Unit]) =>
                                   Nat.nat =>
                                     (FSet.fset[(Nat.nat,
          ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                       (FSet.fset[(Nat.nat,
            ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
 Option[(FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
          (Nat.nat => Nat.nat, Nat.nat => Nat.nat))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (FSet.equal_fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           ((Transition.transition_ext[Unit], Nat.nat),
                             (Transition.transition_ext[Unit],
                               Nat.nat))))](s,
     FSet.bot_fset[(Nat.nat,
                     ((Nat.nat, Nat.nat),
                       ((Transition.transition_ext[Unit], Nat.nat),
                         (Transition.transition_ext[Unit], Nat.nat))))]))
    (if (nondeterminism(t)) None
      else Some[FSet.fset[(Nat.nat,
                            ((Nat.nat, Nat.nat),
                              Transition.transition_ext[Unit]))]](t))
    else {
           val a: (Nat.nat,
                    ((Nat.nat, Nat.nat),
                      ((Transition.transition_ext[Unit], Nat.nat),
                        (Transition.transition_ext[Unit], Nat.nat))))
             = FSet.fMax[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             ((Transition.transition_ext[Unit], Nat.nat),
                               (Transition.transition_ext[Unit], Nat.nat))))](s)
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
              val (to1, to2): (Nat.nat, Nat.nat) = ab;
              ((ac: ((Transition.transition_ext[Unit], Nat.nat),
                      (Transition.transition_ext[Unit], Nat.nat)))
                 =>
                {
                  val (ad, ba):
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (Transition.transition_ext[Unit], Nat.nat))
                    = ac;
                  ({
                     val (t1, u1): (Transition.transition_ext[Unit], Nat.nat) =
                       ad;
                     ((ae: (Transition.transition_ext[Unit], Nat.nat)) =>
                       {
                         val (t2, u2):
                               (Transition.transition_ext[Unit], Nat.nat)
                           = ae;
                         merge_states(to1, to2, t)
                         val z: FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
                           = merge_states(arrives(u1, t), arrives(u2, t), t);
                         (merge_transitions(e, z, leaves(u1, e), leaves(u2, e),
     leaves(u1, z), arrives(u1, z), arrives(u2, z), t1, u1, t2, u2, g, m, true)
                            match {
                            case None =>
                              resolve_nondeterminism(FSet.minus_fset[(Nat.nat,
                               ((Nat.nat, Nat.nat),
                                 ((Transition.transition_ext[Unit], Nat.nat),
                                   (Transition.transition_ext[Unit],
                                     Nat.nat))))](s,
           FSet.finsert[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            ((Transition.transition_ext[Unit], Nat.nat),
                              (Transition.transition_ext[Unit],
                                Nat.nat))))](FSet.fMax[(Nat.nat,
                 ((Nat.nat, Nat.nat),
                   ((Transition.transition_ext[Unit], Nat.nat),
                     (Transition.transition_ext[Unit], Nat.nat))))](s),
      FSet.bot_fset[(Nat.nat,
                      ((Nat.nat, Nat.nat),
                        ((Transition.transition_ext[Unit], Nat.nat),
                          (Transition.transition_ext[Unit], Nat.nat))))])),
              e, t, g, m)
                            case Some(newa) =>
                              resolve_nondeterminism(nondeterministic_pairs(newa),
              e, newa, g, m)
                          })
                       })
                   })(ba)
                })
            })(b)
         })

def merge(e: FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
           s1: Nat.nat, s2: Nat.nat,
           g: (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                Nat.nat =>
                  (Transition.transition_ext[Unit]) =>
                    Nat.nat =>
                      (Transition.transition_ext[Unit]) =>
                        Option[Transition.transition_ext[Unit]],
           m: (Transition.transition_ext[Unit]) =>
                (Transition.transition_ext[Unit]) =>
                  Nat.nat =>
                    (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        Option[(FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                 (Nat.nat => Nat.nat, Nat.nat => Nat.nat))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (if (Nat.equal_nata(s1, s2))
    Some[FSet.fset[(Nat.nat,
                     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]](e)
    else {
           val t: FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]
             = merge_states(s1, s2, e);
           (if (! (nondeterminism(t)))
             Some[FSet.fset[(Nat.nat,
                              ((Nat.nat, Nat.nat),
                                Transition.transition_ext[Unit]))]](t)
             else resolve_nondeterminism(nondeterministic_pairs(t), e, t, g, m))
         })

def inference_step(uu: FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))],
                    x1: List[(Nat.nat, (Nat.nat, Nat.nat))],
                    uv: (FSet.fset[(Nat.nat,
                                     ((Nat.nat, Nat.nat),
                                       Transition.transition_ext[Unit]))]) =>
                          Nat.nat =>
                            (Transition.transition_ext[Unit]) =>
                              Nat.nat =>
                                (Transition.transition_ext[Unit]) =>
                                  Option[Transition.transition_ext[Unit]],
                    uw: (Transition.transition_ext[Unit]) =>
                          (Transition.transition_ext[Unit]) =>
                            Nat.nat =>
                              (FSet.fset[(Nat.nat,
   ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                (FSet.fset[(Nat.nat,
     ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]) =>
                                  Option[(FSet.fset[(Nat.nat,
              ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
   (Nat.nat => Nat.nat, Nat.nat => Nat.nat))]):
      Option[FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))]]
  =
  (uu, x1, uv, uw) match {
  case (uu, Nil, uv, uw) => None
  case (ta, (s, (s1, s2)) :: t, g, m) =>
    (if (Nat.less_nat(Nat.zero_nata, s))
      (merge(ta, s1, s2, g, m) match {
         case None => inference_step(ta, t, g, m)
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
           val (_, (ta, _)):
                 (Nat.nat, (Transition.transition_ext[Unit], Nat.nat))
             = aa;
           ta
         }),
        outgoing_transitions(s1, t))))(FSet.fimage[(Nat.nat,
             (Transition.transition_ext[Unit], Nat.nat)),
            Transition.transition_ext[Unit]](((aa:
         (Nat.nat, (Transition.transition_ext[Unit], Nat.nat)))
        =>
       {
         val (_, (ta, _)): (Nat.nat, (Transition.transition_ext[Unit], Nat.nat))
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
                 FSet_Utils.fprod[Nat.nat, Nat.nat](S(t), S(t))))

def infer(t: FSet.fset[(Nat.nat,
                         ((Nat.nat, Nat.nat),
                           Transition.transition_ext[Unit]))],
           r: (FSet.fset[Transition.transition_ext[Unit]]) =>
                (FSet.fset[Transition.transition_ext[Unit]]) => Nat.nat,
           g: (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                Nat.nat =>
                  (Transition.transition_ext[Unit]) =>
                    Nat.nat =>
                      (Transition.transition_ext[Unit]) =>
                        Option[Transition.transition_ext[Unit]],
           m: (Transition.transition_ext[Unit]) =>
                (Transition.transition_ext[Unit]) =>
                  Nat.nat =>
                    (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        Option[(FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                 (Nat.nat => Nat.nat, Nat.nat => Nat.nat))]):
      FSet.fset[(Nat.nat,
                  ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))]
  =
  (inference_step(t, Lista.rev[(Nat.nat,
                                 (Nat.nat,
                                   Nat.nat))](FSet.sorted_list_of_fset[(Nat.nat,
                                 (Nat.nat, Nat.nat))](score(t, r))),
                   g, m)
     match {
     case None => t
     case Some(newa) => infer(newa, r, g, m)
   })

def make_outputs(x0: List[Value.value]): List[AExp.aexp] = x0 match {
  case Nil => Nil
  case h :: t => AExp.L(h) :: make_outputs(t)
}

def make_guard(x0: List[Value.value], uu: Nat.nat): List[GExp.gexp] = (x0, uu)
  match {
  case (Nil, uu) => Nil
  case (h :: t, n) =>
    GExp.Eq(AExp.V(VName.I(n)), AExp.L(h)) ::
      make_guard(t, Nat.plus_nata(n, Nat.one_nat))
}

def make_branch(e: FSet.fset[((Nat.nat, Nat.nat),
                               Transition.transition_ext[Unit])],
                 uu: Nat.nat, uv: VName.vname => Option[Value.value],
                 x3: List[(List[String.char],
                            (List[Value.value], List[Value.value]))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  (e, uu, uv, x3) match {
  case (e, uu, uv, Nil) => e
  case (e, s, r, (label, (inputs, outputs)) :: t) =>
    (EFSM.step(e, s, r, label, inputs) match {
       case None =>
         make_branch(FSet.finsert[((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit])](((s,
                                 Nat.plus_nata(maxS(e), Nat.one_nat)),
                                Transition.transition_exta[Unit](label,
                          Lista.size_list[Value.value].apply(inputs),
                          make_guard(inputs, Nat.one_nat),
                          make_outputs(outputs), Nil, ())),
                               e),
                      Nat.plus_nata(maxS(e), Nat.one_nat), r, t)
       case Some((_, (sa, (_, updated)))) => make_branch(e, sa, updated, t)
     })
}

def make_pta(x0: List[List[(List[String.char],
                             (List[Value.value], List[Value.value]))]],
              e: FSet.fset[((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit])]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  (x0, e) match {
  case (Nil, e) => e
  case (h :: t, e) =>
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
  case (n, h :: t) => (n, h) :: toiEFSM_aux(Nat.plus_nata(n, Nat.one_nat), t)
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

def learn(l: List[List[(List[String.char],
                         (List[Value.value], List[Value.value]))]],
           r: (FSet.fset[Transition.transition_ext[Unit]]) =>
                (FSet.fset[Transition.transition_ext[Unit]]) => Nat.nat,
           g: (FSet.fset[(Nat.nat,
                           ((Nat.nat, Nat.nat),
                             Transition.transition_ext[Unit]))]) =>
                Nat.nat =>
                  (Transition.transition_ext[Unit]) =>
                    Nat.nat =>
                      (Transition.transition_ext[Unit]) =>
                        Option[Transition.transition_ext[Unit]],
           m: (Transition.transition_ext[Unit]) =>
                (Transition.transition_ext[Unit]) =>
                  Nat.nat =>
                    (FSet.fset[(Nat.nat,
                                 ((Nat.nat, Nat.nat),
                                   Transition.transition_ext[Unit]))]) =>
                      (FSet.fset[(Nat.nat,
                                   ((Nat.nat, Nat.nat),
                                     Transition.transition_ext[Unit]))]) =>
                        Option[(FSet.fset[(Nat.nat,
    ((Nat.nat, Nat.nat), Transition.transition_ext[Unit]))],
                                 (Nat.nat => Nat.nat, Nat.nat => Nat.nat))]):
      FSet.fset[((Nat.nat, Nat.nat), Transition.transition_ext[Unit])]
  =
  tm(infer(toiEFSM(make_pta(l, FSet.bot_fset[((Nat.nat, Nat.nat),
       Transition.transition_ext[Unit])])),
            r, g, m))

def null_modifier(a: Transition.transition_ext[Unit],
                   b: Transition.transition_ext[Unit], c: Nat.nat,
                   d: FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                   e: FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))]):
      Option[(FSet.fset[(Nat.nat,
                          ((Nat.nat, Nat.nat),
                            Transition.transition_ext[Unit]))],
               (Nat.nat => Nat.nat, Nat.nat => Nat.nat))]
  =
  None

def null_generator(a: FSet.fset[(Nat.nat,
                                  ((Nat.nat, Nat.nat),
                                    Transition.transition_ext[Unit]))],
                    b: Nat.nat, c: Transition.transition_ext[Unit], d: Nat.nat,
                    e: Transition.transition_ext[Unit]):
      Option[Transition.transition_ext[Unit]]
  =
  None

} /* object Inference */

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
                                 (Lista.equal_list[String.char](Transition.Label[Unit](x),
                         Transition.Label[Unit](y))) && (Nat.equal_nata(Transition.Arity[Unit](x),
                                 Transition.Arity[Unit](y)))
                               }),
                              FSet_Utils.fprod[Transition.transition_ext[Unit],
        Transition.transition_ext[Unit]](t1, t2)))

} /* object SelectionStrategies */
