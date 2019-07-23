import com.microsoft.z3
import exceptions._
import java.io._
import scala.io.Source
import scala.util.Random
import sys.process._
import Types._

object Dirties {

  def foldl[A, B](f: A => B => A, b: A, l: List[B]): A =
    l.par.foldLeft(b)(((x, y) => (f(x))(y)))

  def toZ3(a: VName.vname): String = a match {
    case VName.I(n) => s"i${Code_Numeral.integer_of_nat(n)}"
    case VName.R(n) => s"r${Code_Numeral.integer_of_nat(n)}"
  }

  def toZ3(a: AExp.aexp): String =  a match {
    case AExp.L(Value.Numa(n)) => Code_Numeral.integer_of_int(n).toString
    case AExp.L(Value.Str(s)) => "\"" + s + "\""
    case AExp.V(v) => s"${toZ3(v)}Value"
    case AExp.Plus(a1, a2) => s"(+ (${toZ3(a1)}) (${toZ3(a2)}))"
    case AExp.Minus(a1, a2) => s"(- (${toZ3(a1)}) (${toZ3(a2)}))"
  }

  def toZ3(a: Type_Inference.typea): String = a match  {
    case Type_Inference.NUM() => "Int"
    case Type_Inference.STRING() => "String"
    case Type_Inference.UNBOUND() => "String"
  }

  def toZ3(g: GExp.gexp, types: Map[VName.vname, Type_Inference.typea]): String =  g match {
    case GExp.Bc(a) => a.toString()
    case GExp.Eq(a1, a2) => s"(= ${toZ3(a1)} ${toZ3(a2)})"
    case GExp.Gt(a1, a2) => s"(> ${toZ3(a1)} ${toZ3(a2)})"
    case GExp.Nor(g1, g2) => if (g1 == g2) s"(not ${toZ3(g1, types)})" else s"(not (or ${toZ3(g1, types)} ${toZ3(g2, types)}))"
    case GExp.Null(AExp.V(VName.I(n))) => s"(= i${Code_Numeral.integer_of_nat(n)} (as none (Option ${toZ3(types(VName.I(n)))})))"
    case GExp.Null(AExp.V(VName.R(n))) => s"(= r${Code_Numeral.integer_of_nat(n)} (as none (Option ${toZ3(types(VName.I(n)))})))"
    case GExp.Null(v) => throw new java.lang.IllegalArgumentException("Z3 does not handle null of more complex arithmetic expressions")
  }

  var sat_memo = scala.collection.immutable.Map[GExp.gexp, Boolean]()

  def satisfiable(g: GExp.gexp): Boolean = {
    if (sat_memo isDefinedAt g) {
      return sat_memo(g)
    }
    else {
      val maybe_types = Type_Inference.infer_types(g)
      maybe_types match {
        case None => false
        case Some(types) => {
          var z3String = s"(declare-datatype Option (par (X) ((none) (some (val X)))))\n" +
          types.map(t => t match {
              case (k, v) => s"(declare-const ${toZ3(k)} (Option ${toZ3(v)}))\n(declare-const ${toZ3(k)}Value (${toZ3(v)}))"
            }
          ).foldLeft("")(((x, y) => x + y + "\n"))+
          s"(assert ${toZ3(g, types)})\n(check-sat)"

          Log.root.debug(g.toString)
          Log.root.debug(z3String)

          val ctx = new z3.Context()
          val solver = ctx.mkSimpleSolver()
          solver.fromString(z3String)
          return solver.check() == z3.Status.SATISFIABLE
        }
      }
    }
  }

  // def randomMember[A](f: FSet.fset[A]): Option[A] = f match {
  //   case FSet.Abs_fset(s) => s match {
  //     case Set.seta(l) => {
  //       if (l == List()) {
  //         None
  //       }
  //       else {
  //         Some(Random.shuffle(l).head)
  //       }
  //     }
  //   }
  // }

  def randomMember[A](f: FSet.fset[A]): Option[A] = f match {
    case FSet.fset_of_list(l) =>
        if (l == List()) {
          None
        }
        else {
          Some(Random.shuffle(l).head)
        }
  }

  def addLTL(f: String, e: String) = {
    val lines = Source.fromFile(f).getLines().toList.dropRight(1)

    val pw = new PrintWriter(new File(f))

    (lines :+ (e + "\nEND")).foreach(pw.println)

    pw.close()
  }

  def alwaysDifferentOutputsDirectSubsumption[A](m1: IEFSM,
                                              m2: IEFSM,
                                              s:Nat.nat,
                                              s_prime: Nat.nat,
                                              t1: Transition.transition_ext[A],
                                              t2: Transition.transition_ext[A]):Boolean = {
      // This is a stub but should be safe enough
      true
  }

  def initiallyUndefinedContextCheck(e: IEFSM, r: Nat.nat, s: Nat.nat): Boolean = {
    val f = "intermediate_"+System.currentTimeMillis()
    TypeConversion.efsmToSALTranslator(Inference.tm(e), f)

    addLTL("salfiles/" + f + ".sal", s"  initiallyUndefined: THEOREM MichaelsEFSM |- G(cfstate = State_${Code_Numeral.integer_of_nat(s)} => r_${Code_Numeral.integer_of_nat(r)} = value_option ! None);")

    val output = Seq("bash", "-c", "cd salfiles; sal-smc --assertion='" + f + "{100}!initiallyUndefined'").!!
    if (output.toString != "proved.\n") {
      print(output)
    }
    return (output.toString == "proved.\n")
  }

  def salValue(v: Value.value): String = v match {
    case Value.Str(s) => s"STR(String_$s)"
    case Value.Numa(n) => s"NUM(${Code_Numeral.integer_of_int(n)})"
  }

  def generaliseOutputContextCheck(l: String, ePrime: IEFSM, e: IEFSM, r: Nat.nat, v: Value.value, s_old: Nat.nat, s_new: Nat.nat): Boolean = {
    val f_old = "orig_"+System.currentTimeMillis()
    TypeConversion.efsmToSALTranslator(Inference.tm(e), f_old)
    val inxLabel = Code_Generation.input_updates_register(ePrime)
    addLTL("salfiles/" + f_old + s".sal", s"  inputValue: THEOREM MichaelsEFSM |-\n" +
      s"    U(cfstate /= NULL_STATE, cfstate=State_${Code_Numeral.integer_of_nat(s_old)}) =>\n"+
      s"    U(label = ${inxLabel._2} => I(1) = ${salValue(v)}, X(cfstate = NULL_STATE));")

    val f_new = "intermediate_"+System.currentTimeMillis()
    TypeConversion.efsmToSALTranslator(Inference.tm(ePrime), f_new)
    addLTL("salfiles/" + f_new + ".sal", s"  generaliseOutput: THEOREM MichaelsEFSM |-\n"+
      s"    U(cfstate /= NULL_STATE, cfstate = State_${Code_Numeral.integer_of_nat(s_new)}) =>\n"+
      s"    U(label = select => I(${Code_Numeral.integer_of_nat(inxLabel._1)+1}) = ${salValue(v)}, cfstate = NULL_STATE) =>\n"+
      s"    U(cfstate = State_${Code_Numeral.integer_of_nat(s_new)} => r_1 = Some(${salValue(v)}), cfstate=NULL_STATE);")


    println(s"sal-smc --assertion='${f_old}{100}!inputValue'")
    val output1 = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f_old}{100}!inputValue'").!!
    println(output1)

    println(s"sal-smc --assertion='${f_new}{100}!generaliseOutput'")
    val output2 = Seq("bash", "-c", s"cd salfiles; sal-smc --assertion='${f_new}{100}!generaliseOutput'").!!
    println(output2)

    return (output1.toString == "proved.\n" && output2.toString == "proved.\n")
  }

  def canTake(e: Types.IEFSM, s: Nat.nat, t: Types.Transition): Boolean = {
    val f = "intermediate_"+System.currentTimeMillis()
    TypeConversion.efsmToSALTranslator(Inference.tm(e), f)

    addLTL("salfiles/" + f + ".sal", s"  canTake: THEOREM MichaelsEFSM |- G(cfstate = State_${Code_Numeral.integer_of_nat(s)} => EXISTS (I : input_sequence ! Sequence): (${efsm2sal.guards2sal(Transition.Guard(t))}));")

    val output = Seq("bash", "-c", "cd salfiles; sal-smc --assertion='" + f + "{100}!canTake'").!!
    if (output.toString != "proved.\n") {
      print(output)
    }
    return (output.toString == "proved.\n")
  }

  def scalaDirectlySubsumes(a: IEFSM,
                            b: IEFSM,
                            s: Nat.nat,
                            s_prime: Nat.nat,
                            t1: Transition.transition_ext[Unit],
                            t2: Transition.transition_ext[Unit]): Boolean = {
                              if (Store_Reuse_Subsumption.drop_guard_add_update_direct_subsumption(t2, t1, b, s_prime)) {
                                // println("n")
                                return false
                              }
                              if (Store_Reuse_Subsumption.generalise_output_direct_subsumption(t2, t1, b, a, s, s_prime)) {
                                // println("n")
                                return false
                              }
                              // if (Transition.Guard(t1).length > 0 && Transition.Guard(t1).length > 0) {
                              //   return true
                              // }
                              // else {
                                println(s"Does ${PrettyPrinter.transitionToString(t1)} directly subsume ${PrettyPrinter.transitionToString(t2)}? (y/N)")
                                val subsumes = readLine("") == "y"
                                subsumes
                              // }
                            }
  }
