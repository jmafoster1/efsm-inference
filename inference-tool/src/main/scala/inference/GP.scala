import mint.inference.gp.tree.NonTerminal;

import mint.inference.gp.tree.terminals.VariableTerminal;
import mint.inference.gp.tree.terminals.BooleanVariableAssignmentTerminal;
import mint.inference.gp.tree.terminals.IntegerVariableAssignmentTerminal;
import mint.inference.gp.tree.terminals.StringVariableAssignmentTerminal;

import mint.tracedata.types.BooleanVariableAssignment;

import mint.inference.gp.tree.nonterminals.integers.AddIntegersOperator;
import mint.inference.gp.tree.nonterminals.integers.SubtractIntegersOperator;
import mint.inference.gp.tree.nonterminals.integers.MultiplyIntegersOperator;
import mint.inference.gp.tree.nonterminals.booleans.LTBooleanIntegersOperator;
import mint.inference.gp.tree.nonterminals.booleans.GTBooleanIntegersOperator;
import mint.inference.gp.tree.nonterminals.booleans.AndBooleanOperator;
import mint.inference.gp.tree.nonterminals.booleans.OrBooleanOperator;
import mint.inference.gp.tree.nonterminals.booleans.NotBooleanOperator;

object GP {
  // Integer non-terminals
  def intNonTerms = List[NonTerminal[_]](
    new AddIntegersOperator(),
    new SubtractIntegersOperator(),
    new MultiplyIntegersOperator()
  )

  // Boolean terminals
  def boolTerms = List[VariableTerminal[_]](
    new BooleanVariableAssignmentTerminal(new BooleanVariableAssignment("tr", true), true, false),
    new BooleanVariableAssignmentTerminal(new BooleanVariableAssignment("fa", false), true, false)
  )

  // Boolean non-terminals
  def boolNonTerms = List[NonTerminal[_]](
    new LTBooleanIntegersOperator(),
    new GTBooleanIntegersOperator(),
    new NotBooleanOperator(),
    new AndBooleanOperator(),
    new OrBooleanOperator()
  )

  def getValueTerminals(values: List[Value.value]): (List[VariableTerminal[_]], List[VariableTerminal[_]]) = {
    var intTerms = List[VariableTerminal[_]]()
    var stringTerms = List[VariableTerminal[_]]()

    for (v <- (Value.Numa(Int.int_of_integer(0)) :: values).distinct.reverse) v match {
      case Value.Numa(n) => intTerms = (new IntegerVariableAssignmentTerminal(TypeConversion.toLong(n))) :: intTerms
      case Value.Str(s) => stringTerms = (new StringVariableAssignmentTerminal(s)) :: stringTerms
    }

    return (intTerms.distinct, stringTerms.distinct)
  }
}
