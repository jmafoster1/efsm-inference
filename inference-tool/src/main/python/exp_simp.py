import sympy
from sympy.core.relational import (
    StrictLessThan,
    StrictGreaterThan,
    LessThan,
    GreaterThan,
    Unequality,
    Equality,
)
from sympy import And, Or, Not


class DOTprinter(sympy.StrPrinter):
    def _print(self, expr):
        if isinstance(expr, StrictGreaterThan):
            a0, a1 = expr.args
            return self.doprint(a0) + " &gt; " + self.doprint(a1)
        if isinstance(expr, StrictLessThan):
            a0, a1 = expr.args
            return self.doprint(a0) + " &lt; " + self.doprint(a1)
        if isinstance(expr, GreaterThan):
            a0, a1 = expr.args
            return self.doprint(a0) + " &ge; " + self.doprint(a1)
        if isinstance(expr, LessThan):
            a0, a1 = expr.args
            return self.doprint(a0) + " &le; " + self.doprint(a1)
        if isinstance(expr, Unequality):
            a0, a1 = expr.args
            return self.doprint(a0) + " &ne; " + self.doprint(a1)
        if isinstance(expr, Equality):
            a0, a1 = expr.args
            return self.doprint(a0) + " = " + self.doprint(a1)
        if isinstance(expr, And):
            return " &and; ".join([self.doprint(a) for a in expr.args])
        if isinstance(expr, Or):
            return " &or; ".join([self.doprint(a) for a in expr.args])
        if isinstance(expr, Not):
            a0 = expr.args
            return " &not; " + self.doprint(a0)
        return super()._print(expr)


def simp(exp):
    return DOTprinter().doprint(sympy.sympify(exp))
