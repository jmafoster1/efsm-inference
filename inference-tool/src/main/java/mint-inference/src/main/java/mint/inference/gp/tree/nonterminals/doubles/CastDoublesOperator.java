package mint.inference.gp.tree.nonterminals.doubles;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;

import mint.inference.gp.Generator;
import mint.inference.gp.tree.Node;
import mint.inference.gp.tree.NodeVisitor;
import mint.inference.gp.tree.NonTerminal;
import mint.tracedata.types.DoubleVariableAssignment;
import mint.tracedata.types.IntegerVariableAssignment;

/**
 * Created by neilwalkinshaw on 03/03/15.
 */
public class CastDoublesOperator extends DoubleNonTerminal {


    public CastDoublesOperator(){}

    public CastDoublesOperator(Node<IntegerVariableAssignment> a){
        super();
        addChild(a);
    }

    @Override
    public NonTerminal<DoubleVariableAssignment> createInstance(Generator g, int depth){
        DoubleNonTerminal created =  new CastDoublesOperator(g.generateRandomIntegerExpression(depth));
        created.setResVar(copyResVar());
        return created;
    }

    @Override
    public DoubleVariableAssignment evaluate() throws InterruptedException {
        checkInterrupted();
        String val = getChild(0).evaluate().getValue().toString();
        DoubleVariableAssignment res = copyResVar();
        res.setValue(Double.parseDouble(val));
        vals.add(res.getValue());
        return res;
    }

    @Override
    public Node<DoubleVariableAssignment> copy() {
        DoubleNonTerminal created =  new CastDoublesOperator((Node<IntegerVariableAssignment>)getChild(0).copy());
        created.setResVar(copyResVar());
        return created;
    }

    @Override
    public String nodeString(){
        return "(to_real "+childrenString()+")";
    }

    @Override
    public boolean accept(NodeVisitor visitor)throws InterruptedException {
        if(visitor.visitEnter(this)) {
            visitChildren(visitor);
        }
        return visitor.visitExit(this);
    }
    
	@Override
	public Expr toZ3(Context ctx) {
		IntExpr b1 = (IntExpr) getChild(0).toZ3(ctx);
		return ctx.mkInt2Real(b1);
	}

}
