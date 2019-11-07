package mint.inference.gp;

import mint.inference.evo.Chromosome;
import mint.inference.evo.GPConfiguration;
import mint.inference.evo.Selection;
import mint.inference.gp.selection.SingleOutputTournament;
import mint.tracedata.types.*;

import java.util.List;

import org.apache.commons.collections4.MultiValuedMap;

/**
 * Created by neilwalkinshaw on 06/03/15.
 */
public class SingleOutputGP extends GP<VariableAssignment<?>> {

	public SingleOutputGP(Generator gen, MultiValuedMap<List<VariableAssignment<?>>, VariableAssignment<?>> evals,
			GPConfiguration gpConf) {
		super(gpConf);
		this.evals = evals;
		this.gen = gen;
	}

	@Override
	protected Selection buildSelection(List<Chromosome> population) {
		return new SingleOutputTournament(evals, population, gpConf.getDepth());
	}

	protected String getType() {
		VariableAssignment<?> var = evals.values().iterator().next();
		if (var instanceof StringVariableAssignment)
			return "String";
		else if (var instanceof DoubleVariableAssignment)
			return "Double";
		else if (var instanceof IntegerVariableAssignment)
			return "Integer";
		else if (var instanceof BooleanVariableAssignment)
			return "Boolean";
		else
			return "List";
	}
}
