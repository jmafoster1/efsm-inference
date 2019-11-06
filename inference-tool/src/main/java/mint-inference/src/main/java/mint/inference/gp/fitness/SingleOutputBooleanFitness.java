package mint.inference.gp.fitness;

import mint.inference.gp.NodeExecutor;
import mint.inference.gp.tree.Node;
import mint.tracedata.types.VariableAssignment;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.commons.collections4.MultiValuedMap;

/**
 * Created by neilwalkinshaw on 07/07/15.
 */
public class SingleOutputBooleanFitness extends SingleOutputFitness<Boolean> {
	public SingleOutputBooleanFitness(MultiValuedMap<List<VariableAssignment<?>>, VariableAssignment<?>> evals, List<Boolean> list,
			Node<VariableAssignment<Boolean>> toEvaluate, int maxDepth) {
		super(evals, toEvaluate, maxDepth);
	}

	@Override
	public Double call() {
		Iterator<List<VariableAssignment<?>>> inputIt = evalSet.keySet().iterator();
		NodeExecutor<Boolean> executor = new NodeExecutor(individual);
		double tp = 0.0000001D, fp = 0.0000001D, tn = 0.0000001D, fn = 0.0000001D;
		boolean haveSeenFalse = false;
		boolean haveSeenTrue = false;
		boolean penalize = false;
		for (Entry<List<VariableAssignment<?>>, VariableAssignment<?>> current: evalSet.entries()) {
			// This might break...
			VariableAssignment<?> expectedVar = (VariableAssignment<?>) current.getValue().getValue();
			if (!expectedVar.withinLimits()) {
				penalize = true;
				break;
			}

			boolean expected = (Boolean) expectedVar.getValue();

			try {
				Boolean actual = executor.execute(current.getKey());
				if (expected == true) {
					if (actual.booleanValue() == true) {
						haveSeenTrue = true;
						tp++;
					} else {
						haveSeenFalse = true;
						fn++;
					}
				} else {
					if (actual.booleanValue() == true) {
						haveSeenTrue = true;
						fp++;
					} else {
						haveSeenFalse = true;
						tn++;
					}
				}

			} catch (Exception e) { // GP candidate has crashed.
				e.printStackTrace();
				penalize = true;
				break;
			}

			// distances.add(bcr(tp,fp,tn,fn));
		}

		// if(!haveSeenFalse || !haveSeenTrue)
		// penalize = true;
		if (individual.subTreeMaxdepth() > maxDepth)
			penalize = true;

		if (penalize)
			return 100000D;
		else {
			// double bcr = 1-bcr(tp,fp,tn,fn);
			double errorRate = 1 - errorRate(tp, fp, tn, fn);
			return errorRate;
		}
	}

	/**
	 * Not necessary in this case - redesign required.
	 * 
	 * @param actual
	 * @param expected
	 * @return
	 */
	@Override
	protected double distance(Boolean actual, Object expected) {
		return 0;
	}

	private Double bcr(double tp, double fp, double tn, double fn) {
		double sensitivity = tp / (tp + fn);
		double specificity = tn / (tn + fp);
		// return (2 * sensitivity*specificity)/(sensitivity + specificity);
		return (sensitivity + specificity) / 2;
	}

	private Double errorRate(double tp, double fp, double tn, double fn) {
		return ((tp + tn) / (tp + tn + fp + fn));
	}

}
