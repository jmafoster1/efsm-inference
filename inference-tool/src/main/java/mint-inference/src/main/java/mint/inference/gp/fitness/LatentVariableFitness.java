package mint.inference.gp.fitness;

import mint.inference.gp.CallableNodeExecutor;
import mint.inference.gp.tree.Node;
import mint.tracedata.types.VariableAssignment;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Created by neilwalkinshaw on 05/03/15.
 */
public abstract class LatentVariableFitness<T> extends Fitness {

	final ArrayList<T> values;

	final Map<List<VariableAssignment<?>>, VariableAssignment<T>> evalSet;

	protected final int maxDepth;

	protected Node<VariableAssignment<T>> individual;
	
	List<Double> distances;

	public LatentVariableFitness(
			Map<List<VariableAssignment<?>>, VariableAssignment<T>> evals,
			Node<VariableAssignment<T>> individual,
			ArrayList<T> values,
			int maxDepth) {
		this.values = values;
		this.evalSet = evals;
		this.individual = individual;
		this.maxDepth = maxDepth;
		this.distances = new ArrayList<Double>();
	}

	public Node<?> getIndividual() {
		return individual;
	}

	public List<Double> getDistances() {
		return distances;
	}
	
	private double eval(List<VariableAssignment<?>> current, Object expected) {
		boolean penalize = false;
		double distance = 0D;
		T actual = null;

		try {
			CallableNodeExecutor<T> executor = new CallableNodeExecutor<T>(individual, current);

			try {
				actual = executor.call();
			} catch (Exception e) { // GP candidate has crashed.
				e.printStackTrace();
				penalize = true;
			}
			if (actual == null)
				penalize = true;
			if (!penalize) {
				distance = (distance(actual, expected));
				distances.add(distance);
			}
		} catch (InvalidDistanceException e) {
			penalize = true;
		}
		if (individual.subTreeMaxdepth() > maxDepth)
			penalize = true;
		// distance+=distance/2;
		else
			distances.add(distance);
		return distance;
	}

	public Double call() throws InterruptedException {
		double diff = 0;
		double mistakes = 0;
		Set<VariableAssignment<?>> totalUsedVars = new HashSet<VariableAssignment<?>>();
		
		for (Map.Entry<List<VariableAssignment<?>>, VariableAssignment<T>> target : evalSet.entrySet()) {
			// Add used variables to totalUsedVars
			T targetValue = target.getValue().getValue();
			List<VariableAssignment<?>> current = target.getKey();
			
			for (VariableAssignment<?> v: current) {
				totalUsedVars.add(v);
			}
			
			CallableNodeExecutor<T> executor = new CallableNodeExecutor<T>(individual, target.getKey());
			
			Set<VariableAssignment<T>> undef = individual.varsInTree();
			undef.removeAll(target.getKey());
			
			double minErr = Double.POSITIVE_INFINITY;
			
			if (undef.isEmpty()) {
				double offBy = eval(current, targetValue);
				if (offBy < minErr) {
					minErr = offBy;
				}			}
			else {
				for (T value: values) {
					for (VariableAssignment<T> v: undef) {
						v.setValue(value);
						double offBy = eval(current, targetValue);
						if (offBy < minErr) {
							minErr = offBy;
						}
					}
				}				
			}
			diff += minErr;
			if (minErr > 0) {
				mistakes++;
			}
		}
		
		return mistakes + ((diff/individual.numVarsInTree()) + totalUsedVars.size() + individual.numVarsInTree());
	}

	protected Double calculateFitness(List<Double> distances) {
		return rmsd(distances);
	}

	protected abstract double distance(T actual, Object expected) throws InvalidDistanceException;

	@Override
	public boolean equals(Object o) {
		if (this == o)
			return true;
		if (!(o instanceof LatentVariableFitness))
			return false;

		LatentVariableFitness singleOutputFitness = (LatentVariableFitness) o;

		if (!individual.equals(singleOutputFitness.individual))
			return false;

		return true;
	}

	@Override
	public int hashCode() {
		return individual.hashCode();
	}
}
