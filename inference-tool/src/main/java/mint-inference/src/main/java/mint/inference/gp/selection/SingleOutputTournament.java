package mint.inference.gp.selection;

import mint.inference.evo.Chromosome;
import mint.inference.gp.fitness.*;
import mint.inference.gp.tree.Node;
import mint.inference.gp.tree.NodeComparator;
import mint.tracedata.types.VariableAssignment;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Future;

import org.apache.commons.collections4.MultiValuedMap;

/**
 * Created by neilwalkinshaw on 25/06/15.
 */
public class SingleOutputTournament extends IOTournamentSelection<VariableAssignment<?>> {

	protected Map<Node<?>, List<Double>> distances = null;

	public SingleOutputTournament(MultiValuedMap<List<VariableAssignment<?>>, VariableAssignment<?>> evals,
			List<Chromosome> totalPopulation, int maxDepth) {
		super(evals, totalPopulation, maxDepth);
		distances = new HashMap<Node<?>, List<Double>>();
	}

	@Override
	public SingleOutputFitness<?> getFitness(Chromosome toEvaluateC) {
		Node<?> toEvaluate = (Node<?>) toEvaluateC;

		if (toEvaluate.getType().equals("string"))
			return new SingleOutputStringFitness(evals, VariableAssignment.getStringValues(),
					(Node<VariableAssignment<String>>) toEvaluate, maxDepth);
		else if (toEvaluate.getType().equals("double"))
			return new SingleOutputDoubleFitness(evals, VariableAssignment.getDoubleValues(),
					(Node<VariableAssignment<Double>>) toEvaluate, maxDepth);
		else if (toEvaluate.getType().equals("integer"))
			return new SingleOutputIntegerFitness(evals, VariableAssignment.getIntValues(),
					(Node<VariableAssignment<Integer>>) toEvaluate, maxDepth);
		else if (toEvaluate.getType().equals("List"))
			return new SingleOutputListFitness(evals, VariableAssignment.getListValues(),
					(Node<VariableAssignment<List>>) toEvaluate, maxDepth);
		else {
			assert (toEvaluate.getType().equals("boolean"));
			return new SingleOutputBooleanFitness(evals, VariableAssignment.getBooleanValues(),
					(Node<VariableAssignment<Boolean>>) toEvaluate, maxDepth);
		}
	}

	@Override
	protected Comparator<Chromosome> getComparator() {
		return new NodeComparator(this);
	}

	@Override
	protected void processResult(Map<Future, Chromosome> solMap, Future<Double> sol, double score, Fitness fitness) {
		super.processResult(solMap, sol, score, fitness);
		SingleOutputFitness sof = (SingleOutputFitness) fitness;
	}

	public Map<Node<?>, List<Double>> getDistances() {
		return distances;
	}
}
