package mint.inference.evo;

import org.apache.log4j.Logger;

import mint.inference.gp.Generator;

import java.util.*;

/**
 * Responsible for creating the offspring in an iteration by applying mutation
 * and crossover. Also retains a small number (3) elite offspring from the
 * previous generation.
 *
 * Created by neilwalkinshaw on 06/03/15.
 */
public abstract class AbstractIterator {

    protected Generator gen;
	protected List<Chromosome> offSpring, population;
	protected List<Chromosome> elite;
	protected Random rand;
	protected float crossOver, mutation;

	private final static Logger LOGGER = Logger.getLogger(AbstractIterator.class.getName());

	public AbstractIterator(List<Chromosome> population, float crossOver, float mutation, Random r,
			Collection<Chromosome> elites) {
		offSpring = new ArrayList<Chromosome>();
		rand = r;
		this.population = population;
		this.mutation = mutation;
		this.crossOver = crossOver;

		this.elite = new ArrayList<Chromosome>();
		this.elite.addAll(elites);
	}

	public List<Chromosome> iterate(AbstractEvo gp) {
//		System.out.println("  AbstractIterator.iterate");

		int numberCrossover = Math.round(population.size() * crossOver);
		int elites = Math.min(3, elite.size());
		Collections.shuffle(population);

//		System.out.println("    Crossing over");
		crossOver(population, numberCrossover);
//		System.out.println("    Mutating");
		mutate();

		for (int i = 0; i < elites; i++) {
			offSpring.add(elite.get(i));
		}
		int remainder = population.size() - offSpring.size();
		if (remainder > 0) {
			offSpring.addAll(gp.generatePopulation(remainder));
		}
		Collections.shuffle(offSpring);
//		System.out.println("  AbstractIterator.iterate finished");

		return offSpring;
	}

	public abstract void mutate();
	
	protected abstract void crossOver(List<Chromosome> pop, int number);

}
