package mint.inference.evo;

import org.apache.log4j.Logger;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

/**
 * Created by neilwalkinshaw on 06/03/15.
 */
public abstract class AbstractEvo {

	protected GPConfiguration gpConf;
	protected Collection<Chromosome> seeds;
	protected List<Chromosome> population;

	private final static Logger LOGGER = Logger.getLogger(AbstractEvo.class.getName());

	/**
	 * Takes as input a random program generator, a training set (a map from a list
	 * of input parameters to an output parameter) and a configuration.
	 * 
	 * @param gpConf
	 */
	public AbstractEvo(GPConfiguration gpConf) {
		this.gpConf = gpConf;
		seeds = new HashSet<Chromosome>();
	}

	/**
	 * Add seed nodes to be considered by GP.
	 *
	 * @param seeds
	 */
	public void setSeeds(Collection<Chromosome> seeds) {
		if (seeds != null)
			this.seeds = seeds;
	}

	public List<Chromosome> getPopulation() {
		return population;
	}

	public Chromosome evolve(int lim) {
		assert (lim > 0);
		population = generatePopulation(gpConf.getPopulationSize() - seeds.size());
		System.out.println("population: "+population);

		population.addAll(seeds);
		Selection selection = null;
		for (int i = 0; i < lim; i++) {
//			System.out.println("Iteration: "+i);
			selection = buildSelection(population);
			population = select(population, selection);
			if (selection.getBestFitness() <= 0D) { // If the result is perfect...
//				System.out.println("Winning");
				break;
			}
			assert (population.size() == gpConf.getPopulationSize());

//			System.out.println("No win yet");
			
			AbstractIterator it = getIterator(selection);

			population = new ArrayList<Chromosome>();
			population.addAll(it.iterate(this));

			Double bestFitness = selection.getBestFitness();
			LOGGER.debug("GP iteration: " + i + " - best fitness: " + bestFitness);
		}
		TournamentSelection ts = (TournamentSelection) selection;
		LOGGER.debug(ts.getBestFitnessSummary());
		assert (selection.getBestFitness() >= 0);
		LOGGER.debug("Best fitness: " + selection.getBestFitness());
		Chromosome retNode = null;
		if (!selection.getElites().isEmpty())
			retNode = selection.getElites().iterator().next();
		LOGGER.debug("Inferred GP: " + retNode);
		return retNode;
	}

	protected abstract AbstractIterator getIterator(Selection selection);

	protected abstract Selection buildSelection(List<Chromosome> population);

	protected abstract List<Chromosome> select(List<Chromosome> population, Selection selection);

	/**
	 * Generate a population of size i
	 * 
	 * @param i
	 * @return
	 */
	protected abstract List<Chromosome> generatePopulation(int i);

}
