/*
 * Copyright (C) 2010-2018 Gordon Fraser, Andrea Arcuri and EvoSuite
 * contributors
 *
 * This file is part of EvoSuite.
 *
 * EvoSuite is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3.0 of the License, or
 * (at your option) any later version.
 *
 * EvoSuite is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with EvoSuite. If not, see <http://www.gnu.org/licenses/>.
 */
package org.evosuite.ga.metaheuristics.mosa;

import java.io.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.*;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.evosuite.ClientProcess;
import org.evosuite.Properties;
import org.evosuite.ga.Chromosome;
import org.evosuite.ga.ChromosomeFactory;
import org.evosuite.ga.FitnessFunction;
import org.evosuite.ga.comparators.OnlyCrowdingComparator;
import org.evosuite.ga.operators.ranking.CrowdingDistance;
import org.evosuite.ga.operators.selection.BestKSelection;
import org.evosuite.ga.operators.selection.RandomKSelection;
import org.evosuite.ga.operators.selection.RankSelection;
import org.evosuite.ga.operators.selection.SelectionFunction;
import org.evosuite.rmi.ClientServices;
import org.evosuite.statistics.RuntimeVariable;
import org.evosuite.testcase.TestChromosome;
import org.evosuite.testsuite.TestSuiteChromosome;
import org.evosuite.utils.Listener;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Implementation of the Many-Objective Sorting Algorithm (MOSA) described in the
 * paper "Reformulating branch coverage as a many-objective optimization problem".
 * 
 * @author Annibale Panichella, Fitsum M. Kifetew
 */
public class MOSA<T extends Chromosome> extends AbstractMOSA<T> {

	private static final long serialVersionUID = 146182080947267628L;

	private static final Logger logger = LoggerFactory.getLogger(MOSA.class);

	/** immigrant groups from neighboring client */
	private ConcurrentLinkedQueue<List<T>> immigrants = new ConcurrentLinkedQueue<>();

	private SelectionFunction<T> emigrantsSelection;

	/** Crowding distance measure to use */
	protected CrowdingDistance<T> distance = new CrowdingDistance<>();

	/**
	 * Constructor based on the abstract class {@link AbstractMOSA}
	 * @param factory
	 */
	public MOSA(ChromosomeFactory<T> factory) {
		super(factory);

		switch (Properties.EMIGRANT_SELECTION_FUNCTION) {
		case RANK:
			this.emigrantsSelection = new RankSelection<>();
			break;
		case RANDOMK:
			this.emigrantsSelection = new RandomKSelection<>();
			break;
		default:
			this.emigrantsSelection = new BestKSelection<>();
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected void evolve() {
		List<T> offspringPopulation = this.breedNextGeneration();

		// Create the union of parents and offSpring
		List<T> union = new ArrayList<>();
		union.addAll(this.population);
		union.addAll(offspringPopulation);

		// for parallel runs: integrate possible immigrants
		if (Properties.NUM_PARALLEL_CLIENTS > 1 && !immigrants.isEmpty()) {
			union.addAll(immigrants.poll());
		}

		Set<FitnessFunction<T>> uncoveredGoals = this.getUncoveredGoals();

		// Ranking the union
		logger.debug("Union Size =" + union.size());
		// Ranking the union using the best rank algorithm (modified version of the non dominated sorting algorithm)
		this.rankingFunction.computeRankingAssignment(union, uncoveredGoals);

		int remain = this.population.size();
		int index = 0;
		List<T> front = null;
		this.population.clear();

		// Obtain the next front
		front = this.rankingFunction.getSubfront(index);

		while ((remain > 0) && (remain >= front.size()) && !front.isEmpty()) {
			// Assign crowding distance to individuals
			this.distance.fastEpsilonDominanceAssignment(front, uncoveredGoals);
			// Add the individuals of this front
			this.population.addAll(front);

			// Decrement remain
			remain = remain - front.size();

			// Obtain the next front
			index++;
			if (remain > 0) {
				front = this.rankingFunction.getSubfront(index);
			}
		}

		// Remain is less than front(index).size, insert only the best one
		if (remain > 0 && !front.isEmpty()) { // front contains individuals to insert
			this.distance.fastEpsilonDominanceAssignment(front, uncoveredGoals);
			front.sort(new OnlyCrowdingComparator());
			for (int k = 0; k < remain; k++) {
				this.population.add(front.get(k));
			}

			remain = 0;
		}

		// for parallel runs: collect best k individuals for migration
		if (Properties.NUM_PARALLEL_CLIENTS > 1 && Properties.MIGRANTS_ITERATION_FREQUENCY > 0) {
			if ((currentIteration + 1) % Properties.MIGRANTS_ITERATION_FREQUENCY == 0 && !this.population.isEmpty()) {
				HashSet<T> emigrants = new HashSet<>(emigrantsSelection.select(this.population, Properties.MIGRANTS_COMMUNICATION_RATE));
				ClientServices.getInstance().getClientNode().emigrate(emigrants);
			}
		}

		this.currentIteration++;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void generateSolution() {
		logger.info("executing generateSolution function");

		// keep track of covered goals
		this.fitnessFunctions.forEach(this::addUncoveredGoal);

		// initialize population
		if (this.population.isEmpty()) {
			this.initializePopulation();
		}

		// Calculate dominance ranks and crowding distance
		this.rankingFunction.computeRankingAssignment(this.population, this.getUncoveredGoals());
		for (int i = 0; i < this.rankingFunction.getNumberOfSubfronts(); i++) {
			this.distance.fastEpsilonDominanceAssignment(this.rankingFunction.getSubfront(i), this.getUncoveredGoals());
		}

		Listener<Set<? extends Chromosome>> listener = null;
		if (Properties.NUM_PARALLEL_CLIENTS > 1) {
			listener = (Listener<Set<? extends Chromosome>>) event -> immigrants.add(new LinkedList<>((Set<? extends T>) event));
			ClientServices.getInstance().getClientNode().addListener(listener);
		}

		// TODO add here dynamic stopping condition
		while (!this.isFinished() && this.getNumberOfUncoveredGoals() > 0) {
			this.evolve();
			this.notifyIteration();
		}

		if (Properties.NUM_PARALLEL_CLIENTS > 1) {
			ClientServices.getInstance().getClientNode().deleteListener(listener);

			if (ClientProcess.DEFAULT_CLIENT_NAME.equals(ClientProcess.getIdentifier())) {
				//collect all end result test cases
				Set<Set<? extends Chromosome>> collectedSolutions = ClientServices.getInstance()
						.getClientNode().getBestSolutions();

				logger.debug(ClientProcess.DEFAULT_CLIENT_NAME + ": Received " + collectedSolutions.size() + " solution sets");
				for (Set<? extends Chromosome> solution : collectedSolutions) {
					for (Chromosome t : solution) {
						this.calculateFitness((T) t);
					}
				}
			} else {
				//send end result test cases to Client-0
				Set<T> solutionsSet = new HashSet<>(getSolutions());
				logger.debug(ClientProcess.getPrettyPrintIdentifier() + "Sending " + solutionsSet.size()
				+ " solutions to " + ClientProcess.DEFAULT_CLIENT_NAME);
				ClientServices.getInstance().getClientNode().sendBestSolution(solutionsSet);
			}
		}
		
		this.getBranchFitness();

		// storing the time needed to reach the maximum coverage
		ClientServices.getInstance().getClientNode().trackOutputVariable(RuntimeVariable.Time2MaxCoverage,
				this.budgetMonitor.getTime2MaxCoverage());
		this.notifySearchFinished();
	}

	// calculate the average fitness of each branch based on the 50 test cases of the best individual -- part of fitness landscape analysis
	protected void getBranchFitness() { 
		TestSuiteChromosome ts = (TestSuiteChromosome) getBestIndividual();

		List<Double> avg_fitness = new ArrayList<>();
		Map<Integer,List<Double>> branches_fitnessVals = new HashMap<Integer, List<Double>>();

		for(int i=0; i<this.getNumberOfFitnessFunctions(); i++) {
			double total = 0;
			for(int j=0; j<ts.getTests().size(); j++) {
				TestChromosome Tc = ts.getTestChromosome(j);
				List<Double> fitness_values = this.getFitnessPerTestGoal((T) Tc);

				if(!branches_fitnessVals.containsKey(j)) {
					branches_fitnessVals.put(j, fitness_values);
				}

				total += fitness_values.get(i);
			}
			double avg = total / ts.getTests().size();
			avg_fitness.add(avg);
		}

		//this.writeToCSV(avg_fitness, null); // to print the average fitness to csv file
		this.writeToCSV(avg_fitness, branches_fitnessVals); // to print the raw fitness of 50 test cases to csv file
	}

	public void writeToCSV(List<Double> avg_fitness, Map<Integer,List<Double>> branches_fitnessVals) {
		File outputDir = getReportDir();

		String class_name = Properties.TARGET_CLASS;

		String file_name = null;
		if(branches_fitnessVals == null) {
			file_name = class_name + "_Branch_Fitness.csv";
		}else {
			file_name = class_name + "_Branch_Raw_Fitness.csv";
		}

		File f = new File(outputDir.getAbsolutePath() + File.separator + file_name);

		try {
			BufferedWriter out = new BufferedWriter(new FileWriter(f, true));
			if (f.length() == 0L) {
				out.write("Class");
				out.write(",");
				out.write("Identifier");
				out.write(",");
				if(branches_fitnessVals != null) {
					out.write("TC");
					out.write(",");
				}
				for(int i=1; i<=avg_fitness.size(); i++) {
					out.write(String.valueOf(i));
					out.write(",");
				}
				out.write("\n");
			}

			int limit = 0;

			if(branches_fitnessVals == null) {
				limit = 1;
			}else {
				limit = branches_fitnessVals.size();
			}

			for(int i=0; i<limit; i++) {
				out.write(class_name);
				out.write(",");

				out.write(Properties.UNIQUE_IDENTIFIER);
				out.write(",");

				if(branches_fitnessVals == null) {
					for(int j=0; j<avg_fitness.size(); j++) {
						out.write(String.valueOf(avg_fitness.get(j)));
						out.write(",");
					}
				}else {
					out.write(String.valueOf(i+1));
					out.write(",");

					List<Double> fitness_values = branches_fitnessVals.get(i);

					for(double x: fitness_values) {
						out.write(String.valueOf(x));
						out.write(",");
					}
				}

				out.write("\n");
			}

			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static File getReportDir() throws RuntimeException{
		File dir = new File(Properties.REPORT_DIR);

		if(!dir.exists()){
			boolean created = dir.mkdirs();
			if(!created){
				String msg = "Cannot create report dir: "+Properties.REPORT_DIR;
				throw new RuntimeException(msg);
			}
		}

		return dir;
	}
}
