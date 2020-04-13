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
package org.evosuite.strategy;

import org.evosuite.ClientProcess;
import org.evosuite.Properties;
import org.evosuite.Properties.Criterion;
import org.evosuite.coverage.CoverageCriteriaAnalyzer;
import org.evosuite.coverage.TestFitnessFactory;
import org.evosuite.ga.ChromosomeFactory;
import org.evosuite.ga.FitnessFunction;
import org.evosuite.ga.metaheuristics.GeneticAlgorithm;
import org.evosuite.ga.stoppingconditions.MaxStatementsStoppingCondition;
import org.evosuite.result.TestGenerationResultBuilder;
import org.evosuite.rmi.ClientServices;
import org.evosuite.rmi.service.ClientState;
import org.evosuite.statistics.RuntimeVariable;
import org.evosuite.testcase.TestChromosome;
import org.evosuite.testcase.TestFitnessFunction;
import org.evosuite.testcase.execution.ExecutionResult;
import org.evosuite.testcase.execution.ExecutionTracer;
import org.evosuite.testcase.execution.TestCaseExecutor;
import org.evosuite.testcase.factories.RandomLengthTestFactory;
import org.evosuite.testsuite.TestSuiteChromosome;
import org.evosuite.utils.ArrayUtil;
import org.evosuite.utils.LoggingUtils;
import org.evosuite.utils.Randomness;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.*;
import java.util.stream.Collectors;
import java.util.*;

/**
 * Test generation with MOSA
 * 
 * @author Annibale,Fitsum
 *
 */
public class MOSuiteStrategy extends TestGenerationStrategy {

	static Map<Integer, Map<String, String>> branches = new HashMap<Integer, Map<String, String>>();
	static Map<Integer, String> methods = new HashMap<Integer, String>();
	
	@Override	
	public TestSuiteChromosome generateTests() {
		// Currently only LIPS uses its own Archive
		if (Properties.ALGORITHM == Properties.Algorithm.LIPS) {
			Properties.TEST_ARCHIVE = false;
		}

		Properties.UNIQUE_IDENTIFIER = UUID.randomUUID().toString().substring(0, 8);
		ClientServices.getInstance().getClientNode().trackOutputVariable(RuntimeVariable.UniqueIdentifier,Properties.UNIQUE_IDENTIFIER);
		
		// Set up search algorithm
		PropertiesSuiteGAFactory algorithmFactory = new PropertiesSuiteGAFactory();

		GeneticAlgorithm<TestSuiteChromosome> algorithm = algorithmFactory.getSearchAlgorithm();
		
		// Override chromosome factory
		// TODO handle this better by introducing generics
		ChromosomeFactory factory = new RandomLengthTestFactory();
		algorithm.setChromosomeFactory(factory);
		
		if(Properties.SERIALIZE_GA || Properties.CLIENT_ON_THREAD)
			TestGenerationResultBuilder.getInstance().setGeneticAlgorithm(algorithm);

		long startTime = System.currentTimeMillis() / 1000;

		// What's the search target
		List<TestFitnessFactory<? extends TestFitnessFunction>> goalFactories = getFitnessFactories();
		List<TestFitnessFunction> fitnessFunctions = new ArrayList<>();
		goalFactories.forEach(f -> fitnessFunctions.addAll(f.getCoverageGoals()));
		algorithm.addFitnessFunctions((List)fitnessFunctions);

		// if (Properties.SHOW_PROGRESS && !logger.isInfoEnabled())
		algorithm.addListener(progressMonitor); // FIXME progressMonitor may cause
		// client hang if EvoSuite is
		// executed with -prefix!
		
//		List<TestFitnessFunction> goals = getGoals(true);
		LoggingUtils.getEvoLogger().info("* " + ClientProcess.getPrettyPrintIdentifier() + "Total number of test goals for {}: {}",
				Properties.ALGORITHM.name(), fitnessFunctions.size());
		
//		ga.setChromosomeFactory(getChromosomeFactory(fitnessFunctions.get(0))); // FIXME: just one fitness function?

//		if (Properties.SHOW_PROGRESS && !logger.isInfoEnabled())
//			ga.addListener(progressMonitor); // FIXME progressMonitor may cause

		// part of fitness landscape analysis
		for(int i=0; i<fitnessFunctions.size(); i++) {
			Map<String, String> bran = new HashMap<String, String>();
			String[] br = fitnessFunctions.get(i).toString().split("\\s+");
			String branch = null;
			String type = null;
			
			if(br[br.length-1].equals("root-Branch")) {
				branch = "Root";
				type = "Root";
			}else {
				String iftype = br[4], condition = br[br.length-1];
				branch = iftype ;
				type = condition;
			}
			bran.put(branch, type);
			branches.put(i, bran);
			
			Matcher matcher1 = Pattern.compile("(?<=\\.).+(?=\\()").matcher(br[0]);
			matcher1.find();
			String[] str = matcher1.group(0).split("\\.");
			String method1 = str[str.length-1];
			methods.put(i, method1);
		}
		
		if (ArrayUtil.contains(Properties.CRITERION, Criterion.DEFUSE) || 
				ArrayUtil.contains(Properties.CRITERION, Criterion.ALLDEFS) || 
				ArrayUtil.contains(Properties.CRITERION, Criterion.STATEMENT) || 
				ArrayUtil.contains(Properties.CRITERION, Criterion.RHO) || 
				ArrayUtil.contains(Properties.CRITERION, Criterion.BRANCH) ||
				ArrayUtil.contains(Properties.CRITERION, Criterion.AMBIGUITY))
			ExecutionTracer.enableTraceCalls();

		algorithm.resetStoppingConditions();
		
		TestSuiteChromosome testSuite = null;

		if (!(Properties.STOP_ZERO && fitnessFunctions.isEmpty()) || ArrayUtil.contains(Properties.CRITERION, Criterion.EXCEPTION)) {
			// Perform search
			LoggingUtils.getEvoLogger().info("* " + ClientProcess.getPrettyPrintIdentifier() + "Using seed {}", Randomness.getSeed());
			LoggingUtils.getEvoLogger().info("* " + ClientProcess.getPrettyPrintIdentifier() + "Starting evolution");
			ClientServices.getInstance().getClientNode().changeState(ClientState.SEARCH);

			algorithm.generateSolution();

			testSuite = algorithm.getBestIndividual();
			if (testSuite.getTestChromosomes().isEmpty()) {
				LoggingUtils.getEvoLogger().warn(ClientProcess.getPrettyPrintIdentifier() + "Could not generate any test case");
			}
		} else {
			zeroFitness.setFinished();
			testSuite = new TestSuiteChromosome();
			for (FitnessFunction<?> ff : testSuite.getFitnessValues().keySet()) {
				testSuite.setCoverage(ff, 1.0);
			}
		}
		
		if(Properties.COUNT_BRANCH_EXECUTION && Properties.ALGORITHM == Properties.Algorithm.MOSA) {
			this.getBranchCoveredCount(testSuite, fitnessFunctions);
		}

		long endTime = System.currentTimeMillis() / 1000;

//		goals = getGoals(false); //recalculated now after the search, eg to handle exception fitness
//        ClientServices.getInstance().getClientNode().trackOutputVariable(RuntimeVariable.Total_Goals, goals.size());
        
		// Newline after progress bar
		if (Properties.SHOW_PROGRESS)
			LoggingUtils.getEvoLogger().info("");
		
		String text = " statements, best individual has fitness: ";
		LoggingUtils.getEvoLogger().info("* " + ClientProcess.getPrettyPrintIdentifier() + "Search finished after "
				+ (endTime - startTime)
				+ "s and "
				+ algorithm.getAge()
				+ " generations, "
				+ MaxStatementsStoppingCondition.getNumExecutedStatements()
				+ text
				+ testSuite.getFitness());
		// Search is finished, send statistics
		sendExecutionStatistics();

		// We send the info about the total number of coverage goals/targets only after 
		// the end of the search. This is because the number of coverage targets may vary
		// when the criterion Properties.Criterion.EXCEPTION is used (exception coverage
		// goal are dynamically added when the generated tests trigger some exceptions
		ClientServices.getInstance().getClientNode().trackOutputVariable(RuntimeVariable.Total_Goals, algorithm.getFitnessFunctions().size());
		
		return testSuite;
	}
	
	private void getBranchCoveredCount(TestSuiteChromosome testSuite, List<TestFitnessFunction> fitnessFunctions) {
		List<Map<Integer, Integer>> maps = new ArrayList<>();
		
		for (TestChromosome test : testSuite.getTestChromosomes()) {
        	ExecutionResult origResult = test.getLastExecutionResult();
        	if(origResult == null) {
        		origResult = TestCaseExecutor.runTest(test.getTestCase());
        	}
    		Map<Integer, Integer> result = origResult.getTrace().getBranchExecutionCount();
    		maps.add(result);
        }
		
		Map<Integer, Integer> result = maps.stream()
	            .map(Map::entrySet)
	            .flatMap(Collection::stream)
	            .collect(Collectors.groupingBy(
	                    Map.Entry::getKey,
	                    Collectors.summingInt(Map.Entry::getValue)));
		
		Map<Integer, Integer> map = new TreeMap<Integer, Integer>(result); 
		
		Map<Integer, Integer> finalExecCount = CoverageCriteriaAnalyzer.validateBranchCoveredCount(map, fitnessFunctions); 
		
		CoverageCriteriaAnalyzer.writeToCSV("GA", finalExecCount);
	}
	
	public static Map<Integer, Map<String, String>> getBranches(){
		return branches;
	}
	
	public static Map<Integer, String> getMethods(){
		return methods;
	}
}
