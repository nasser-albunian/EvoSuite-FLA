package org.evosuite.ga.metaheuristics.LandscapeAnalysis;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.UUID;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.evosuite.Properties;
import org.evosuite.coverage.CoverageCriteriaAnalyzer;
import org.evosuite.ga.Chromosome;
import org.evosuite.ga.ChromosomeFactory;
import org.evosuite.ga.FitnessFunction;
import org.evosuite.ga.metaheuristics.mosa.AbstractMOSA;
import org.evosuite.rmi.ClientServices;
import org.evosuite.statistics.RuntimeVariable;
import org.evosuite.strategy.MOSuiteStrategy;
import org.evosuite.testcase.TestChromosome;
import org.evosuite.testcase.TestFitnessFunction;
import org.evosuite.testcase.execution.ExecutionResult;
import org.evosuite.testcase.execution.TestCaseExecutor;
import org.objectweb.asm.Type;

public class RandomWalkBasedTestCase<T extends Chromosome> extends AbstractMOSA<T> {

	private static final long serialVersionUID = 8372613372917265750L;

	// Individuals of a random walk
	private List<T> individuals = new ArrayList<T>();

	String identifier = UUID.randomUUID().toString().substring(0, 8);

	public RandomWalkBasedTestCase(ChromosomeFactory<T> factory) {
		super(factory);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected void evolve() {
		T MutationOffspring = (T) individuals.get(individuals.size()-1).clone();
		notifyMutation(MutationOffspring);

		MutationOffspring.mutate();
		calculateFitness(MutationOffspring);
		
		individuals.add(MutationOffspring);
	}

	protected void generateRandomIndividual() {
		this.notifySearchStarted();

		this.generateInitialPopulation(1);

		this.calculateFitness();
		
		individuals.add(population.get(0));
	}

	@Override
	public void generateSolution() {
		if (this.population.isEmpty()) {
			this.generateRandomIndividual();
		}

		// check whether the random walk is limited to a specific number of steps (e.g., 1000 steps)
		if(Properties.LIMITED_RANDOM_WALK) {
			while ((!isFinished()) && individuals.size() < Properties.RANDOM_WALK_STEPS) {
				this.evolve();
			}
		}else {
			while ((!isFinished())) {
				this.evolve();
			}
		}
		
		this.writeToCSV("Fitness");
		this.writeToCSV("Neutrality");
		
		ClientServices.getInstance().getClientNode().trackOutputVariable(RuntimeVariable.RandomIdentRW,identifier);

		try {
			this.getBranchCoveredCount();
		} catch (SecurityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private List<Double> getFitnessValues(T i){
		List<Double> fitness_values = this.getFitnessPerTestGoal(i);
		return fitness_values;
	}

	private Map<Integer,List<Double>> getFitnessValuesPerBranch(){
		Map<Integer,List<Double>> branches_fitnessVals = new HashMap<Integer, List<Double>>();

		int branches = this.getFitnessValues(individuals.get(0)).size();
		for(int i=0; i<branches; i++) {
			List<Double> branch_fitness = new ArrayList<>();
			for(int j=0; j<individuals.size(); j++) {
				double fitness_value = this.getFitnessValues(individuals.get(j)).get(i);
				branch_fitness.add(fitness_value);
			}
			branches_fitnessVals.put(i, branch_fitness);
		}
		
		return branches_fitnessVals;
	}

	private Map<Integer,List<Integer>> calculateNeutrailtyMeasures() {
		Map<Integer,List<Integer>> neutralityValues = new HashMap<Integer, List<Integer>>();
		Map<Integer,List<Double>> branches_fitnessVals = this.getFitnessValuesPerBranch();
		for(int i=0; i<branches_fitnessVals.size(); i++) {
			List<Integer> values = new ArrayList<>();
			values.add(this.getNeutralityVolume(branches_fitnessVals.get(i)).size());
			values.add(this.getNeutralityDistance(branches_fitnessVals.get(i)));
			neutralityValues.put(i, values);
		}
		
		return neutralityValues;
	}

	private Map<Double, Integer> getNeutralityVolume(List<Double> fitnessValues) {
		Map<Double, Integer> volumeObject = new HashMap<Double, Integer>();

		double prevValue = fitnessValues.get(0);

		int count = 0;
		for(int i=0; i < fitnessValues.size(); i++) {
			if(prevValue == fitnessValues.get(i)) {
				count++;
			}else {
				if(volumeObject.containsKey(fitnessValues.get(i-1))) {
					volumeObject.put(fitnessValues.get(i-1), count + ((int) volumeObject.get(fitnessValues.get(i-1))));
				}else {
					volumeObject.put(fitnessValues.get(i-1), count);
				}

				prevValue = fitnessValues.get(i);
				count = 1;

			}
			if(fitnessValues.size() == (i+1)) {
				if(volumeObject.containsKey(fitnessValues.get(i))) {
					volumeObject.put(fitnessValues.get(i), count + ((int) volumeObject.get(fitnessValues.get(i))));
				}else {
					volumeObject.put(fitnessValues.get(i), count);
				}
			}
		}

		return volumeObject;
	}

	private int getNeutralityDistance(List<Double> fitnessValues) {
		double prevValue = fitnessValues.get(0);
		int count = 0;
		for(int i=0; i < fitnessValues.size(); i++) {
			if(prevValue == fitnessValues.get(i)) {
				count++;
			}else {
				break;
			}
		}
		return count;
	}

	private void getBranchCoveredCount() throws SecurityException, ClassNotFoundException{
		List<Map<Integer, Integer>> coveredBranchCount = new ArrayList<>();
		List<Map<String, Integer>> coveredMethodCount = new ArrayList<>();

		Map<String, Integer> methodThrowExceptionCount = new HashMap<String, Integer>();
		
		for(int i=0; i<individuals.size(); i++) {
			TestChromosome test = (TestChromosome) individuals.get(i);
			ExecutionResult origResult = test.getLastExecutionResult();
			if(origResult == null) {
				origResult = TestCaseExecutor.runTest(test.getTestCase());
			}
			Map<Integer, Integer> branchExecCount = origResult.getTrace().getBranchExecutionCount();
			Map<String, Integer> methodExecCount = origResult.getTrace().getMethodExecutionCount();
			
			String methodThroExcep = origResult.getTrace().getMethodThrowException();
			String methodThroExcep_jvm = Properties.TARGET_CLASS + "." + methodThroExcep;
			
			if (!methodThrowExceptionCount.containsKey(methodThroExcep_jvm)) {
				methodThrowExceptionCount.put(methodThroExcep_jvm, 1);
			} else {
				methodThrowExceptionCount.put(methodThroExcep_jvm, methodThrowExceptionCount.get(methodThroExcep_jvm) + 1);
			}

			coveredBranchCount.add(branchExecCount);
			coveredMethodCount.add(methodExecCount);
		}

		Map<Integer, Integer> result = coveredBranchCount.stream()
				.map(Map::entrySet)
				.flatMap(Collection::stream)
				.collect(Collectors.groupingBy(
						Map.Entry::getKey,
						Collectors.summingInt(Map.Entry::getValue)));

		Map<Integer, Integer> map = new TreeMap<Integer, Integer>(result); 

		List<TestFitnessFunction> goals = new ArrayList<TestFitnessFunction>();
		List<FitnessFunction<T>> ff = this.getFitnessFunctions();
		for(FitnessFunction<T> x: ff) {
			goals.add((TestFitnessFunction)x);
		}

		//Map<Integer, Integer> finalExecCount = CoverageCriteriaAnalyzer.validateBranchCoveredCount(map, goals); 

		//CoverageCriteriaAnalyzer.writeToCSV("RW", finalExecCount);
		
		// method types
		Map<String, String> method_types = new HashMap<String, String>();
		Method[] methods = ClassLoader.getSystemClassLoader().loadClass(Properties.TARGET_CLASS).getDeclaredMethods();
		Constructor<?>[] constructors = ClassLoader.getSystemClassLoader().loadClass(Properties.TARGET_CLASS).getConstructors();
		
		for (Method method : methods) {
			Type mt = org.objectweb.asm.Type.getType(method);
			String name = Properties.TARGET_CLASS + "." + method.getName() + mt; 
			String type = Modifier.toString(method.getModifiers());
			method_types.put(name, type);
		}
		
		for(Constructor<?> cons : constructors) {
			Type mt = org.objectweb.asm.Type.getType(cons);
			String name = Properties.TARGET_CLASS + ".<init>" + mt;
			method_types.put(name, "Constructor");
		}
		
		Set<String> keys = method_types.keySet();
		
		List<Map<String, Integer>> all = new ArrayList<>();
		
		for(int i=0; i<coveredMethodCount.size(); i++) {
			Map<String, Integer> perStep = new HashMap<String, Integer>();
			for(String key: keys) {
				int count=0;
				if(coveredMethodCount.get(i).get(key) != null)
					count = coveredMethodCount.get(i).get(key);
				perStep.put(key, count);
			}
			all.add(perStep);
		}
		
		this.writeMethodExecutionCSV(all, methodThrowExceptionCount, method_types, "all");
		this.writeMethods();
	}

	public void writeToCSV(String valType) {
		File outputDir = this.getReportDir();

		String class_name = Properties.TARGET_CLASS;

		String file_name = valType == "Fitness" ? (class_name+"_RW.csv") : valType == "Neutrality" ? (class_name+"_NT.csv") : "IndividualsCoverage.csv";

		File f = new File(outputDir.getAbsolutePath() + File.separator + file_name);

		Map<Integer, List<Integer>> neutralityValues = this.calculateNeutrailtyMeasures();
		
		try {
			BufferedWriter out = new BufferedWriter(new FileWriter(f, true));
			if (f.length() == 0L) {
				//print first line of CSV (headers)
				out.write("Class");
				out.write(",");
				out.write("Identifier");
				out.write(",");
				out.write("Total_individuals");
				out.write(",");
				out.write("Total_goals");
				out.write(",");
				if(valType.equals("Neutrality")) {
					out.write("Branch");
					out.write(",");
					out.write("NeutralityVolume");
					out.write(",");
					out.write("NeutralityDistance");
					out.write(",");
				}else {
					out.write("Step");
					out.write(",");
					for(int i=1; i<=this.getFitnessValues(individuals.get(0)).size(); i++) {
						out.write(String.valueOf(i));
						out.write(",");
					}
				}
				out.write("\n");
				
				// print second line of file (branch names)
				out.write("Class");
				out.write(",");
				out.write("Identifier");
				out.write(",");
				out.write("Total_individuals");
				out.write(",");
				out.write("Total_goals");
				out.write(",");
				out.write("Step");
				out.write(",");
				Map<Integer, Map<String, String>> branches = MOSuiteStrategy.getBranches();
				
				for(int i=0; i<branches.size(); i++) {
					Map<String, String> entry = branches.get(i); 
					out.write(entry.keySet().toArray()[0].toString());
					out.write(",");
				}
				
				out.write("\n");
				
				// print third line of file (branch conditions true or false)
				out.write("Class");
				out.write(",");
				out.write("Identifier");
				out.write(",");
				out.write("Total_individuals");
				out.write(",");
				out.write("Total_goals");
				out.write(",");
				out.write("Step");
				out.write(",");
				
				for(int i=0; i<branches.size(); i++) {
					Map<String, String> entry = branches.get(i); 
					out.write(entry.get(entry.keySet().toArray()[0]));
					out.write(",");
				}
				
				out.write("\n");
			}

			int limit = 0;
			
			if(valType.equals("Neutrality")) {
				limit = neutralityValues.size();
			}else {
				limit = individuals.size();
			}
			
			for(int i=0; i<limit; i++) {
				out.write(class_name);
				out.write(",");

				out.write(identifier);
				out.write(",");

				out.write(String.valueOf(individuals.size()));
				out.write(",");

				out.write(String.valueOf(neutralityValues.size()));
				out.write(",");

				out.write(String.valueOf(i+1));
				out.write(",");

				if(valType.equals("Neutrality")) {
					for(Integer x: neutralityValues.get(i)) {
						out.write(String.valueOf(x));
						out.write(",");
					}
				}else {
					List<Double> fitness_values = this.getFitnessValues(individuals.get(i));
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
	
	public void writeMethods() {
		File outputDir = this.getReportDir();
		
		String file_name = Properties.TARGET_CLASS + "_methods.csv";
		
		File f = new File(outputDir.getAbsolutePath() + File.separator + file_name);
		
		Map<Integer, String> methods = MOSuiteStrategy.getMethods();
		
		try {
			BufferedWriter out = new BufferedWriter(new FileWriter(f, true));
			if (f.length() == 0L) {
				out.write("TARGET_CLASS");
				out.write(",");
				out.write("Identifier");
				out.write(",");
				for(int i=1; i<=methods.size(); i++) {
					out.write(String.valueOf(i));
					out.write(",");
				}

				out.write("\n");
			}
			
			out.write(Properties.TARGET_CLASS);
			out.write(",");
			out.write(identifier);
			out.write(",");
			
			for(int i=0; i<methods.size(); i++) {
				out.write(methods.get(i));
				out.write(",");
			}
			
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public void writeMethodExecutionCSV(List<Map<String, Integer>> methodExec, Map<String, Integer> methodThrowExceptionCount, Map<String, String> method_types, String wtPrint) {
		File outputDir = this.getReportDir();

		String file_name = wtPrint == "all" ? Properties.TARGET_CLASS+"_MethodExecCountRW.csv" : Properties.TARGET_CLASS+"_MethodExecCountRW_THROW.csv";

		File f = new File(outputDir.getAbsolutePath() + File.separator + file_name);
		
		Set<String> keys = method_types.keySet();
		
		try {
			BufferedWriter out = new BufferedWriter(new FileWriter(f, true));
			if (f.length() == 0L) {
				out.write("TARGET_CLASS");
				out.write(",");
				out.write("Identifier");
				out.write(",");
				out.write("Step");
				out.write(",");
				for(String k : keys) {
					Matcher matcher = Pattern.compile("(?<=\\.).+(?=\\()").matcher(k);
					matcher.find();
					String[] s = matcher.group(0).split("\\.");
					String method = s[s.length-1];
					out.write(method);
					out.write(",");
				}

				out.write("\n");
				
				out.write("Exception_thrown");
				out.write(",");
				out.write(identifier);
				out.write(",");
				out.write("0");
				out.write(",");
				for(String k : keys) {
					if(methodThrowExceptionCount.containsKey(k)) {
						out.write("Exception");
						out.write(",");
					}else {
						out.write("No_Exception");
						out.write(",");
					}
				}

				out.write("\n");
				
				out.write("Method_type");
				out.write(",");
				out.write(identifier);
				out.write(",");
				out.write("0");
				out.write(",");
				for(String k : keys) {
					out.write(method_types.get(k));
					out.write(",");
				}

				out.write("\n");
				
			}
			
			for(int i=0; i<methodExec.size(); i++) {
				out.write(Properties.TARGET_CLASS);
				out.write(",");
				out.write(identifier);
				out.write(",");
				out.write(String.valueOf(i+1));
				out.write(",");
				Map<String, Integer> perStep = methodExec.get(i);
				for(String k : keys) {
					out.write(String.valueOf(perStep.get(k)));
					out.write(",");
				}
				out.write("\n");
			}
			
			out.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public File getReportDir() throws RuntimeException{
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
