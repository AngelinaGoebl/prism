//==============================================================================
//	
//	Copyright (c) 2020-
//	Authors:
//	* Dave Parker <d.a.parker@cs.bham.ac.uk> (University of Birmingham)
//	
//------------------------------------------------------------------------------
//	
//	This file is part of PRISM.
//	
//	PRISM is free software; you can redistribute it and/or modify
//	it under the terms of the GNU General Public License as published by
//	the Free Software Foundation; either version 2 of the License, or
//	(at your option) any later version.
//	
//	PRISM is distributed in the hope that it will be useful,
//	but WITHOUT ANY WARRANTY; without even the implied warranty of
//	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//	GNU General Public License for more details.
//	
//	You should have received a copy of the GNU General Public License
//	along with PRISM; if not, write to the Free Software Foundation,
//	Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
//	
//==============================================================================

package explicit;

import java.util.*;

import acceptance.AcceptanceReach;
import acceptance.AcceptanceType;
import common.IntSet;
import common.Interval;
import common.IterableStateSet;
import explicit.rewards.MCRewards;
import explicit.rewards.Rewards;
import parser.ast.Expression;
import prism.*;
import explicit.UDistributionVertices;
import common.Interval;
import common.iterable.Reducible;
//import org.apache.commons.lang3.NotImplementedException;

import java.util.*;


import com.gurobi.gurobi.GRB;
import com.gurobi.gurobi.GRBEnv;
import com.gurobi.gurobi.GRBException;
import com.gurobi.gurobi.GRBLinExpr;
import com.gurobi.gurobi.GRBModel;
import com.gurobi.gurobi.GRBVar;

/**
 * Explicit-state model checker for interval discrete-time Markov chains (IDTMCs).
 */
public class IDTMCModelChecker extends ProbModelChecker
{
	// DTMCModelChecker in order to use e.g. precomputation algorithms
	protected DTMCModelChecker mcDTMC = null;

	protected IMDPSolnMethod imdpSolnMethod = IMDPSolnMethod.LINEAR_PROGRAMMING;
	
	/**
	 * Create a new IDTMCModelChecker, inherit basic state from parent (unless null).
	 */
	public IDTMCModelChecker(PrismComponent parent) throws PrismException
	{
		super(parent);
		mcDTMC = new DTMCModelChecker(this);
		mcDTMC.inheritSettings(this);
	}

	// Model checking functions


	@Override
	protected StateValues checkProbPathFormulaLTL(Model<?> model, Expression expr, boolean qual, MinMax minMax, BitSet statesOfInterest) throws PrismException
	{
		// Build product of Markov chain and DA for the LTL formula, and do any required exports
		LTLModelChecker mcLtl = new LTLModelChecker(this);
		AcceptanceType[] allowedAcceptance = {
				AcceptanceType.RABIN,
				AcceptanceType.REACH,
				AcceptanceType.BUCHI,
				AcceptanceType.STREETT,
				AcceptanceType.GENERIC
		};
		LTLModelChecker.LTLProduct<IDTMC<Double>> product = mcLtl.constructDAProductForLTLFormula(this, (IDTMC<Double>) model, expr, statesOfInterest, allowedAcceptance);
		doProductExports(product);

		// Find accepting states + compute reachability probabilities
		BitSet acc;
		if (product.getAcceptance() instanceof AcceptanceReach) {
			mainLog.println("\nSkipping BSCC computation since acceptance is defined via goal states...");
			acc = ((AcceptanceReach)product.getAcceptance()).getGoalStates();
		} else {
			mainLog.println("\nFinding accepting BSCCs...");
			acc = mcLtl.findAcceptingBSCCs(product.getProductModel(), product.getAcceptance());
		}
		mainLog.println("\nComputing reachability probabilities...");


		mainLog.println("\n ProbPath Formula LTL");


		//New
		// build partitions of states
		int numOfPartitions = model.getNumStates(); //Do they start at 0?
		List<Set<Integer>> partitions = new ArrayList<>(numOfPartitions);
		for (int i = 0; i < numOfPartitions; i++) {
			partitions.add(new LinkedHashSet<>());
		}
		for (int i=0; i<product.productModel.getNumStates(); i++){
			partitions.get(product.getModelState(i)).add(i);
		}

		// build extreme distributions
		// index of partition --> list of extreme distributions

//		mainLog.println("numofOriginal " + model.getNumStates());
//		mainLog.println("numofpartitions: " + numOfPartitions);
//		mainLog.println("numofstates: " + product.productModel.getNumStates());
//		for (int i=0; i<product.productModel.getNumStates(); i++){
////			mainLog.println("iteration:" + i + ", belongs to: " + product.getModelState(i));
//		}
//		mainLog.println("partitions:" + partitions);

		IDTMC<Double> idtmc = (IDTMC<Double>) model;
		double[][][] extremeDistr = new double[model.getNumStates()][][];
		for (int i = 0; i < model.getNumStates(); i++) {
			List<Interval<Double>> intervals = new ArrayList<>();
			List<Integer> targets = new ArrayList<>();
			Iterator<Map.Entry<Integer, Interval<Double>>> iter = idtmc.getTransitionsIterator(i);

			while (iter.hasNext()) {
				Map.Entry<Integer, Interval<Double>> entry = iter.next();
				if (entry.getValue().getLower() > 0.0 || entry.getValue().getUpper() > 0.0) {
					targets.add(entry.getKey());
					intervals.add(entry.getValue());
				}
			}

			if (targets.isEmpty()) {
				extremeDistr[i] = new double[][] { new double[model.getNumStates()] };
				continue;
			}

			//extreme distributions for state i
			UDistributionVertices<Double> uDist = new UDistributionVertices<>(
					Collections.singletonList(intervals),
					Collections.singletonList(i),
					true
			);
			mainLog.println("marginalVertices size: " + uDist.marginalVertices[0][0].length);

			double[][] mappedVertices = new double[uDist.marginalVertices[0].length][model.getNumStates()];
			for (int v = 0; v < uDist.marginalVertices[0].length; v++) {
				double[] fullVec = new double[model.getNumStates()];
				for (int t = 0; t < targets.size(); t++) {
					fullVec[targets.get(t)] = uDist.marginalVertices[0][v][t];
				}
				mappedVertices[v] = fullVec;
			}

			extremeDistr[i] = mappedVertices;
		}

		// New above
		IDTMCModelChecker mcProduct = new IDTMCModelChecker(this);
		mcProduct.inheritSettings(this);
		ModelCheckerResult res = mcProduct.computeReachProbs(product.getProductModel(), acc, minMax,extremeDistr,partitions);
		StateValues probsProduct = StateValues.createFromArrayResult(res, product.getProductModel());

		// Output vector over product, if required
		if (getExportProductVector()) {
			mainLog.println("\nExporting product solution vector matrix to file \"" + getExportProductVectorFilename() + "\"...");
			PrismFileLog out = new PrismFileLog(getExportProductVectorFilename());
			probsProduct.print(out, false, false, false, false);
			out.close();
		}

		// Mapping probabilities in the original model
		StateValues probs = product.projectToOriginalModel(probsProduct);
		probsProduct.clear();

		return probs;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	protected StateValues checkProbPathFormulaCosafeLTL(Model<?> model, Expression expr, boolean qual, MinMax minMax, BitSet statesOfInterest) throws PrismException
	{
		// Build product of IMC and DFA for the LTL formula, and do any required exports
		LTLModelChecker mcLtl = new LTLModelChecker(this);
		LTLModelChecker.LTLProduct<IDTMC<Double>> product = mcLtl.constructDFAProductForCosafetyProbLTL(this, (IDTMC<Double>) model, expr, statesOfInterest);
		doProductExports(product);
		
		// Find accepting states + compute reachability probabilities
		BitSet acc = ((AcceptanceReach)product.getAcceptance()).getGoalStates();
		mainLog.println("\nComputing reachability probabilities...");
		mainLog.println("\n CosafeLTL");

		// build partitions of states
		int numOfPartitions = model.getNumStates(); //Do they start at 0?
		List<Set<Integer>> partitions = new ArrayList<>(numOfPartitions);
		for (int i = 0; i < numOfPartitions; i++) {
			partitions.add(new LinkedHashSet<>());
		}
		for (int i=0; i<product.productModel.getNumStates(); i++){
			partitions.get(product.getModelState(i)).add(i);
		}

		// build extreme distributions
		// index of partition --> list of extreme distributions

//		mainLog.println("numofOriginal " + model.getNumStates());
//		mainLog.println("numofpartitions: " + numOfPartitions);
//		mainLog.println("numofstates: " + product.productModel.getNumStates());
////		for (int i=0; i<product.productModel.getNumStates(); i++){
//////			mainLog.println("iteration:" + i + ", belongs to: " + product.getModelState(i));
////		}
//		mainLog.println("partitions:" + partitions);





		IDTMC<Double> idtmc = (IDTMC<Double>) model;
		double[][][] extremeDistr = new double[model.getNumStates()][][];
		for (int i = 0; i < model.getNumStates(); i++) {
			List<Interval<Double>> intervals = new ArrayList<>();
			List<Integer> targets = new ArrayList<>();
			Iterator<Map.Entry<Integer, Interval<Double>>> iter = idtmc.getTransitionsIterator(i);

			while (iter.hasNext()) {
				Map.Entry<Integer, Interval<Double>> entry = iter.next();
				if (entry.getValue().getLower() > 0.0 || entry.getValue().getUpper() > 0.0) {
					targets.add(entry.getKey());
					intervals.add(entry.getValue());
				}
			}

			if (targets.isEmpty()) {
				extremeDistr[i] = new double[][] { new double[model.getNumStates()] };
				continue;
			}

			//extreme distributions for state i
			UDistributionVertices<Double> uDist = new UDistributionVertices<>(
					Collections.singletonList(intervals),
					Collections.singletonList(i),
					true
			);
			mainLog.println("marginalVertices size: " + uDist.marginalVertices[0][0].length);

			double[][] mappedVertices = new double[uDist.marginalVertices[0].length][model.getNumStates()];
			for (int v = 0; v < uDist.marginalVertices[0].length; v++) {
				double[] fullVec = new double[model.getNumStates()];
				for (int t = 0; t < targets.size(); t++) {
					fullVec[targets.get(t)] = uDist.marginalVertices[0][v][t];
				}
				mappedVertices[v] = fullVec;
			}

			extremeDistr[i] = mappedVertices;
		}




		IDTMCModelChecker mcProduct = new IDTMCModelChecker(this);
		mcProduct.inheritSettings(this);
		ModelCheckerResult res = mcProduct.computeReachProbs(product.getProductModel(), acc, minMax, extremeDistr, partitions);
		StateValues probsProduct = StateValues.createFromArrayResult(res, product.getProductModel());

		// Output vector over product, if required
		if (getExportProductVector()) {
				mainLog.println("\nExporting product solution vector matrix to file \"" + getExportProductVectorFilename() + "\"...");
				PrismFileLog out = new PrismFileLog(getExportProductVectorFilename());
				probsProduct.print(out, false, false, false, false);
				out.close();
		}

		// Mapping probabilities in the original model
		StateValues probs = product.projectToOriginalModel(probsProduct);
		probsProduct.clear();

		return probs;
	}
	
	@Override
	@SuppressWarnings("unchecked")
	protected StateValues checkRewardCoSafeLTL(Model<?> model, Rewards<?> modelRewards, Expression expr, MinMax minMax, BitSet statesOfInterest) throws PrismException
	{
		// Build product of IMC and DFA for the LTL formula, convert rewards and do any required exports
		LTLModelChecker mcLtl = new LTLModelChecker(this);
		LTLModelChecker.LTLProduct<IDTMC<Double>> product = mcLtl.constructDFAProductForCosafetyReward(this, (IDTMC<Double>) model, expr, statesOfInterest);
		MCRewards<Double> productRewards = ((MCRewards<Double>) modelRewards).liftFromModel(product);
		doProductExports(product);

		// Find accepting states + compute reachability rewards
		BitSet acc = ((AcceptanceReach)product.getAcceptance()).getGoalStates();
		mainLog.println("\nComputing reachability rewards...");
		IDTMCModelChecker mcProduct = new IDTMCModelChecker(this);
		mcProduct.inheritSettings(this);
		ModelCheckerResult res = mcProduct.computeReachRewards(product.getProductModel(), productRewards, acc, minMax);
		StateValues rewardsProduct = StateValues.createFromArrayResult(res, product.getProductModel());
		
		// Output vector over product, if required
		if (getExportProductVector()) {
				mainLog.println("\nExporting product solution vector matrix to file \"" + getExportProductVectorFilename() + "\"...");
				PrismFileLog out = new PrismFileLog(getExportProductVectorFilename());
				rewardsProduct.print(out, false, false, false, false);
				out.close();
		}

		// Mapping rewards in the original model
		StateValues rewards = product.projectToOriginalModel(rewardsProduct);
		rewardsProduct.clear();
		
		return rewards;
	}
	
	// Numerical computation functions

	/**
	 * Compute next-state probabilities.
	 * i.e. compute the probability of being in a state in {@code target} in the next step.
	 * @param idtmc The IDTMC
	 * @param target Target states
	 * @param minMax Min/max info
	 */
	public ModelCheckerResult computeNextProbs(IDTMC<Double> idtmc, BitSet target, MinMax minMax) throws PrismException
	{
		long timer = System.currentTimeMillis();

		// Check for any zero lower probability bounds (not supported
		// since this approach assumes the graph structure remains static)
		idtmc.checkLowerBoundsArePositive();
		
		// Store num states
		int n = idtmc.getNumStates();
		PrimitiveIterator.OfInt statesAll = new IterableStateSet(n).iterator();

		// Create/initialise solution vector(s)
		double[] soln = Utils.bitsetToDoubleArray(target, n);
		double[] soln2 = new double[n];

		// Next-step probabilities
		idtmc.mvMultUnc(soln, minMax, soln2, statesAll);

		// Return results
		ModelCheckerResult res = new ModelCheckerResult();
		res.soln = soln2;
		res.accuracy = AccuracyFactory.boundedNumericalIterations();
		res.numIters = 1;
		timer = System.currentTimeMillis() - timer;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Compute bounded reachability probabilities.
	 * i.e. compute the probability of reaching a state in {@code target} within k steps.
	 * @param idtmc The IDTMC
	 * @param target Target states
	 * @param k Bound
	 * @param minMax Min/max info
	 */
	public ModelCheckerResult computeBoundedReachProbs(IDTMC<Double> idtmc, BitSet target, int k, MinMax minMax) throws PrismException
	{
		return computeBoundedUntilProbs(idtmc, null, target, k, minMax);
	}

	/**
	 * Compute bounded until probabilities.
	 * i.e. compute the probability of reaching a state in {@code target},
	 * within k steps, and while remaining in states in {@code remain}.
	 * @param idtmc The IDTMC
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param k Bound
	 * @param minMax Min/max info
	 */
	public ModelCheckerResult computeBoundedUntilProbs(IDTMC<Double> idtmc, BitSet remain, BitSet target, int k, MinMax minMax) throws PrismException
	{
		ModelCheckerResult res = null;
		BitSet unknown;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[];
		long timer;

		// Start bounded probabilistic reachability
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting bounded probabilistic reachability...");

		// Check for any zero lower probability bounds (not supported
		// since this approach assumes the graph structure remains static)
		idtmc.checkLowerBoundsArePositive();
		
		// Store num states
		n = idtmc.getNumStates();

		// Create solution vector(s)
		soln = new double[n];
		soln2 = new double[n];

		// Initialise solution vectors.
		for (i = 0; i < n; i++)
			soln[i] = soln2[i] = target.get(i) ? 1.0 : 0.0;

		// Determine set of states actually need to perform computation for
		unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(target);
		if (remain != null)
			unknown.and(remain);
		IntSet unknownStates = IntSet.asIntSet(unknown);

		// Start iterations
		iters = 0;
		while (iters < k) {
			iters++;
			// Matrix-vector multiply and min/max ops
			idtmc.mvMultUnc(soln, minMax, soln2, unknownStates.iterator());
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished bounded probabilistic reachability
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Bounded probabilistic reachability");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.lastSoln = soln2;
		res.accuracy = AccuracyFactory.boundedNumericalIterations();
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		res.timePre = 0.0;
		return res;
	}
	
	/**
	 * Compute reachability probabilities.
	 * i.e. compute the probability of reaching a state in {@code target}.
	 * @param idtmc The IDTMC
	 * @param target Target states
	 * @param minMax Min/max info
	 */
	public ModelCheckerResult computeReachProbs(IDTMC<Double> idtmc, BitSet target, MinMax minMax,double[][][] extremeDistr, List<Set<Integer>> partitions) throws PrismException
	{
		return computeReachProbs(idtmc, null, target, minMax,extremeDistr, partitions);
	}

	/**
	 * Compute until probabilities.
	 * i.e. compute the probability of reaching a state in {@code target}.
	 * @param idtmc The IDTMC
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param minMax Min/max info
	 */
	public ModelCheckerResult computeUntilProbs(IDTMC<Double> idtmc, BitSet remain, BitSet target, MinMax minMax) throws PrismException
	{
		return computeReachProbs(idtmc, remain, target, minMax, null,null);
	}

	/**
	 * Compute reachability/until probabilities.
	 * i.e. compute the probability of reaching a state in {@code target},
	 * while remaining in those in {@code remain}.
	 * @param idtmc The IDTMC
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param minMax Min/max info
	 */
	public ModelCheckerResult computeReachProbs(IDTMC<Double> idtmc, BitSet remain, BitSet target, MinMax minMax, double[][][] extremeDistr, List<Set<Integer>> partitions) throws PrismException
	{
		// Switch to a supported method, if necessary
		IMDPSolnMethod imdpSolnMethod = this.imdpSolnMethod;
		mainLog.println("imdpSolnMethod: " + imdpSolnMethod);
		switch (imdpSolnMethod)
		{
		case VALUE_ITERATION:
		case GAUSS_SEIDEL:
			break; // supported
		case LINEAR_PROGRAMMING:
			break;
		default:
			imdpSolnMethod = IMDPSolnMethod.GAUSS_SEIDEL;
			mainLog.printWarning("Switching to solution method \"" + imdpSolnMethod.fullName() + "\"");
			mainLog.println("Switching to solution method \"" + imdpSolnMethod.fullName() + "\"");
		}

		// Start probabilistic reachability
		long timer = System.currentTimeMillis();
		mainLog.println("\nStarting probabilistic reachability...");

		// Check for any zero lower probability bounds (not supported
		// since this approach assumes the graph structure remains static)
		idtmc.checkLowerBoundsArePositive();
		
		// Check for deadlocks in non-target state (because breaks e.g. prob1)
		idtmc.checkForDeadlocks(target);

		// Store num states
		int n = idtmc.getNumStates();

		// Precomputation
		BitSet no, yes;
		PredecessorRelation pre = null;
		if (precomp && (prob0 || prob1) && preRel) {
			pre = idtmc.getPredecessorRelation(this, true);
		}
		if (precomp && prob0) {
			if (preRel) {
				no = mcDTMC.prob0(idtmc, remain, target, pre);
			} else {
				no = mcDTMC.prob0(idtmc, remain, target);
			}
		} else {
			no = new BitSet();
		}
		if (precomp && prob1) {
			if (preRel) {
				yes = mcDTMC.prob1(idtmc, remain, target, pre);
			} else {
				yes = mcDTMC.prob1(idtmc, remain, target);
			}
		} else {
			yes = (BitSet) target.clone();
		}

		// Print results of precomputation
		int numYes = yes.cardinality();
		int numNo = no.cardinality();
		mainLog.println("target=" + target.cardinality() + ", yes=" + numYes + ", no=" + numNo + ", maybe=" + (n - (numYes + numNo)));

		// Start value iteration
		timer = System.currentTimeMillis();
		String sMinMax = minMax.isMinUnc() ? "min" : "max";
		mainLog.println("Starting value iteration (" + sMinMax + ")...");

		// Store num states
		n = idtmc.getNumStates();

		// Initialise solution vectors
		double[] init = new double[n];
		for (int i = 0; i < n; i++)
			init[i] = yes.get(i) ? 1.0 : no.get(i) ? 0.0 : 0.0;

		// Determine set of states actually need to compute values for
		BitSet unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(yes);
		unknown.andNot(no);

		// Compute probabilities (if needed)
		ModelCheckerResult res;
		double[] soln = null;
		if (numYes + numNo < n) {
			IterationMethod iterationMethod = null;
			switch (imdpSolnMethod) {
			case VALUE_ITERATION:
				iterationMethod = new IterationMethodPower(termCrit == TermCrit.ABSOLUTE, termCritParam);
				break;
			case GAUSS_SEIDEL:
				iterationMethod = new IterationMethodGS(termCrit == TermCrit.ABSOLUTE, termCritParam, false);
				break;
				case  LINEAR_PROGRAMMING:
					//int[] strat = null;
					soln = solveReachProbsLPWithGurobi(idtmc,no, yes, unknown, extremeDistr, partitions, minMax.isMinUnc(), null); //double[][][] extremeDistr,List<Set<Integer>> partitions ,boolean min, int strat[]
					timer = System.currentTimeMillis() - timer;
					mainLog.print("Linear programming");
					mainLog.println(" took " + timer / 1000.0 + " seconds.");

					// Return results
					// (Note we don't add the strategy - the one passed in is already there
					// and might have some existing choices stored for other states).
					res = new ModelCheckerResult();
					res.soln = soln;
					res.accuracy = new Accuracy(Accuracy.AccuracyLevel.EXACT_FLOATING_POINT);
					res.timeTaken = timer / 1000.0;
					return res;
			default:
				throw new PrismException("Unknown solution method " + imdpSolnMethod.fullName());
			}
			IterationMethod.IterationValIter iterationReachProbs = iterationMethod.forMvMultMinMaxUnc(idtmc, minMax);
			iterationReachProbs.init(init);
			IntSet unknownStates = IntSet.asIntSet(unknown);
			String description = sMinMax + ", with " + iterationMethod.getDescriptionShort();
			res = iterationMethod.doValueIteration(this, description, iterationReachProbs, unknownStates, timer, null);
		} else {
			res = new ModelCheckerResult();
			res.soln = Utils.bitsetToDoubleArray(yes, n);
			res.accuracy = AccuracyFactory.doublesFromQualitative();
		}
		
		// Finished probabilistic reachability
		timer = System.currentTimeMillis() - timer;
		mainLog.println("Probabilistic reachability took " + timer / 1000.0 + " seconds.");

		// Update time taken
		res.timeTaken = timer / 1000.0;

		return res;
	}
	
	/**
	 * Compute expected reachability rewards.
	 * @param idtmc The IDTMC
	 * @param imcRewards The rewards
	 * @param target Target states
	 * @param minMax Min/max info
	 */
	public ModelCheckerResult computeReachRewards(IDTMC<Double> idtmc, MCRewards<Double> imcRewards, BitSet target, MinMax minMax) throws PrismException
	{
		// Switch to a supported method, if necessary
		IMDPSolnMethod imdpSolnMethod = this.imdpSolnMethod;
		switch (imdpSolnMethod)
		{
		case VALUE_ITERATION:
		case GAUSS_SEIDEL:
			break; // supported
		default:
			imdpSolnMethod = IMDPSolnMethod.GAUSS_SEIDEL;
			mainLog.printWarning("Switching to solution method \"" + imdpSolnMethod.fullName() + "\"");
		}

		// Start probabilistic reachability
		long timer = System.currentTimeMillis();
		mainLog.println("\nStarting expected reachability...");

		// Check for any zero lower probability bounds (not supported
		// since this approach assumes the graph structure remains static)
		idtmc.checkLowerBoundsArePositive();
		
		// Check for deadlocks in non-target state (because breaks e.g. prob1)
		idtmc.checkForDeadlocks(target);

		// Store num states
		int n = idtmc.getNumStates();

		// Precomputation (not optional)
		BitSet inf;
		if (preRel) {
			// prob1 via predecessor relation
			PredecessorRelation pre = idtmc.getPredecessorRelation(this, true);
			inf = mcDTMC.prob1(idtmc, null, target, pre);
		} else {
			// prob1 via fixed-point algorithm
			inf = mcDTMC.prob1(idtmc, null, target);
		}
		inf.flip(0, n);

		// Print results of precomputation
		int numTarget = target.cardinality();
		int numInf = inf.cardinality();
		mainLog.println("target=" + numTarget + ", inf=" + numInf + ", rest=" + (n - (numTarget + numInf)));

		// Start value iteration
		timer = System.currentTimeMillis();
		String sMinMax = minMax.isMinUnc() ? "min" : "max";
		mainLog.println("Starting value iteration (" + sMinMax + ")...");

		// Store num states
		n = idtmc.getNumStates();

		// Initialise solution vectors
		double[] init = new double[n];
		for (int i = 0; i < n; i++)
			init[i] = target.get(i) ? 0.0 : inf.get(i) ? Double.POSITIVE_INFINITY : 0.0;

		// Determine set of states actually need to compute values for
		BitSet unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(target);
		unknown.andNot(inf);

		// Compute probabilities (if needed)
		ModelCheckerResult res;
		if (numTarget + numInf < n) {
			IterationMethod iterationMethod = null;
			switch (imdpSolnMethod) {
			case VALUE_ITERATION:
				iterationMethod = new IterationMethodPower(termCrit == TermCrit.ABSOLUTE, termCritParam);
				break;
			case GAUSS_SEIDEL:
				iterationMethod = new IterationMethodGS(termCrit == TermCrit.ABSOLUTE, termCritParam, false);
				break;
			default:
				throw new PrismException("Unknown solution method " + imdpSolnMethod.fullName());
			}
			IterationMethod.IterationValIter iterationReachProbs = iterationMethod.forMvMultRewMinMaxUnc(idtmc, imcRewards, minMax);
			iterationReachProbs.init(init);
			IntSet unknownStates = IntSet.asIntSet(unknown);
			String description = sMinMax + ", with " + iterationMethod.getDescriptionShort();
			res = iterationMethod.doValueIteration(this, description, iterationReachProbs, unknownStates, timer, null);
		} else {
			res = new ModelCheckerResult();
			res.soln = Utils.bitsetToDoubleArray(inf, n, Double.POSITIVE_INFINITY);
			res.accuracy = AccuracyFactory.doublesFromQualitative();
		}
		
		// Finished probabilistic reachability
		timer = System.currentTimeMillis() - timer;
		mainLog.println("Probabilistic reachability took " + timer / 1000.0 + " seconds.");

		// Update time taken
		res.timeTaken = timer / 1000.0;

		return res;
	}

	/**
	 * Solve the linear program for reachability probabilities with Gurobi.
	 * @param idtmc: The IDTMC
	 * @param no: Probability 0 states
	 * @param yes: Probability 1 states
	 * @param min: Min or max probabilities (true=min, false=max)
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 */
	protected double[] solveReachProbsLPWithGurobi(IDTMC<Double> idtmc, BitSet no, BitSet yes, BitSet unknown, double[][][] extremeDistr,List<Set<Integer>> partitions ,boolean min, int strat[]) throws PrismException
	{
		double[] soln = null;

		//inverse partition
		int n = idtmc.getNumStates();
		List<Integer> inversePartition = new ArrayList<>(Collections.nCopies(idtmc.getNumStates(), -1));
		for (int i = 0; i < partitions.size(); i++) {
			for (int val : partitions.get(i)) {
				inversePartition.set(val, i);
			}
		}
		mainLog.println("inversePartition=" + inversePartition);

		//getActionVars
		Map<Integer, Map<Integer, Integer>> getAction = new HashMap<>();
		int actionVarsCount = 0;
		mainLog.println("partitions.size()=" + partitions.size());
		mainLog.println("extremeDistr.length=" + extremeDistr.length);
		mainLog.println("idtmc.numstates" + idtmc.getNumStates());
		for (int x=0; x <partitions.size(); x++) {
			if (extremeDistr[x].length>1){
				for (int a=0; a<extremeDistr[x].length; a++) {
					getAction.computeIfAbsent(x, k -> new HashMap<>()).put(a, n+actionVarsCount);
					actionVarsCount++;
				}
			}
		}
		mainLog.println("getAction in LP: " + getAction);
		mainLog.println("actionVarsCount=" + actionVarsCount);



		// old here:




		//make sure there is exactly 1 initial state
		Iterable<Integer> initialStates= idtmc.getInitialStates();
		int count = 0;
		for (Integer state : idtmc.getInitialStates()) {count++;}
		if (count != 1){throw new PrismException("Wrong number of initial states");}

		// build support
		List<Set<Integer>> supportProd = new ArrayList<>();
		for (int i=0; i<idtmc.getNumStates(); i++) {
			supportProd.add(new LinkedHashSet<>());
		}

		for  (int i=0; i<idtmc.getNumStates(); i++){
			//int j = partitions.get(i).iterator().next();
			Iterator<Map.Entry<Integer, Interval<Double>>> iter = idtmc.getTransitionsIterator(i);
			while (iter.hasNext()) {
				Map.Entry<Integer, Interval<Double>> entry = iter.next();
				Interval<Double> interval = entry.getValue();
				if (interval != null && (interval.getLower() > 0.0 || interval.getUpper() > 0.0)) {
					supportProd.get(i).add(entry.getKey());
				}
			}
		}
		mainLog.println("supportProd: " + supportProd);

		List<Set<Integer>> supportOriginal = new ArrayList<>();
		for (int i=0; i<partitions.size(); i++) {
			supportOriginal.add(new LinkedHashSet<>());
		}
		for  (int i=0; i<idtmc.getNumStates(); i++){
			Set<Integer> prodSupports = supportProd.get(i);
			int originalState = inversePartition.get(i);
			for (int prodState:  prodSupports) {
				supportOriginal.get(originalState).add(inversePartition.get(prodState));
			}
		}
		mainLog.println("support: " + supportOriginal);



		//


		int addVarsCount = 0;
		Map<Integer, Map<Integer, Map<Integer,Integer>>> getExtraVar = new HashMap<>();
		for (int x=0; x <partitions.size(); x++) {
			if (extremeDistr[x].length > 1) {
				for (int a=0; a<extremeDistr[x].length; a++) {
					for (int y: supportOriginal.get(x)) {
						for (int z:partitions.get(y)){
							if (!no.get(z) && !yes.get(z)){
								 getExtraVar.computeIfAbsent(x, k -> new HashMap<>()).computeIfAbsent(a, k -> new HashMap<>()).put(z, n+actionVarsCount+addVarsCount);
								 addVarsCount ++;
							}
						}
					}
				}
			}
		}
		mainLog.println("getExtraVar: " + getExtraVar);
		mainLog.println("addVarsCount: " + addVarsCount);





		try {
			// Initialise LP solver
			GRBEnv env = new GRBEnv("gurobi.log");
			env.set(GRB.IntParam.OutputFlag, 1);
			GRBModel model = new GRBModel(env);
			// Set up LP variables + objective function
			GRBVar xVars[] = new GRBVar[n+actionVarsCount+addVarsCount];



			for (int s = 0; s < n; s++) {
				xVars[s] = model.addVar(0.0, 1.0, idtmc.isInitialState(s) ? 1.0 : 0.0, GRB.CONTINUOUS, "x" + s);
			}
			for (int s = 0; s < actionVarsCount; s++) {
				xVars[n+s] = model.addVar(0.0, 1.0,  0.0, GRB.BINARY, "a" + s);
			}
			for (int s = 0; s < addVarsCount; s++) {
				xVars[n+actionVarsCount+s] = model.addVar(0.0, 1.0, 0.0, GRB.CONTINUOUS, "z" + s);
			}
			model.set(GRB.IntAttr.ModelSense, min ? 1 : -1);

			int counter = 0;
			//set up integer constraints
			int positionCounter = n;

			// sum of action constraints
			for (int m = 0; m < partitions.size(); m++) {
				if (extremeDistr[m].length > 1){
					GRBLinExpr expr = new GRBLinExpr();
					for (int v = 0; v < extremeDistr[m].length; v++) {
						expr.addTerm(1.0, xVars[positionCounter]);
						positionCounter++;
					}
					model.addConstr(expr, GRB.EQUAL, 1.0, "c" + counter++);
				}
			}


			// added constraints for extra variables, such that ...
			for (int x=0; x <partitions.size(); x++) {
				if (extremeDistr[x].length > 1) {
					for (int a=0; a<extremeDistr[x].length; a++) {
						int alpha = getAction.get(x).get(a);
						for (int y: supportOriginal.get(x)) {
							for (int z:partitions.get(y)){
								if (!no.get(z) && !yes.get(z)){
									int posZ =getExtraVar.get(x).get(a).get(z);

									//x = z
									GRBLinExpr expr1 = new GRBLinExpr();
									expr1.addTerm(1.0, xVars[posZ]);
									expr1.addTerm(-1.0, xVars[alpha]);
									model.addConstr(expr1, GRB.LESS_EQUAL, 0.0, "c" + counter++);
											//computeIfAbsent(x, k -> new HashMap<>()).computeIfAbsent(a, k -> new HashMap<>()).put(z, n+actionVarsCount+addVarsCount);
									GRBLinExpr expr2 = new GRBLinExpr();
									expr2.addTerm(1.0, xVars[posZ]);
									expr2.addTerm(-1.0, xVars[z]);
									model.addConstr(expr2, GRB.LESS_EQUAL, 0.0, "c" + counter++);

									GRBLinExpr expr3 = new GRBLinExpr();
									expr3.addTerm(1.0, xVars[posZ]);
									expr3.addTerm(-1.0, xVars[z]);
									expr3.addTerm(-1.0, xVars[alpha]);
									model.addConstr(expr3, GRB.GREATER_EQUAL, -1.0, "c" + counter++);
								}
							}
						}
					}
				}
			}



			/
			double row[] = new double[n + 1];
			int colno[] = new int[n + 1];
			// Add constraints
			mainLog.println("counter before adding traditional constraints:" + counter);
			mainLog.println("yes:" + yes);
			mainLog.println("no:" + no);

			for (int s = 0; s < n; s++) {
				if (yes.get(s)) {
					GRBLinExpr expr = new GRBLinExpr();
					expr.addTerm(1.0, xVars[s]);
					model.addConstr(expr, GRB.EQUAL, 1.0, "c" + counter++);
					mainLog.println("Added constaint for" + s + ", counter:" + counter);
				} else if (no.get(s)) {
					GRBLinExpr expr = new GRBLinExpr();
					expr.addTerm(1.0, xVars[s]);
					model.addConstr(expr, GRB.EQUAL, 0.0, "c" + counter++);
					mainLog.println("Added constaint for" + s + ", counter:" + counter);
				} else {
					GRBLinExpr expr = new GRBLinExpr();
					expr.addTerm(1.0, xVars[s]);


					if(extremeDistr[inversePartition.get(s)].length ==1){
						//first Case, only 1 action

						Set<Integer> set = supportProd.get(s);
						for (int i: set) {
							double coeff =- extremeDistr[inversePartition.get(s)][0][inversePartition.get(i)];
							expr.addTerm(coeff, xVars[i]);
							mainLog.print(coeff);
						}
						mainLog.println("Added for single successor");

					} else if (extremeDistr[inversePartition.get(s)].length >1) {
						Set<Integer> successor = supportProd.get(s);
						for (int ithSuccessor: successor ) {
							if (yes.get(ithSuccessor)){
								for (int a = 0; a < extremeDistr[inversePartition.get(s)].length; a++) {
									double coeff = - extremeDistr[inversePartition.get(s)][a][inversePartition.get(ithSuccessor)];

									expr.addTerm(coeff, xVars[getAction.get(inversePartition.get(s)).get(a)]);

								}
								mainLog.println("ithSuccessor is:" + ithSuccessor);
							} else if(!no.get(ithSuccessor)){
								for (int a = 0; a < extremeDistr[inversePartition.get(s)].length; a++) {
									double coeff =- extremeDistr[inversePartition.get(s)][a][inversePartition.get(ithSuccessor)];
									expr.addTerm(coeff, xVars[getExtraVar.get(inversePartition.get(s)).get(a).get(ithSuccessor)]);
								}
								mainLog.println("ithSuccessor in ? is :" + ithSuccessor);
							}
						}
					}

					model.addConstr(expr, GRB.EQUAL, 0.0, "c" + counter++);
					mainLog.println("Added constaint for" + s + ",in ExtraWork counter:" + counter);
				}
			}
			// Solve LP
			model.write("gurobi.lp");

			model.optimize();
			if (model.get(GRB.IntAttr.Status) == GRB.Status.OPTIMAL) {
				soln = new double[n];
				for (int s = 0; s < n; s++) {
					soln[s] = xVars[s].get(GRB.DoubleAttr.X);
				}
			} else {
				throw new PrismException("Error solving LP" + (model.get(GRB.IntAttr.Status) == GRB.Status.INFEASIBLE ? " (infeasible)" : ""));
			}
			// Clean up
			model.dispose();
			env.dispose();
			// Return solution
			return soln;
		} catch (GRBException e) {
			throw new PrismException("Error solving LP: " +e.getMessage());
		}
	}
}

