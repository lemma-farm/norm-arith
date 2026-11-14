module

public import Mathlib
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fin.Rev
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.LinearCombination
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
public import Mathlib.Topology.MetricSpace.Bounded

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_77dc75e288693bd3fa29_ApproximateFlowFromSlabComparisons ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Approximate composition from three slab comparisons -/
@[expose] public noncomputable section
open MeasureTheory Filter

open scoped CompactlySupported Topology ENNReal
namespace Critical2DKPZ.SHF.Flow
private theorem sq_sub_le_three_sq_errors (a b c d : ℝ) :
    (a - d) ^ 2 ≤ 3 * ((a - b) ^ 2 + (b - c) ^ 2 + (d - c) ^ 2) := by
  nlinarith only [sq_nonneg ((a - b) - (b - c)),
    sq_nonneg ((a - b) + (d - c)), sq_nonneg ((b - c) + (d - c))]
end Critical2DKPZ.SHF.Flow
