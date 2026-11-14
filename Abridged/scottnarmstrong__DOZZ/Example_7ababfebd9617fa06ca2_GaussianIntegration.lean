module

public import Mathlib
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Probability.Independence.Process.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Cover
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompleteLattice.Group
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.EMetricSpace.PairReduction
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

-- ==== Examples.scottnarmstrong__DOZZ.Examples.Example_7ababfebd9617fa06ca2_GaussianIntegration ====
/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Gaussian Bochner integrals in the given L² space

The closed linear span of one jointly Gaussian family remains Gaussian. Hilbert projections
keep deterministic integrals in that span. Scalar product Fubini identifies the resulting
representative with the literal samplewise integral used in the off-center decomposition.
-/
@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


set_option linter.unusedVariables false in
/-- A jointly measurable representative of an integrable L²-valued family is product
integrable. This proves the Fubini premise rather than assuming it. -/
theorem integrable_L2_representative_prod {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [SFinite μ] (F : A → Lp ℝ 2 P) (hF : Integrable F μ)
    (f : A → Ω → ℝ) (hm : AEStronglyMeasurable (Function.uncurry f) (μ.prod P))
    (heq : ∀ a, (⇑(F a)) =ᵐ[P] f a) 
    (h_DOZZ_Proofs_integral_norm_L2_le : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
      [MeasureTheory.IsProbabilityMeasure P] (U : ↥(MeasureTheory.Lp ℝ 2 P)),
      ∫ (ω : Ω), ‖(↑(↑U : Ω →ₘ[P] ℝ) : Ω → ℝ) ω‖ ∂P ≤ ‖U‖)
    : Integrable (Function.uncurry f) (μ.prod P) := by
  apply (integrable_prod_iff hm).mpr
  refine ⟨Eventually.of_forall (fun a => ((Lp.memLp (F a)).integrable (by norm_num)).congr (heq a)), ?_⟩
  apply hF.norm.mono' hm.norm.integral_prod_right'
  apply Eventually.of_forall
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ω => norm_nonneg (f a ω)))]
  calc
    _ = ∫ ω, ‖F a ω‖ ∂P := integral_congr_ae ((heq a).fun_comp norm).symm
    _ ≤ ‖F a‖ := h_DOZZ_Proofs_integral_norm_L2_le (F a)
end DOZZ.Proofs
