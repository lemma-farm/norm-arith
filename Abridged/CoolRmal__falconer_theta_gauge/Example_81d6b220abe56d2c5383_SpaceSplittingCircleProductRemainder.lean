module

public import Mathlib
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Image
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.Regular
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.PSeries
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- ==== Examples.CoolRmal__falconer_theta_gauge.Examples.Example_81d6b220abe56d2c5383_SpaceSplittingCircleProductRemainder ====
set_option autoImplicit false
/-! # The true averaged product of the circular stationary remainders is negligible -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
theorem norm_circle_product_sub_stationary_product_le {Ix Iy Mx My : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hx : ‖Ix‖ ≤ 2 * Real.pi) (hy : ‖Iy‖ ≤ 2 * Real.pi)
    (hex : ‖Ix - Mx‖ ≤ δ) (hey : ‖Iy - My‖ ≤ δ) :
    ‖Ix * Iy - Mx * My‖ ≤ (4 * Real.pi + δ) * δ := by
  have hMx : ‖Mx‖ ≤ 2 * Real.pi + δ := by
    have h' := norm_add_le (Mx - Ix) Ix
    rw [sub_add_cancel, norm_sub_rev] at h'
    linarith
  have heq : Ix * Iy - Mx * My = (Ix - Mx) * Iy + Mx * (Iy - My) := by ring
  rw [heq]
  calc
    _ ≤ ‖Ix - Mx‖ * ‖Iy‖ + ‖Mx‖ * ‖Iy - My‖ := by
      simpa only [norm_mul] using norm_add_le ((Ix - Mx) * Iy) (Mx * (Iy - My))
    _ ≤ δ * (2 * Real.pi) + (2 * Real.pi + δ) * δ :=
      add_le_add (mul_le_mul hex hy (norm_nonneg _) hδ)
        (mul_le_mul hMx hey (norm_nonneg _) (by positivity))
    _ = _ := by ring
end FalconerThetaGauge
