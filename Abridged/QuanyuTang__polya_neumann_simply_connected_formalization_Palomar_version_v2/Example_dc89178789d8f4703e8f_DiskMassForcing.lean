module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

-- ==== Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Examples.Example_dc89178789d8f4703e8f_DiskMassForcing ====
/-!
# One full Sobolev derivative from physical disk mass forcing

The nonzero-mode coefficient has multiplier sqrt(1+|n|)/(sqrt(2π)|n|).
The area Bessel estimate bounds the entire H¹ Fourier norm, rather than
only the individual coefficients. Frequency zero is removed explicitly.
-/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open MeasureTheory Set Metric Real
open scoped ComplexConjugate
def diskMassForcingScale (m : ℕ) : ℝ :=
  Real.sqrt ((m + 2 : ℕ) : ℝ) / (Real.sqrt (2 * π) * ((m + 1 : ℕ) : ℝ))

set_option linter.unusedVariables false in
private theorem diskMassForcing_sector (M : ℕ → ℂ) (B : ℝ)
    (hs : Summable (fun m => ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2))
    (hB : (∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2) ≤ π * B) 
    (h_PolyaNeumann_diskMassForcingScale_weight : ∀ (m : ℕ) (a : ℂ),
      ((↑(m + 2) : ℝ) * ‖(↑(PolyaNeumann.diskMassForcingScale m) : ℂ) * a‖) ^ 2 ≤
        4 / (2 * Real.pi) * ((↑(m + 2) : ℝ) * ‖a‖ ^ 2))
    :
    Summable (fun m => (((m + 2 : ℕ) : ℝ) *
      ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2) ∧
    (∑' m : ℕ, (((m + 2 : ℕ) : ℝ) *
      ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2) ≤ 2 * B := by
  let f : ℕ → ℝ := fun m => ((m + 1 : ℕ) : ℝ) * ‖M m‖ ^ 2
  let e : ℕ → ℝ := fun m => (((m + 2 : ℕ) : ℝ) *
    ‖(diskMassForcingScale m : ℂ) * M (m + 1)‖) ^ 2
  have hi : Function.Injective (fun m : ℕ => m + 1) := by
    intro m n h
    change m + 1 = n + 1 at h
    exact Nat.add_right_cancel h
  have ht : Summable (fun m : ℕ => f (m + 1)) := hs.comp_injective hi
  have htail : (∑' m : ℕ, f (m + 1)) ≤ π * B :=
    (tsum_comp_le_tsum_of_inj hs (fun m => by positivity) hi).trans hB
  have he (m : ℕ) : e m ≤ (4 / (2 * π)) * f (m + 1) := by
    simpa only [e, f, Nat.add_assoc] using h_PolyaNeumann_diskMassForcingScale_weight m (M (m + 1))
  have hse : Summable e := Summable.of_nonneg_of_le (fun m => sq_nonneg _) he
    (ht.mul_left (4 / (2 * π)))
  refine ⟨hse, ?_⟩
  calc
    _ ≤ ∑' m : ℕ, (4 / (2 * π)) * f (m + 1) :=
      hse.tsum_le_tsum he (ht.mul_left _)
    _ = (4 / (2 * π)) * ∑' m : ℕ, f (m + 1) := tsum_mul_left
    _ ≤ (4 / (2 * π)) * (π * B) := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 2 * B := by field_simp [Real.pi_ne_zero]; ring
end PolyaNeumann
end
