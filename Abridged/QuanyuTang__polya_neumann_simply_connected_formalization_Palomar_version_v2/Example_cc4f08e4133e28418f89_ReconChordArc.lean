module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic
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

-- ==== Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Examples.Example_cc4f08e4133e28418f89_ReconChordArc ====
/-!
# Lipschitz extension of boundary traces

For a bounded Lipschitz domain `Ω` with boundary parametrization `γ`, the parametrization is
bi-Lipschitz onto `∂Ω` (with respect to the distance on the circle, `chord_arc`), so every
closed Lipschitz function `h` on `[0, 2π]` is the trace `V ∘ γ` of a Lipschitz compactly
supported `V : ℂ → ℂ` (`exists_lipschitz_extension_of_trace`).

The chord-arc estimate is proved locally in a boundary chart: there the boundary is a Lipschitz
graph, the abscissa `x(s)` of `γ(s)` is strictly monotone, and the constant speed of `γ`
together with the cone condition `|γ'| ≤ (1 + K)|x'|` gives `|x'| ≥ c₀/(1 + K)`. A compactness
argument makes the estimate global.
-/
@[expose] public section
open MeasureTheory Set Filter Metric Topology
open scoped ComplexConjugate Real
noncomputable section
namespace PolyaNeumann
variable {Ω : Set ℂ} {γ : ℝ → ℂ}
def circDist (θ θ' : ℝ) : ℝ := min |θ - θ'| (2 * π - |θ - θ'|)
/-- A closed Lipschitz function on `[0, 2π]` is Lipschitz for the circle distance. -/
lemma norm_sub_le_circDist {h : ℝ → ℂ} {K : NNReal} (hK : LipschitzOnWith K h (Icc 0 (2 * π)))
    (hper : h (2 * π) = h 0) {θ θ' : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) (hθ' : θ' ∈ Icc 0 (2 * π)) :
    ‖h θ - h θ'‖ ≤ K * circDist θ θ' := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hd : ∀ x ∈ Icc (0 : ℝ) (2 * π), ∀ y ∈ Icc (0 : ℝ) (2 * π), ‖h x - h y‖ ≤ K * |x - y| :=
    fun x hx y hy => by
      have := hK.dist_le_mul x hx y hy
      rwa [dist_eq_norm, Real.dist_eq] at this
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * π) := ⟨le_rfl, h2π.le⟩
  have h1 : 2 * π ∈ Icc (0 : ℝ) (2 * π) := ⟨h2π.le, le_rfl⟩
  unfold circDist
  rw [mul_min_of_nonneg _ _ (NNReal.coe_nonneg K)]
  refine le_min (hd θ hθ θ' hθ') ?_
  rcases le_total θ θ' with hle | hle
  · have e : h θ - h θ' = (h θ - h 0) + (h (2 * π) - h θ') := by rw [hper]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have a1 := hd θ hθ 0 h0
    have a2 := hd (2 * π) h1 θ' hθ'
    rw [abs_of_nonpos (by linarith)]
    rw [sub_zero, abs_of_nonneg hθ.1] at a1
    rw [abs_of_nonneg (by linarith [hθ'.2])] at a2
    nlinarith
  · have e : h θ - h θ' = (h θ - h (2 * π)) + (h 0 - h θ') := by rw [hper]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have a1 := hd θ hθ (2 * π) h1
    have a2 := hd 0 h0 θ' hθ'
    rw [abs_of_nonneg (by linarith)]
    rw [abs_of_nonpos (by linarith [hθ.2])] at a1
    rw [zero_sub, abs_neg, abs_of_nonneg hθ'.1] at a2
    nlinarith
end PolyaNeumann
