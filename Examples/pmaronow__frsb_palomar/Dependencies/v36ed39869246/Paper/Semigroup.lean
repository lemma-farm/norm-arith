module
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
/-!
# Symmetric Markov kernels and the contraction in Proposition 5.5

This file proves the paper's double-integral identity for genuine Bochner
integrals. It separates the universal measure-theoretic step from the analytic
verification that the Gaussian kernel and the paper's functions satisfy the
hypotheses. Product integrability is explicit, rather than implicit in a
formal use of Fubini's theorem.
-/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace Paper
section Kernel
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
/-- Integration against a real-valued kernel. -/
def kernelAverage (φ : α → α → ℝ) (k : α → ℝ) (x : α) : ℝ :=
  ∫ y, φ x y * k y ∂μ
theorem kernel_cross_integral
    (φ : α → α → ℝ) (w k : α → ℝ)
    (hcross : Integrable (fun z : α × α => φ z.1 z.2 * w z.1 * k z.2) (μ.prod μ)) :
    (∫ z : α × α, φ z.1 z.2 * w z.1 * k z.2 ∂μ.prod μ) =
      ∫ x, w x * kernelAverage (μ := μ) φ k x ∂μ := by
  rw [integral_prod _ hcross]
  apply integral_congr_ae
  filter_upwards with x
  calc
    (∫ y, φ x y * w x * k y ∂μ) = ∫ y, w x * (φ x y * k y) ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = w x * kernelAverage (μ := μ) φ k x := by
      rw [integral_const_mul]
      rfl
end Kernel
section Gaussian
open ProbabilityTheory
/-- The Gaussian heat kernel with variance `v`. The Markov normalization is
valid for `v ≠ 0`; the paper handles time zero separately. -/
def heatKernel (v : ℝ≥0) (x y : ℝ) : ℝ :=
  gaussianPDFReal 0 v (x - y)
/-- The centered difference form equals the Gaussian density with mean `x`. -/
theorem heatKernel_eq_gaussianPDFReal (v : ℝ≥0) (x y : ℝ) :
    heatKernel v x y = gaussianPDFReal x v y := by
  unfold heatKernel gaussianPDFReal
  simp only [sub_zero]
  rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]
/-- The Gaussian heat kernel is nonnegative. -/
theorem heatKernel_nonneg (v : ℝ≥0) (x y : ℝ) : 0 ≤ heatKernel v x y :=
  gaussianPDFReal_nonneg 0 v (x - y)
/-- Joint measurability of the Gaussian heat kernel. -/
theorem measurable_heatKernel (v : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => heatKernel v z.1 z.2) :=
  (measurable_gaussianPDFReal 0 v).comp (measurable_fst.sub measurable_snd)
/-- Symmetry of the Gaussian heat kernel. -/
theorem heatKernel_symm (v : ℝ≥0) (x y : ℝ) :
    heatKernel v x y = heatKernel v y x := by
  unfold heatKernel gaussianPDFReal
  simp only [sub_zero]
  rw [show (x - y) ^ 2 = (y - x) ^ 2 by ring]
/-- Each positive-variance Gaussian heat-kernel row integrates to one. -/
theorem integral_heatKernel_eq_one (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    (∫ y, heatKernel v x y) = 1 := by
  simp_rw [heatKernel_eq_gaussianPDFReal]
  exact integral_gaussianPDFReal_eq_one x hv
end Gaussian
end Paper
