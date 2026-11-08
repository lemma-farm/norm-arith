module
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.GaussianDifferentiation
public import Mathlib
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
/-!
# Strict positivity of odd-function Gaussian expectations

For a positive Gaussian mean, reflection makes an odd function's expectation
positive when it is strictly positive on the positive half-line. The proof
uses genuine Gaussian densities and Lebesgue integrals. The full-line
symmetrization avoids auxiliary set-integral boundary arguments.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
theorem gaussian_shift_law (h t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1).map (fun z => h + Real.sqrt t * z) = gaussianReal h t.toNNReal := by
  have he : (fun z : ℝ => h + Real.sqrt t * z) =
      (fun y : ℝ => h + y) ∘ (fun z : ℝ => Real.sqrt t * z) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  simp only [mul_zero, zero_add, mul_one]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mk, Real.coe_toNNReal t ht]
  exact Real.sq_sqrt ht
/-- Rewriting a concrete affine Gaussian expectation as an integral against
its Gaussian image measure. -/
theorem gaussianExpectation_shift_eq_integral
    (h t : ℝ) (ht : 0 ≤ t) (g : ℝ → ℝ) (hg : Measurable g) :
    gaussianExpectation (fun z => g (h + Real.sqrt t * z)) =
      ∫ y, g y ∂gaussianReal h t.toNNReal := by
  unfold gaussianExpectation
  rw [← gaussian_shift_law h t ht]
  exact (integral_map (by fun_prop) hg.aestronglyMeasurable).symm
end Paper
