module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_e5494400a9c5cce1bb40_Symbol ====
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
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# One-dimensional kernels with symbol `exp(-t ξ^{2j})`

`symKernel j t b = ∫ exp(-t ξ^{2j}) cos(2π ξ b) dξ` is the real, even inverse Fourier transform of
the symbol `ξ ↦ exp(-t ξ^{2j})`. For `j = 1` it is a Gaussian (the 1D heat kernel) and for `j = 2`
it is the quartic kernel of `∂_t + ∂_b⁴`. For `t > 0` it is the (real part of the) Schwartz
function `𝓕⁻ (exp(-t ξ^{2j}))`; we prove continuity, integrability, `∫ = 1`, the semigroup
property `k_s ⋆ k_t = k_{s+t}` and rapid decay of `k_1` and `k_1'`, using
`Mathlib.Analysis.Distribution.SchwartzSpace.Fourier` and `Mathlib.Analysis.Fourier.Convolution`.
This is the 1D building block of the auxiliary semigroup of [Hos25, Example 2.7]
(arXiv:2310.07396v2).
-/
@[expose] public noncomputable section
open MeasureTheory Real
namespace RegularityStructures

end RegularityStructures
end
public section
open MeasureTheory Real SchwartzMap
open scoped FourierTransform
namespace RegularityStructures
variable {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j)


theorem abs_le_mul_one_add_rpow_neg {f : ℝ → ℝ} {g : ℝ → ℂ} (hfg : ∀ x, |f x| ≤ ‖g x‖)
    (hg : ∀ n : ℕ, ∃ C : ℝ, ∀ x, (1 + |x|) ^ n * ‖g x‖ ≤ C) (n : ℕ) :
    ∃ C : ℝ, ∀ x, |f x| ≤ C * (1 + |x|) ^ (-(n : ℝ)) := by
  obtain ⟨C, hC⟩ := hg n
  refine ⟨C, fun x => ?_⟩
  have hpos : 0 < (1 + |x|) ^ n := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc |f x| * (1 + |x|) ^ n ≤ ‖g x‖ * (1 + |x|) ^ n := by gcongr; exact hfg x
    _ = (1 + |x|) ^ n * ‖g x‖ := mul_comm _ _
    _ ≤ C := hC x

end RegularityStructures
end
