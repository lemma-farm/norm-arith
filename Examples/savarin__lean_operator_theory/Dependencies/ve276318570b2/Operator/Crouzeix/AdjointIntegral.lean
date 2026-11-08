/-
# Adjoint of operator-valued integrals

The symmetrized Crouzeix--Palencia contour operator contains the adjoint of
an operator-valued integral.  Since adjoint is conjugate-linear, moving it
through integration is not an instance of the usual complex-linear integral
API.  This file supplies that bridge using Mathlib's semilinear integration
theorem and records the resulting contour formula.

## Main declarations

* `ContinuousLinearMap.adjoint_integral` -- adjoint commutes with an
  integrable Bochner integral.
* `ContinuousLinearMap.adjoint_intervalIntegral` -- the corresponding
  interval-integral statement.
* `ContinuousLinearMap.adjoint_contourIntegral` -- the adjoint of a contour
  integral has conjugated tangent weight and pointwise-adjoint integrand.
* `ContinuousLinearMap.intervalIntegral_smul_add_adjoint` -- complex-weighted
  symmetrization of an operator kernel and its adjoint.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ContourIntegral
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval
universe u v w
namespace ContinuousLinearMap
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-- Adjoint commutes with an integrable operator-valued Bochner integral.
The proof uses adjoint as a continuous conjugate-linear map and the fact that
complex conjugation fixes real scalars. -/
theorem adjoint_integral (f : X → E →L[ℂ] F) (hf : Integrable f μ) :
    ContinuousLinearMap.adjoint (∫ x, f x ∂μ) =
      ∫ x, ContinuousLinearMap.adjoint (f x) ∂μ := by
  symm
  exact ContinuousLinearMap.integral_comp_commSL
    RCLike.conj_smul
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap hf
/-- Adjoint commutes with an operator-valued interval integral whenever the
integrand is interval integrable. -/
theorem adjoint_intervalIntegral (f : ℝ → E →L[ℂ] F) {a b : ℝ}
    {ν : Measure ℝ} (hf : IntervalIntegrable f ν a b) :
    ContinuousLinearMap.adjoint (∫ x in a..b, f x ∂ν) =
      ∫ x in a..b, ContinuousLinearMap.adjoint (f x) ∂ν := by
  unfold intervalIntegral
  rw [map_sub, adjoint_integral _ hf.1, adjoint_integral _ hf.2]
end ContinuousLinearMap
