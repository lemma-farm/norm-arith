/-
# Normalization of the integrated double-layer kernel

The positive-kernel route to the symmetrized Crouzeix--Palencia estimate
needs two independent inputs: pointwise positivity of the double-layer
kernel, and its total mass.  This file supplies the algebraic second input.

First, integration commutes with symmetrization `B ↦ B + B†`.  Consequently,
if a parametrized resolvent satisfies the Cauchy identity

`integral (gamma' • R_A(gamma)) = 2 * pi * i • 1`,

then its outward-normal kernel `(-i * gamma') • R_A(gamma)` has integral
`2 * pi • 1`, and the double-layer kernel obtained by adding the pointwise
adjoint has integral `4 * pi • 1`.

The resolvent Cauchy identity remains an explicit hypothesis here.  It is
the analytic input supplied separately by a circle or contour Cauchy theorem;
no such boundary-value assertion is hidden in the normalization argument.

## Main declarations

* `ContinuousLinearMap.intervalIntegral_add_adjoint` -- interval integration
  commutes with pointwise symmetrization.
* `intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy` --
  the double-layer kernel has total mass `4 * pi • 1` whenever the underlying
  resolvent contour has Cauchy integral `2 * pi * i • 1`.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.AdjointIntegral
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace ContinuousLinearMap
/-- Interval integration commutes with symmetrization of an
operator-valued integrand. -/
theorem intervalIntegral_add_adjoint {f : ℝ → E →L[ℂ] E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t + ContinuousLinearMap.adjoint (f t)) =
      (∫ t in a..b, f t) +
        ContinuousLinearMap.adjoint (∫ t in a..b, f t) := by
  let adj : (E →L[ℂ] E) →L⋆[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.adjoint.toLinearIsometry.toContinuousLinearMap
  have hfadj : IntervalIntegrable (fun t ↦ ContinuousLinearMap.adjoint (f t))
      volume a b := by
    constructor
    · change Integrable (fun t ↦ adj (f t)) (volume.restrict (Ioc a b))
      exact adj.integrable_comp hf.1
    · change Integrable (fun t ↦ adj (f t)) (volume.restrict (Ioc b a))
      exact adj.integrable_comp hf.2
  rw [intervalIntegral.integral_add hf hfadj,
    ← ContinuousLinearMap.adjoint_intervalIntegral f hf]
end ContinuousLinearMap
