/-
# Double-layer positivity of the resolvent kernel (L4.2d)

The symmetrized Crouzeix--Palencia bound `‖p(A) + G⋆‖ ≤ 2 m` rests on one positivity fact:
along a positively oriented boundary curve `γ` of a convex domain containing `W(A)`, the
operator kernel of `p(A) + G⋆` is `(2π)⁻¹ p(γ t) • (ν R_A(γ t) + (ν R_A(γ t))⋆)` with
`ν = -i γ'(t)` an outward normal, and the symmetric part `ν R_A(σ) + (ν R_A(σ))⋆` is a
*positive* operator.  This file proves that positivity pointwise, in its natural generality:
the only input is that `W(A)` lies in the closed half-plane cut out at `σ` by the direction `ν`.

Route: for `y = R_A(σ) x` one has `x = σ • y - A y`, hence
`⟪x, ν • R_A(σ) x⟫ = ν · conj (σ‖y‖² - ⟪y, A y⟫)`, whose real part is
`‖y‖² · re (conj ν · (σ - a))` with `a = ⟪y, A y⟫ / ‖y‖² ∈ W(A)`.

## Main declarations

* `re_inner_smul_resolvent_nonneg` -- the pointwise positivity at a supporting point.
* `re_inner_add_adjoint_smul_resolvent_nonneg` -- positivity of the
  self-adjoint double-layer kernel.
* `isPositive_add_adjoint_smul_resolvent` -- the corresponding operator-order
  positivity statement.
* `re_inner_smul_resolvent_circleMap_nonneg` -- its instance on a circle enclosing `W(A)`,
  with `ν = -I * deriv (circleMap c R) t`, the kernel direction produced by `contourIntegral`.
* `re_inner_add_adjoint_smul_resolvent_circleMap_nonneg` -- positivity of the
  symmetric circle kernel.
* `isPositive_add_adjoint_smul_resolvent_circleMap` -- the circle kernel in
  positive-operator form.
-/
import Mathlib
import Mathlib.Analysis.InnerProductSpace.Positive
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.NumericalRange.Helpers
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
