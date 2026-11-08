/-
# The Crouzeix--Palencia auxiliary operator (L4.2c)

This file supplies the kernel-checked contour-integral part of the auxiliary
operator construction.  If a smooth Jordan domain `Omega` strictly contains
`closure (numericalRange A)`, every point of its boundary lies in the
resolvent set of `A`.  Consequently, any continuous scalar boundary datum
`h` gives an integrable operator-valued kernel
`z ↦ h z • resolvent A z` and hence the bounded operator

`G = (2 * pi * i)⁻¹ • contourIntegral (h • resolvent A) Omega.boundaryParam`.

The sharp L4.2d/e estimates are intentionally not asserted here: they require
identifying the resulting contour expressions through boundary
Cauchy-transform identities.  Mathlib has no located Plemelj boundary-value
theorem from which those identities follow directly.

## Main declarations

* `SmoothJordanDomain.boundaryParam_mem_resolventSet` -- the boundary of a
  domain containing `closure (numericalRange A)` lies in the resolvent set.
* `exists_smoothJordanDomain_for_numericalRange` -- such a containing smooth
  Jordan domain exists for every bounded operator.
* `crouzeixAuxiliaryIntegrand_contourIntegrable` -- continuity of the scalar
  boundary datum implies integrability of the operator-valued kernel.
* `crouzeixAuxiliaryOperator` -- the normalized contour-integral operator.
* `crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable` -- integrability
  for conjugate polynomial boundary values.
* `crouzeixPolynomialAuxiliaryOperator` -- its specialization to the
  conjugate boundary values of a polynomial.
* `exists_bound_crouzeixPolynomialAuxiliaryIntegrand` -- the polynomial
  resolvent kernel is uniformly bounded along the compact parameter interval.
* `norm_crouzeixAuxiliaryOperator_le` -- its explicit contour-length bound.
* `exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator` --
  the packaged bounded auxiliary-operator construction.
-/
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.ContourIntegral
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.Crouzeix.SmoothApprox
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.NumericalRange.Bounded
import Examples.savarin__lean_operator_theory.Dependencies.v1a342394bc34.Operator.SpectralSet.SpectrumInNR
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace SmoothJordanDomain
private theorem boundaryParam_mem_frontier (Omega : SmoothJordanDomain) (t : ℝ) :
    Omega.boundaryParam t ∈ frontier Omega.carrier := by
  rw [← Omega.boundaryParam_range]
  exact ⟨t, rfl⟩
/-- Every boundary point of a smooth Jordan domain that contains
`closure (numericalRange A)` belongs to the resolvent set of `A`. -/
theorem boundaryParam_mem_resolventSet [CompleteSpace E]
    (Omega : SmoothJordanDomain) (A : E →L[ℂ] E)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) (t : ℝ) :
    Omega.boundaryParam t ∈ resolventSet ℂ A := by
  by_contra hrho
  have hsigma : Omega.boundaryParam t ∈ spectrum ℂ A := hrho
  have hcarrier := hOmega (spectrum_subset_closure_numericalRange A hsigma)
  have hfrontier := boundaryParam_mem_frontier Omega t
  have hempty : Omega.boundaryParam t ∈ (∅ : Set ℂ) := by
    rw [← Omega.isOpen_carrier.inter_frontier_eq]
    exact ⟨hcarrier, hfrontier⟩
  exact hempty
end SmoothJordanDomain
/-- A continuous scalar boundary datum gives a contour-integrable
operator-valued resolvent kernel. -/
theorem crouzeixAuxiliaryIntegrand_contourIntegrable [CompleteSpace E] (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hh : ContinuousOn h (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi))) :
    ContourIntegrable (fun z => h z • resolvent A z) Omega.boundaryParam := by
  apply ContourIntegrable.of_continuousOn
  · exact Omega.boundaryParam_contDiff.continuous.continuousOn
  · exact (Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)).continuousOn
  · refine hh.smul ?_
    rintro z ⟨t, ht, rfl⟩
    exact (spectrum.hasDerivAt_resolvent_const_left
      (Omega.boundaryParam_mem_resolventSet A hOmega t)).continuousAt.continuousWithinAt
/-- The normalized Crouzeix--Palencia auxiliary operator associated to a
scalar boundary datum `h` on a smooth Jordan domain. -/
noncomputable def crouzeixAuxiliaryOperator (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ) : E →L[ℂ] E :=
  (2 * (Real.pi : ℂ) * I)⁻¹ •
    contourIntegral (fun z => h z • resolvent A z) Omega.boundaryParam
/-- The conjugate polynomial boundary datum produces an integrable
operator-valued resolvent kernel.  This is the specialization used in the
Crouzeix--Palencia symmetrized and product estimates. -/
theorem crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ContourIntegrable (fun z => star (Polynomial.eval z p) • resolvent A z)
      Omega.boundaryParam := by
  exact crouzeixAuxiliaryIntegrand_contourIntegrable A Omega
    (fun z => star (Polynomial.eval z p)) hOmega p.continuous.star.continuousOn
noncomputable def crouzeixPolynomialAuxiliaryOperator (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : E →L[ℂ] E :=
  crouzeixAuxiliaryOperator A Omega (fun z => star (Polynomial.eval z p))
