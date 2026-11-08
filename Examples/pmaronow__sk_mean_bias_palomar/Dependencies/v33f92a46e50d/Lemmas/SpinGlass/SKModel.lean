module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v33f92a46e50d.Lemmas.SpinGlass.Defs
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v33f92a46e50d.Lemmas.SpinGlass.Gaussian_IBP_Hilbert
public import Mathlib
set_option autoImplicit true
set_option linter.deprecated false
@[expose] public section
open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open PhysLean.Probability.GaussianIBP
namespace SpinGlass
universe u
/-!
# The Sherrington–Kirkpatrick (SK) model: disorder structures (finite `N`)

This file defines the *random* Hamiltonians used in the SK model and in the simple
reference model used for Guerra's interpolation, in a way compatible with the
Hilbert–space Gaussian IBP machinery.

We keep the disorder abstract: a disorder is a centered Gaussian random vector in
`EnergySpace N` together with a specification of its covariance kernel on the
canonical basis `std_basis`.

## References
* M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I.
* D. Panchenko, *The Sherrington–Kirkpatrick Model*.
-/
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (N : ℕ)
/-! ### Deterministic thermodynamic quantities (aliases) -/
structure SKDisorder (β h : ℝ) where
  /-- The (random) Hamiltonian. -/
  U : Ω → EnergySpace N
  /-- Centered Gaussian structure in the Hilbert space `EnergySpace N`. -/
  hU : IsGaussianHilbert.{u, 0, 0} U
  /-- Covariance on the canonical basis. -/
  cov_eq : ∀ σ τ, inner ℝ ((covOp (g := U) hU)
    (std_basis N σ)) (std_basis N τ) =  sk_cov_kernel N β σ τ
/--
Simple (reference) disorder: a centered Gaussian Hamiltonian with covariance kernel
`simple_cov_kernel`.

This matches the “magnetic field” comparison model used in Guerra's bound.
-/
structure SimpleDisorder (β q : ℝ) where
  /-- The (random) Hamiltonian. -/
  V : Ω → EnergySpace N
  /-- Centered Gaussian structure in the Hilbert space `EnergySpace N`. -/
  hV : IsGaussianHilbert.{u, 0, 0} V
  /-- Covariance on the canonical basis. -/
  cov_eq : ∀ σ τ, inner ℝ ((covOp (g := V) hV) (std_basis N σ))
    (std_basis N τ) = simple_cov_kernel N β (fun x => q * x) σ τ
end SpinGlass
