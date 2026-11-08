-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
/-!
# Actual finite mixtures and degree-window curvature

A mixture is a finitely supported, nonzero, nonnegative coefficient sequence,
with coefficients below degree two equal to zero. Its covariance is an actual
finite polynomial. The tilted degree weights below form an actual probability
mass function, and all moment and curvature identities are derived from that
polynomial.
-/
namespace SlowEquilibration
/-- A canonical finite spin covariance, allowing either parity and zero
coefficients, with no constant or linear term. -/
structure FiniteMixture where
  coeff : ℕ →₀ ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  zero_below_two : ∀ p, p < 2 → coeff p = 0
  nonzero : coeff ≠ 0
namespace FiniteMixture
variable (μ : FiniteMixture)
noncomputable def xi (r : ℝ) : ℝ := ∑ p ∈ μ.coeff.support, μ.coeff p * r ^ p
end FiniteMixture
end SlowEquilibration
