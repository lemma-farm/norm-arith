-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.v22d23b3f3b2b.CKN.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The weighted-gradient candidate for a divergence inverse on a ball

The field `(R² - |x - x₀|²) ∇v` vanishes on the sphere and its divergence is
the negative weighted elliptic operator
`-(R² - |x - x₀|²) Δv + 2 (x - x₀) · ∇v`. These identities are proved for
actual smooth functions, including the exact antisymmetric-gradient formula.

A bounded right inverse for all mean-zero `L²` data would additionally require
solving the weighted equation and proving a uniform gradient estimate. Those
quantitative conclusions are not assumed or asserted here.
-/
@[expose] public section
open CKN
open CKN.Foundation.Parabolic
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace FluidSingularSets
/-- The quadratic weight that vanishes on a Euclidean sphere. -/
def ballBoundaryWeight (x₀ : Vec3) (R : ℝ) (x : Vec3) : ℝ :=
  R ^ 2 - ∑ i : Fin 3, (x i - x₀ i) ^ 2
/-- The ball weight is genuinely smooth. -/
theorem ballBoundaryWeight_contDiff (x₀ : Vec3) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (ballBoundaryWeight x₀ R) := by
  unfold ballBoundaryWeight
  fun_prop
end FluidSingularSets
