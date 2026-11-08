module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6423f25b1c34.HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v6423f25b1c34.HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Density
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The spatial Gelfand triple

This module realizes the dual side of the spatial Gelfand triple
`H¹₀(Ω) → L²(Ω) → (H¹₀(Ω))^*`.  It uses the continuous, injective spatial
value map and its dense-range theorem, together with the real Hilbert-space pairing.

No coercivity, time-dependent, Bochner, or PDE assertion is made here.
-/
@[expose] public section
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
/-- The `H⁻¹` carrier dual to the spatial Hilbert realization of `H¹₀(Ω)`. -/
abbrev H10HilbertGraphDual (hΩ : IsOpen Ω) : Type _ :=
  StrongDual ℝ (H10HilbertGraph hΩ)
end HypoellipticAleksandrov.Parabolic.Dirichlet
