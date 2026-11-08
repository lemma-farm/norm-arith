module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Extensionality of the spatial `H¹₀` value map

The weak-gradient graph has no nontrivial element with zero value component:
weak derivatives are unique almost everywhere on an open domain.  This gives
injectivity of the value map on the closed spatial `H¹₀` carrier.
-/
@[expose] public section
open Filter
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
end HypoellipticAleksandrov.Parabolic.Dirichlet
