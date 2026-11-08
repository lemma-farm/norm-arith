module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.H1.LevelSets
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Level-set locality for the Hilbert realization of spatial `H¹₀`

This module proves the geometry-free Stampacchia property for the selected
value and gradient representatives of `H10HilbertGraph`.  The argument is
local: on every ball compactly contained in the open domain, the graph point
defines an `H¹` representative, to which the existing bounded-convex theorem
applies.  A countable subcover then recovers the original open domain.

No boundedness, convexity, or boundary regularity is assumed of the original
domain, and the proof does not use the zero-boundary closure property.
-/
@[expose] public section
open Filter MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
end HypoellipticAleksandrov.Parabolic.Dirichlet
