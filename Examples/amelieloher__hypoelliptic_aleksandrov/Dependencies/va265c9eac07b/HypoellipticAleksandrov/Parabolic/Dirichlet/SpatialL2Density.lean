module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.va265c9eac07b.HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev
public import Mathlib
public import Mathlib.Geometry.Manifold.SmoothApprox
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Interior-supported smooth tests are dense in spatial `L²`

On every open native-vector domain, actual bundled smooth compactly supported
test functions are dense for the restricted-volume `L²` norm.  The proof first
uses global smooth compact approximation, localizes by a compact core and a
Urysohn cutoff, and smooths once more without enlarging topological support.
-/
@[expose] public section
open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace Topology
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
end HypoellipticAleksandrov.Parabolic.Dirichlet
