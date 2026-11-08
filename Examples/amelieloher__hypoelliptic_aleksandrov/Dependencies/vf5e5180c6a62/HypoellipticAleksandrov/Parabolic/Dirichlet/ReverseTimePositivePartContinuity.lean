module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePart
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Continuity of the reverse-time positive part

This module proves strong continuity of the pointwise spatial positive-part
operation on the reverse-time Bochner `L²` space.
-/
@[expose] public section
open Filter MeasureTheory Set
open scoped ENNReal Topology
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
variable {d : ℕ} {Ω : Set (PDE.Vec d)}
end HypoellipticAleksandrov.Parabolic.Dirichlet
