module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v0f0af030ce8c.PDEFoundation.Ambient.Basic
public import Mathlib.Data.Set.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Affine set operations on native vectors

Pure set-theoretic translation identities. Measure-preserving and integral
transport statements belong in the later measure layer.
-/
@[expose] public section
namespace PDE
/-- Translate a set of native vectors by `z`. -/
def translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) : Set (Vec d) :=
  {x | ∃ y ∈ U, x = y + z}
end PDE
