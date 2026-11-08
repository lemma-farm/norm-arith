module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.H1.Basic
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.LevelSets
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Level-set gradient vanishing in `H¹`

The theorem in this file is a direct `p = 2` facade for the finite-exponent
result.  It concerns the selected concrete weak-gradient representative.
-/
@[expose] public section
namespace PDE
open Filter MeasureTheory
namespace H1Function
variable {d : ℕ} {U : Set (Vec d)}
end H1Function
end PDE
