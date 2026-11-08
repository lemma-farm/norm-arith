module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.Mean
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.Algebra
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Means of representative-level `W^{1,p}` functions

This is the compatibility layer needed by mean-zero Poincaré estimates.  The
arithmetic mean is the scalar definition from `PDEFoundation.Sobolev.Mean`;
subtracting it changes only the value representative and leaves the chosen
weak gradient exactly unchanged.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
open MeasureTheory
namespace W1pFunction
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
end W1pFunction
end PDE
