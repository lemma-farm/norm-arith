module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.Mean
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.Truncation
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Vanishing of weak gradients on individual level sets

For a representative-level finite-exponent `W^{1,p}` function on a bounded
open convex domain, this module proves that its selected weak gradient
vanishes almost everywhere on each individual level set.  The proof compares
the two one-sided positive-part truncations of `u` and `-u`; it does not use a
general Lipschitz Sobolev chain rule.

The result concerns one fixed level only.  The stronger null-preimage theorem
needed for an arbitrary Lipschitz scalar composition remains a separate
later result.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
open Filter MeasureTheory
namespace W1pFunction
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
end W1pFunction
end PDE
