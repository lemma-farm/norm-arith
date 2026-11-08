module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Measure.NormalizedLp
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Convergence between normalized and unnormalized `L^p` norms

On a positive finite-volume domain, normalized and unnormalized `L^p`
convergence are equivalent. The proofs retain the exact volume factors.
-/
@[expose] public section
open scoped ENNReal Topology
namespace PDE
open Filter MeasureTheory
end PDE
