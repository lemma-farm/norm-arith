module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.H1.Basic
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.Graph
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The canonical complete `H¹` carrier

The complete quotient-level carrier for `H¹(U)` is not a second graph
construction. It is the `p = 2` specialization of `W1pGraph`, whose value and
gradient components are `L²` equivalence classes satisfying the closed weak
gradient constraints.

`H1Function U` remains the field-name-compatible concrete-representative
interface. A representative-to-graph map belongs to the generic `W^{1,p}`
bridge and is intentionally not duplicated here.
-/
@[expose] public section
open scoped ENNReal
namespace PDE
/-- The canonical complete quotient-level `H¹(U)` carrier. Completeness and
the normed linear structure are inherited definitionally from `W1pGraph U 2`.
-/
abbrev H1Graph {d : ℕ} (U : Set (Vec d)) :=
  W1pGraph U (2 : ℝ≥0∞)
namespace H1Graph
end H1Graph
end PDE
