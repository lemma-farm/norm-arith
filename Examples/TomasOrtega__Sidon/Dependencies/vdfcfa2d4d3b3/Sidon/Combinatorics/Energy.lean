module
public import Examples.TomasOrtega__Sidon.Dependencies.vdfcfa2d4d3b3.Sidon.Combinatorics.Differences
public import Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Tactic
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # The additive energy of a Sidon set -/
open scoped BigOperators
namespace IsSidonSet
variable {M : Type*} [AddCommGroup M] {S : Finset M}
variable [DecidableEq M]
end IsSidonSet
