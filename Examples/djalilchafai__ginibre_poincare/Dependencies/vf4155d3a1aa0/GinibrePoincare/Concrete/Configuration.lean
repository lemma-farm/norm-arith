module
public import Mathlib
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Set.Basic
@[expose] public section
/-!
# Configuration space and particle permutations

The configuration space of `n` planar particles is `Fin n → ℂ`.  This file
defines particle relabelling, symmetric and alternating observables, and the
collision locus.  It contains no measure-theoretic or analytic input.
-/
namespace GinibrePoincare
/-- The configuration space of `n` labelled particles in the complex plane. -/
abbrev Configuration (n : ℕ) := Fin n → ℂ
end GinibrePoincare
