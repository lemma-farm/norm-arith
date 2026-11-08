module
public import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
open Set Cardinal
/-- A Sidon set is a set of elements in any additive commutative monoid
    where all pairwise sums are distinct. -/
def IsSidonSet {M : Type*} [AddCommMonoid M] (s : Set M) : Prop :=
  ∀ a b c d, a ∈ s → b ∈ s → c ∈ s → d ∈ s →
  a + b = c + d → ({a, b} : Set M) = ({c, d} : Set M)
