module
public import Mathlib
/-! Shared cyclotomic definitions used in the Catalan proof.
The explicit `p` parameter in `G` and `R` is retained in their signatures. -/
/-!
# `Catalan.Cyclotomic.Basic`

Part of the Catalan formalization.
-/
@[expose] public section
open scoped BigOperators nonZeroDivisors Pointwise
open NumberField
noncomputable section
namespace Catalan
/-- Interface: the Galois group of K/Q; p is an explicit phantom parameter. -/
abbrev G (p : ℕ) (K : Type*) [Field K] [NumberField K] := K ≃ₐ[ℚ] K
section CyclotomicPrelude
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [hcycl : IsCyclotomicExtension {p} ℚ K]
end CyclotomicPrelude
end Catalan
