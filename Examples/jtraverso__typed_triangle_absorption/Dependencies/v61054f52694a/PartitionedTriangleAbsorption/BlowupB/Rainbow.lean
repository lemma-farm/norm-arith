/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.RepHost
/-! # BlowupB.Rainbow — the unconditional case of rainbow families

A family `F` is **rainbow** when every type consists of three distinct classes (as the family
`F₃` of the four triangles of `K₄`). For rainbow families one representative per class suffices
and the residual on the representatives is trivially physical, so the reduction needs no finite
hypothesis: `physDiv_of_isIntDiv_rainbow` — in any complete `F`-blowup (`F` rainbow, every class
non-empty), integral `F`-divisibility implies physical divisibility.

The file first records the generic shape of steps 1 and 2 for an arbitrary *spoke system*
`S : V → Fin t → (Sym2 V → ℤ)` (`step1_of`, `step2_of`), then instantiates it with the spokes
`ind1 s(x, r k)` of a transversal `r`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
/-! ### Generic spoke systems -/
section Generic
variable (p : V → Fin t) (S : V → Fin t → Sym2 V → ℤ)
variable {p S}
end Generic
/-! ### Rainbow families and transversals -/
/-- Every type of `F` has three distinct classes. -/
def IsRainbow (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ τ ∈ F, Multiset.card τ = 3 ∧ τ.Nodup
theorem IsRainbow.card3 {F : Finset (Multiset (Fin t))} (hR : IsRainbow F) :
    ∀ τ ∈ F, Multiset.card τ = 3 := fun τ hτ => (hR τ hτ).1
variable {p : V → Fin t}
def sp (r : Fin t → V) (x : V) (k : Fin t) : Sym2 V → ℤ := ind1 s(x, r k)
/-! ### Step 1 (rainbow) -/
end PartitionedTriangleAbsorption.BlowupB
