/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.CoherentTransformer.StarObstruction
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedApplicationLinks
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
/-! # A six-class host whose root has a bipartite F0-link

Vertices are `Fin 6 × Fin L`. Classes `0 = A`, `1 = X`, `2 = Y` form part `0`,
classes `3 = P`, `4 = Q`, `5 = Z` form part `1`. The classes `X`, `Y`, `Z`
are cliques and `A`, `P`, `Q` are independent. The class adjacencies are

  `A : X Y P Q`, `X : A X Y Q Z`, `Y : A X Y P Z`,
  `P : A Y Q Z`, `Q : A X P Z`, `Z : X Y P Q Z`.

Every vertex `v` of `A` has a bipartite F0-link with sides `P ∪ X`
and `Q ∪ Y`. Hence the star charge `χ_v` (`+1` towards `P ∪ X`, `-1`
towards `Q ∪ Y`) annihilates every F0 triangle of the host.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.CoherentTransformer.BipartiteLinkHost
open Finset TypedApplicationLinks
/-- Class-to-part map. -/
def part : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]
/-- Class adjacency (diagonal entries `true` mean the class is a clique). -/
def R : Fin 6 → Fin 6 → Bool :=
  ![![false, true, true, true, true, false],
    ![true, true, true, false, true, true],
    ![true, true, true, true, false, true],
    ![true, false, true, false, true, true],
    ![true, true, false, true, false, true],
    ![false, true, true, true, true, true]]
theorem R_symm : ∀ a b : Fin 6, R a b = R b a := by decide
variable (L : ℕ)
/-- The host graph on `Fin 6 × Fin L`. -/
def host : SimpleGraph (Fin 6 × Fin L) where
  Adj a b := a ≠ b ∧ R a.1 b.1 = true
  symm := ⟨fun a b h => ⟨Ne.symm h.1, by rw [R_symm]; exact h.2⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩
instance : DecidableRel (host L).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ R a.1 b.1 = true))
/-- The partition `p`. -/
def hp : Fin 6 × Fin L → Fin 2 := fun v => part v.1
end PartitionedTriangleAbsorption.CoherentTransformer.BipartiteLinkHost
