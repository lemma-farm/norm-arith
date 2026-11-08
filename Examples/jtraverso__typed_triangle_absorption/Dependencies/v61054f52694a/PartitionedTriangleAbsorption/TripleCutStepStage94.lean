/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TripleCutInvariantStage94
/-! # Cutting one prescribed triple of original tokens

`cut_triple` is the producer for one triple. Three distinct remaining
original tokens `e₁, e₂, e₃` with endpoint-label types `(i,j)`, `(j,k)`,
`(k,i)` and `{i,j,k} ∈ F` are given. Their six current endpoints are carriers
(boundary invariant), hence pairwise distinct and distinct from their six
catalytic endpoints; these are the twelve distinct roots of
`three_exchanges`. The result:

* an actual allowed triangle `z_A z_B z_C` formed by `e₁, e₂, e₃`, with its
  decomposition, isolated as a component (`TriangleCut`);
* the boundary invariant for the remaining tokens `R \ {e₁, e₂, e₃}`;
* all other original tokens and all `(y, 2)` catalytic tokens unchanged;
* a physical trace of exactly nine moves, ledger growth at most `81`,
  active-set growth at most `6`, and a continuation from the final ledger.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TripleCutStage94
open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89 PhysicalMovesStage86
variable {V : Type*} [DecidableEq V] {t : ℕ}
/-- The finished triangle of one cut: the three original tokens form the
actual allowed triangle `z_A z_B z_C`, and no other token touches it. -/
structure TriangleCut (p : V → Fin t) (F : Finset (Multiset (Fin t))) (S : Data V)
    (pos : Tok V → Sym2 V) (e₁ e₂ e₃ : Sym2 V) (i j k : Fin t) (zA zB zC : V) : Prop where
  ne : zA ≠ zB ∧ zA ≠ zC ∧ zB ≠ zC
  label : p zA = i ∧ p zB = j ∧ p zC = k
  pos₁ : pos (.inl e₁) = s(zA, zB)
  pos₂ : pos (.inl e₂) = s(zB, zC)
  pos₃ : pos (.inl e₃) = s(zC, zA)
  decomp : HasDecomp p F {s(zA, zB), s(zB, zC), s(zC, zA)}
  atA : tokAtP S pos zA = {.inl e₃, .inl e₁}
  atB : tokAtP S pos zB = {.inl e₁, .inl e₂}
  atC : tokAtP S pos zC = {.inl e₂, .inl e₃}
variable [Fintype V]
end PartitionedTriangleAbsorption.TripleCutStage94
