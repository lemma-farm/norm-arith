/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TripleCutStepStage94
/-! # Cutting all triples of a given disjoint family

A `TargetTriple` is combinatorial data only: three original tokens together
with corner labels `i, j, k` such that the tokens have endpoint-label types
`(i,j)`, `(j,k)`, `(k,i)` and `{i,j,k} ∈ F`. It is not a physical
decomposition of anything. Given a list of valid target triples whose token
sets are pairwise disjoint and contained in the remaining tokens, `cut_all`
cuts them one after another with `cut_triple`.

Budget: `|Z| + 4 (d + |U|) + 330 r < a` for `r` triples. Each cut adds at
most `6` active vertices and `81` ledger edges, and needs
`234 + |Z| + 4 (d + |U|) < a`; `330 = 6 + 4 · 81`. The result is a trace of
exactly `9 r` moves with ledger growth at most `81 r`, every triple an
isolated allowed triangle in the final configuration, the boundary invariant
for the rest, and a continuation from the final ledger.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TripleCutStage94
open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89 PhysicalMovesStage86
variable {V : Type*} [DecidableEq V] {t : ℕ}
/-- A prescribed target triple: three original tokens and their corner labels. -/
structure TargetTriple (V : Type*) (t : ℕ) where
  e₁ : Sym2 V
  e₂ : Sym2 V
  e₃ : Sym2 V
  i : Fin t
  j : Fin t
  k : Fin t
/-- The three tokens of a target triple. -/
def TargetTriple.toks (T : TargetTriple V t) : Finset (Sym2 V) := {T.e₁, T.e₂, T.e₃}
/-- Label validity of a target triple (purely combinatorial). -/
structure TargetTriple.Valid (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (T : TargetTriple V t) : Prop where
  ne₁₂ : T.e₁ ≠ T.e₂
  ne₁₃ : T.e₁ ≠ T.e₃
  ne₂₃ : T.e₂ ≠ T.e₃
  ty₁ : Sym2.map p T.e₁ = s(T.i, T.j)
  ty₂ : Sym2.map p T.e₂ = s(T.j, T.k)
  ty₃ : Sym2.map p T.e₃ = s(T.k, T.i)
  link : Link F T.i T.j T.k
variable [Fintype V]
end PartitionedTriangleAbsorption.TripleCutStage94
