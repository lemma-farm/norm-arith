/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ClassCertificate.Extraction
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.IntegerCertificate.Assembly
/-! # Structural-lattice physical certificates in the complete four-class host

Let `cls : V → Fin 4` with representatives `r i` (`cls (r i) = i`), and let `G` be the
complete four-class graph, `G.Adj u v ↔ cls u ≠ cls v`. For every `P ⊆ E(G)` with the
**structural** divisibility `IsIntDiv cls F3 P`, the indicator of `P` is an integer
combination of actual triangles of `G` with total absolute coefficient at most `12 |P|`,
equal at every `Sym2` coordinate. Every triangle has three distinct classes, so it is an F3
copy for `cls` and an F0 copy for the coarse labels `classPart ∘ cls`.

The proof follows the three physical stages of the Stage65 note:

1. `realizes_rectE`: per source edge `uv`, the rectangle
   `[uv] - [u r_j] - [r_i v] + [r_i r_j]` costs `4` (four triangles through `r_k`).
2. `realizes_starE`: per vertex `v` of class `i`, the star `Σ_j d_j ([v r_j] - [r_i r_j])`
   costs at most `3 Σ_j d_j`, using the even degree from `IsIntDiv` and the star system of
   `ClassLatticeStage65`; the source signed degrees `d_j = degVec cls P v j` are used.
3. `realizes_residual`: the remaining representative edges carry the six class-pair counts;
   the F3 edge equation and `tetrahedron_budget` give cost at most `2 |P|`.

`ind_decomposition` is the exact identity `ind P = Σ rect + Σ star + residual`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.ClassCertificate
open Finset TypedApplicationLinks SignedCertificate IntegerCertificate
open LocalCycleTransportStage62 ParityBalanceStage63 ClassLatticeStage65
open MultipartiteBoundaryStage64
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
def third (i j : Fin 4) : Fin 4 :=
  if 0 ≠ i ∧ 0 ≠ j then 0 else if 1 ≠ i ∧ 1 ≠ j then 1 else 2
theorem distinct_mem_F3 : ∀ x y z : Fin 4, x ≠ y → x ≠ z → y ≠ z →
    ({x, y, z} : Multiset (Fin 4)) ∈ F3 := by decide
section Host
variable {cls : V → Fin 4} {G : SimpleGraph V}
end Host
end PartitionedTriangleAbsorption.ClassCertificate
