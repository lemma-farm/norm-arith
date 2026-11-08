/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedHinge.Core
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedHinge.SlotSelect
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedCertificate.Packing
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
/-! # Stage 53: the bounded signed physical absorber under explicit physical hinge supply

`absorber_of_budget` is the construction for a fixed host, under the two explicit size
conditions `M < α n` and `2^C(C0+1,2) M < β n` with `M = 9K + 4K C0 + 1`.
`signed_hinge_absorber` packages it with uniform constants `C, N` chosen from
`α, β, C0, K` only (before the host, the edge set and the certificate).

The construction:
1. every certificate term `c_j t_j` gives `|c_j|` occurrences; each occurrence of
   `t = {a,b,c}` gets a fresh apex `x` and a supplied hinge `H` for `{a,b,c}, {a,b,x}`
   (vertex-fresh outside its roots); `hinge_gadget` turns it into three slot wedges and a
   decomposable local closure `Y` (`exists_occurrence_hinges`, `hinge_gadget`);
2. the certificate identity gives an edge-preserving bijection
   `positive slots ≃ P ⊕ negative slots` (`exists_slot_matching`);
3. every negative slot gets a supplied slot hinge to its matched positive slot
   (`exists_slot_hinges`);
4. `core_absorber` (via `two_mode_assembly`) gives `A = X` with `X` and `X ∪ P` decomposable;
5. `Q` is a vertex-disjoint fresh F0 packing with the same physical `00/11/01` counts as `P`
   (`exists_fresh_destination`), so `A ∪ Q` is decomposable.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.SignedHinge
open Finset SignedCertificate TypedApplicationLinks
end PartitionedTriangleAbsorption.SignedHinge
namespace PartitionedTriangleAbsorption.SignedHinge
open Finset SignedCertificate TypedApplicationLinks
end PartitionedTriangleAbsorption.SignedHinge
