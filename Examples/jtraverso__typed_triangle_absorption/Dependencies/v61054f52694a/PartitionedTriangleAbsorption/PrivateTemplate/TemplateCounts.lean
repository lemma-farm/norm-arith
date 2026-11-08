/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PrivateTemplate.TemplateDecomp
/-!
# Exact counts for the template

* `|A| = 105 m`;
* `|U| = 34 m + 1` auxiliaries (for `m > 0`);
* `deg_A (root r) = 8 · #{j | xr j = r} = 4 · deg_P (root r)`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PrivateTemplate
open Finset OnePart AntiEdgeSelection
variable {Rt : Type*} [DecidableEq Rt] {m : ℕ}
variable {σt : Equiv.Perm (Fin m)} {xr : Fin m → Rt} (h3 : 3 ∣ m)
/-! ### Piece cardinalities -/
end PartitionedTriangleAbsorption.PrivateTemplate
