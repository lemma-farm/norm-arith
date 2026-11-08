/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.KeevashPaddedBridge
/-! # BlowupB.KeevashPaddedMain — splitting the weights, and the bridge theorem

* `sum_split_eq`: for one type `τ` and one edge `uv`, the padded load of the split weights
  `y_T / N_T` equals the triangle load `∑_{w} y {u, v, w}`;
* `paddedRegularT_of_triRegular`: `TriRegular` with classes `≥ γ n` gives `PaddedRegularT` with
  `ω' = ω · min (1/27) ((γ/2)^{q−3})` and the same load error;
* **`keevashTypedSpec_of_padded`**: `KeevashPaddedSpec F → KeevashTypedSpec F`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {t : ℕ}
section Split
variable {V : Type*} [Fintype V] [DecidableEq V]
end Split
end PartitionedTriangleAbsorption.BlowupB
