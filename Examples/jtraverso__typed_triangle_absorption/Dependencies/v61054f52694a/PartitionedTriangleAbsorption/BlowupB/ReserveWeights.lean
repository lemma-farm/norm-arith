/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.KeevashReserve
/-! # BlowupB.ReserveWeights — densities and type weights with exact unit loads

Class sizes `nc : Fin t → ℝ`, total `n`, scale `θ`. For a pair of classes `s = {a, b}`
(a 2-multiset) the density is

`ρ s = θ · (∑_{c : c ::ₘ s ∈ F} (nc c - count c s)) / n`,

the weight of a type is `wt τ = θ / ∏_{pairs σ of τ} ρ σ` (pairs = `τ.powersetCard 2`), and the
expected number of `τ`-thirds through an `ab` pair, divided by `n`, is

`κ τ a b = ∑_{c : c ::ₘ {a,b} = τ} ρ {a,c} ρ {b,c} (nc c - count c {a,b}) / n`.

**`load_identity`**: `∑_{τ ∈ F} wt τ · κ τ a b = 1` for every allowed pair, exactly.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {t : ℕ}
end PartitionedTriangleAbsorption.BlowupB
