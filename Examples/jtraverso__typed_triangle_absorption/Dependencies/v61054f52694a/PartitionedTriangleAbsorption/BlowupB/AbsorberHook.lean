/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.NearlyCompleteAbsorber
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.UniformBoundedCoreStage104
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.DivisiblePrivateAbsorberStage101
/-! # BlowupB.AbsorberHook — absorbers for every family in nearly complete blowups

The bounded-source absorbers of the tree for an arbitrary family (`ThreeStepLinks F`):
* `BoundedCoreStage104.exists_uniform_terminal_absorber` (terminal core),
* `PrivateAbsorberStage101.private_absorber_from_divisible` (private absorbers),
take the four-root supply `CompatibleSupply` as a hypothesis. The tree derives that supply from
the missing degree only for `F₃` (`AbsorberBootstrapStage138.compatible_supply_of_missing`).

Here (`compatibleSupply_of_missing`) it is derived for **every** family from the missing degree
and the class sizes, through `NearlyCompleteAbsorber.card_query_ge`. Consequently both
absorbers hold in every nearly complete blowup of every family with `ThreeStepLinks`
(`terminal_absorber_nearly`, `private_absorber_nearly`), in particular for `F₀, F₁, F₂, F₃`.

`ThreeStepLinks` is a genuine restriction: it fails for the single rainbow type `{0,1,2}`
(`not_threeStepLinks_rainbow`), although `BlowupB.Uniform` covers that family.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset TypedTransformer PairMoveSelectionStage85 TypedEmbeddingSelection
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
end PartitionedTriangleAbsorption.BlowupB
