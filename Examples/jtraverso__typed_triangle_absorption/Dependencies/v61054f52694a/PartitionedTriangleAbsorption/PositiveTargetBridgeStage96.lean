/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TargetTripleSelectionStage95
/-! # Bridging the padded integer coefficients to target token slots

Stage90 retains integer coefficients max(c,0). Stage95 indexes slots by
natural multiplicities. This bridge discharges that conversion rather than
requiring a second representation as a new hypothesis.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PositiveTargetBridgeStage96
open Finset ColouredHub TargetTripleSelectionStage95 CatalystInsertionStage89
variable {t : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
end PartitionedTriangleAbsorption.PositiveTargetBridgeStage96
