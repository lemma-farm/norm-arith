/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedTransformerLabels
/-! # A constructed abstract typed transformer

The auxiliary vertices are fresh by construction. No existence of a typed
labelling is assumed. Embedding the resulting object into a prescribed host
and producing compatible trail data remain separate obligations.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedTransformer
open Finset PrivateTemplate AntiEdgeSelection
variable {W : Type*} [DecidableEq W] {I : Type*} [Fintype I] [DecidableEq I]
variable {t : ℕ}
end PartitionedTriangleAbsorption.TypedTransformer
