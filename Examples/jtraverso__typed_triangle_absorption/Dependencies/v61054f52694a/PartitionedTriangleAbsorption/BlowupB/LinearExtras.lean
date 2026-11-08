/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.LinearAbsorber
/-! # BlowupB.LinearExtras — linear families are exactly where `ThreeStepLinks` fails

* `not_threeStepLinks_of_linear`: no nonempty linear family satisfies `ThreeStepLinks` (the
  link of a class is a matching, so no walk of length `3` returns from `y` to `y`). Hence the
  linear-family absorbers of `LinearAbsorber` cover a class of families disjoint from the one
  covered by the tree's transformer chain.
* Examples: the rainbow type `R3` and the Fano plane `fano` (seven classes, seven types) are
  linear.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset TypedTransformer
variable {t : ℕ}
end PartitionedTriangleAbsorption.BlowupB
