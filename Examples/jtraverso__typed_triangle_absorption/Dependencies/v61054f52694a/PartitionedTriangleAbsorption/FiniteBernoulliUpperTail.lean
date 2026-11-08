/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.FiniteBernoulliTail
/-! # Upper deviations of actual independent Bernoulli events

This is the upper-tail counterpart of the accepted Stage-12 lower tail.
No independence between different graph-star or common-neighbour queries is
required; independence is needed only within each individual query.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.FiniteBernoulliUpperTail
open Finset MeasureTheory ProbabilityTheory
end PartitionedTriangleAbsorption.FiniteBernoulliUpperTail
