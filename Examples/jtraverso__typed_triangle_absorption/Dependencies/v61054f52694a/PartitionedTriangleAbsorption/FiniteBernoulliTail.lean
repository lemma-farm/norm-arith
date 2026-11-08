/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BernoulliBlocks
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.FieldSimp
/-! # A lower-tail bound for a genuine independent Bernoulli event family

This packages Mathlib's Hoeffding lemma and independent sub-Gaussian sum bound.
The event probabilities are actual measure values. Applying this to all typed
queries of the physical reserve, then selecting one simultaneous outcome,
remains a separate assembly obligation.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.FiniteBernoulliTail
open Finset MeasureTheory ProbabilityTheory
end PartitionedTriangleAbsorption.FiniteBernoulliTail
