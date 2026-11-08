/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SparseReserveGeometry
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Bernoulli
/-! # Grouping actual independent physical-edge trials

A block is retained when every edge in it is retained. Pairwise disjoint
blocks inherit mutual event independence, not merely pairwise independence.
This supplies the probabilistic independence prerequisite for L2; the
concentration and simultaneous reserve-existence theorem are separate.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BernoulliBlocks
open Finset MeasureTheory ProbabilityTheory
variable {E I Ω : Type*} [MeasurableSpace Ω]
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
end PartitionedTriangleAbsorption.BernoulliBlocks
