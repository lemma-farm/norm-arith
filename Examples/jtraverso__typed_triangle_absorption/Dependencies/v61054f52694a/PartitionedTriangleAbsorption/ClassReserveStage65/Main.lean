/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ClassReserveStage65.Count
/-! # One sparse class-aware hinge reserve, selected before all roots and residues

Main result: `exists_class_aware_hinge_reserve`. For fixed `γ > 0` and `0 < ρ ≤ 1` there is
`N`, chosen before the vertex type, the four structural classes, the host and the roots, such
that every complete four-class host on `n ≥ N` vertices whose structural fibres have size at
least `γ n` contains **one** edge reserve `X ⊆ E(G)` with maximum degree at most `2 ρ n` such
that, for every labelling `p` constant on the fibres, every triangle family `F` and every two
original `F`-copies `S, S'` of `G` sharing exactly one edge, `X` contains at least
`γ² ρ⁷ n² / 32` distinct six-vertex `F`-hinges for `S, S'` (counted as edge sets).

Proof (one measure, union bound):

1. Sample every coordinate of `Sym2 V` independently with probability `ρ`; the reserve is the
   set of sampled graph edges.
2. Bad events, all for the same outcome `ω`:
   * `n` degree upper tails (`PhysicalStarTail.sampled_star_degree_tail`);
   * for each ordered tuple `(a, b, w, z)` whose roots `{b, w, z}` avoid the class of `a`: the
     number of `x ∈ fibre(a) \ {a}` with `bx, wx, zx` sampled is at most `γ ρ³ n / 4`
     (`marker_lower_tail`; the three-edge blocks are disjoint);
   * for each pair of disjoint vertex sets `A, B` both larger than `γ ρ³ n / 4`: at most
     `ρ |A| |B| / 2` cross pairs are sampled (`cross_lower_tail`). This family is indexed by
     all `(2ⁿ)²` pairs of sets, which handles the random marked sets without conditioning.
3. `failureBudget γ ρ n < 1` for `n ≥ N` (`exists_uniform_threshold`), so one outcome avoids
   every bad event (`PhysicalReserveTails.exists_simultaneous_outcome`).
4. For roots `u v w`, `u v z`, the two marked sets have more than `γ ρ³ n / 4` elements, so more
   than `ρ (γ ρ³ n / 4)² / 2 = γ² ρ⁷ n² / 32` sampled connectors join them; each gives a
   distinct physical hinge inside the reserve (`hinge_count_of_marked`).
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.ClassReserveStage65
open Finset MeasureTheory ProbabilityTheory BernoulliBlocks ClassAwareHingesStage64
  PhysicalHingeSupply SignedHinge
variable {V : Type*} [Fintype V] [DecidableEq V]
universe u
end PartitionedTriangleAbsorption.ClassReserveStage65
