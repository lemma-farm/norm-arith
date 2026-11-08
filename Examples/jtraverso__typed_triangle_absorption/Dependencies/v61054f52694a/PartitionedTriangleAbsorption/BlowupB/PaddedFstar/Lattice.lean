/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalCharge
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedBoundedCoefficients
@[expose] public section
/-!
# The family F* and its trivial lattice

`Fstar = {000, 001, 002, 012, 123, 133, 233, 333}` on four classes. Its allowed pairs are
00, 01, 02, 12, 13, 23 and 33; the pairs 03, 11 and 22 are forbidden. The local census
(`cegis/b0_refiner/Fstar_20261012/`) found it as the unique family, up to S₄, whose integral
lattice is trivial (`IsIntDiv` = ordinary divisibility on allowed support) and which also has
`ThreeStepLinks` and common neighbour classes. The edge-lattice identity `L_F* = Λ_ord` is
certified by certo (Smith 1,1,1,1,2,2,6 on both sides) and jacobian (equal Hermite forms).

Lean content:
* `isIntDiv_Fstar_iff`: on loopless sets, `IsIntDiv p Fstar E ↔ ActiveEdges ∧ Even3 E`;
* `fstar_bounded_coefficients`: an integral witness with negative mass `≤ 2 |E| + 14`. The
  explicit witness (parameter `s ∈ [0, 6)` chosen by CRT) was first checked by certo/z3.
-/
namespace PaddedFstar
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PaddedF12
variable {V : Type*} [DecidableEq V]
end PaddedFstar
