/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Lattice
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalParity
@[expose] public section
/-!
# The family Fbit (= G9) and its one-bit lattice

`Fbit = {000, 001, 002, 011, 022, 113, 133, 223, 233}`. Allowed pairs: 00, 01, 02, 11, 13, 22, 23,
33 (forbidden 03 and 12). It has `ThreeStepLinks` and common neighbour classes. The local census
found `Λ_ord / L_Fbit = ℤ/2`, and the same for the four other bit-only families of the census
(`Fbit ∪ {333}`, `Fbit ∪ {111}`, `Fbit ∪ {111, 222}`, `Fbit ∪ {111, 222, 333}`), all with the same
allowed pairs. Every type has even cross counts, so the bit is simply

  `fbitBit E = x01 mod 2`

(the class parities force `x01 ≡ x02 ≡ x13 ≡ x23 (mod 2)`); no division by two is needed. The
6-cycle `0,0,1,3,2,0` has bit 1.

Lean content:
* `isIntDiv_Fbit_iff_good_bit`: on loopless sets, `IsIntDiv p Fbit E ↔ FbitGood p E ∧ bit = 0`;
* `fbitParity`: the parity evaluation;
* `fbit_bounded_coefficients`: an integral witness with negative mass `≤ 8 K` (free parameter of
  the one-dimensional kernel set to `a001 = 0`).
-/
namespace PaddedFbit
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PaddedF12
/-- The family Fbit (G9 of the census). -/
noncomputable def Fbit : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 1}, {0, 2, 2}, {1, 1, 3}, {1, 3, 3}, {2, 2, 3},
    {2, 3, 3}}
section Eval
variable (a b c d e f g h k : ℤ)
end Eval
variable {V : Type*} [DecidableEq V]
end PaddedFbit
