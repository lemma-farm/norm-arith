/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedComponents.WitnessFrame
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedComponents.MonoObstruction
@[expose] public section
/-!
# The 39 disconnected `ℤ/3` families with an isolated monochromatic class

Census rows `Y | N | 2 | N | Z/3` with a class `m` whose only type is `{m,m,m}` (`m = 3` with
component labels `cM3 = (0,0,0,3)`, or `m = 0` with `cM0 = (0,1,1,1)`). Definitions and finite facts
(all by `decide`). `FMxx` is the `xx`-th such row of `CENSUS_ALL_765_20261013.md`.
-/
namespace PaddedComponents
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedNoCommon
/-- Component labels when class `3` is the isolated class. -/
def cM3 : Fin 4 → Fin 4 := ![0, 0, 0, 3]
noncomputable def FM01 : Finset (Multiset (Fin 4)) := {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {3, 3, 3}}
end PaddedComponents
