/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFstar.Lattice
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedF3.Universal
@[expose] public section
/-!
# A universal F* absorber from the ORDINARY refiner

F* has a trivial lattice (`isIntDiv_Fstar_iff`). Hence the ordinary universal refiner
(`exists_universal_refiner_alpha`, pieces even with `3 ∣ |P|`, at most 42 edges) already refines
F*-divisible leftovers into F*-divisible pieces. No charge or torsion layer is needed. Terminal
absorbers for the 42-edge pieces use the explicit witness bound `8·42 + 40 = 376`: order 40996 and
size 123978, both below `2^21`.
-/
namespace PaddedFstar
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open PaddedF12
universe u
end PaddedFstar
