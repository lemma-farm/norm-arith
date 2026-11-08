/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.Uniform
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedApplicationLinks
/-! # BlowupB.Families — the Nash–Williams families F₀–F₃

Instances of `isIntDiv_iff_physDiv_uniform` for the four families of the paper
(`TypedApplicationLinks.F0 … F3`), and the `F₃` instance in the language of the four-class host
of `ClassCertificate` (`G.Adj a b ↔ cls a ≠ cls b`).
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0 F1 F2 F3)
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {E : Finset (Sym2 V)}
end PartitionedTriangleAbsorption.BlowupB
