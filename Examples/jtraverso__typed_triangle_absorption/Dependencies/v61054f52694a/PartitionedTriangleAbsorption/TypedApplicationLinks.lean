/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedLinkCoefficients
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
/-! # The F0--F3 vertex-link dictionaries

Every inventory below lists all types containing the root. The conclusions
give natural coefficients in `typeDegVec`, not simultaneous graph embeddings.
In the fork cases the extra boundary-parity hypothesis cannot be dropped;
adding one permitted pair repairs it at the coefficient level.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedApplicationLinks
open Finset TypedLinkArithmetic TypedLinkCoefficients
def F0 : Finset (Multiset (Fin 2)) := {{0, 0, 1}, {0, 1, 1}}
def F1 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 2}, {0, 0, 3}, {1, 1, 2}, {1, 1, 3},
    {0, 2, 2}, {1, 2, 2}, {0, 3, 3}, {1, 3, 3}}
def F2 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 2}, {0, 0, 3}, {1, 1, 2}, {1, 1, 3}, {0, 2, 3}, {1, 2, 3}}
def F3 : Finset (Multiset (Fin 4)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}
def first1 : Fin 4 → Fin 4 := ![2, 2, 0, 0]
def second1 : Fin 4 → Fin 4 := ![3, 3, 1, 1]
def lower2 : Fin 2 → Fin 4 := ![0, 1]
def upper2 : Fin 2 → Fin 4 := ![2, 3]
def central2 : Fin 2 → Fin 4 := ![3, 2]
end PartitionedTriangleAbsorption.TypedApplicationLinks
