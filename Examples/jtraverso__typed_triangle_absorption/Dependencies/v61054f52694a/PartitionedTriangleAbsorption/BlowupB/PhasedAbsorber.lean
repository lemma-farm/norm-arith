/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.LinearAbsorber
/-! # BlowupB.PhasedAbsorber — absorbers from phased trails, for every family

A **phased trail system** for `P` (`PhasedTrail`) is a permutation `σ` of positions `I`, a trail
`x` with `srcE σ x = P` (injective edges), and a phase `κ : I → Fin 3` increasing by one along
`σ`, such that

* every three consecutive classes `p (x i), p (x (σ i)), p (x (σ (σ i)))` form a type of `F`;
* along each cycle of `σ`, all positions of phase `0` lie in one class (the centre class).

`phased_private_absorber`: in every `G` inside the `F`-blowup with `missDeg ≤ d` and classes of
size more than `|Z| + 6K + (4K + 2)(d + 1)`, a set `P ⊆ E(G)` with a phased trail system and
`|P| ≤ K` has an absorber `A ⊆ E(G)` on at most `4K` fresh vertices outside `Z ∪ V(P)`.

No hypothesis on `F` is used (repeated classes allowed, no linearity, no `ThreeStepLinks`).
The construction is the one of `LinearAbsorber` (odd transformer with walks of length `1`,
windmill target with one centre per cycle); the family enters only through the existence of
phased trail systems.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset Equiv
universe u
variable {t : ℕ}
/-- A phased trail system for `P` on the positions `I`. -/
structure PhasedTrail {V : Type*} [DecidableEq V] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (P : Finset (Sym2 V)) (I : Type*) [Fintype I]
    [DecidableEq I] where
  σ : Perm I
  x : I → V
  κ : I → Fin 3
  hx : ∀ i, x i ≠ x (σ i)
  hinj : Function.Injective fun i => s(x i, x (σ i))
  hsrc : srcE σ x = P
  hκ : ∀ i, κ (σ i) = κ i + 1
  hcen : ∀ i j, σ.SameCycle i j → κ i = 0 → κ j = 0 → p (x i) = p (x j)
  htrip : ∀ i, ({p (x i), p (x (σ i)), p (x (σ (σ i)))} : Multiset (Fin t)) ∈ F
section Pairs
variable {F : Finset (Multiset (Fin t))} {a b c : Fin t}
end Pairs
section Assembly
variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 V)} {I : Type*} [Fintype I] [DecidableEq I]
  (T : PhasedTrail p F P I)
end Assembly
end PartitionedTriangleAbsorption.BlowupB
