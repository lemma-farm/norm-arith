/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.TeoremaB
/-! # BlowupB.TeoremaBBalanced — Theorem B for ε-balanced blowups under a finite condition on `F`

`BalancedWeights F w`: positive type weights with `∑_{c : c ::ₘ {a,b} ∈ F} w (c ::ₘ {a,b}) = t` for
every allowed pair `ab` — a finite linear feasibility condition on the family alone (the load
equations of the balanced complete blowup).

**`teoremaB_balanced`**: under `KeevashTypedSpec F`, a family with balanced weights has the
following property. There are `η, δ > 0` and `N` such that every graph on `n ≥ N` vertices using
only allowed pairs, with at most `δ n` allowed non-neighbours per vertex, all classes of size in
`[(1/t - η) n, (1/t + η) n]`, and integrally `F`-divisible (Definition 13.5), has an
`F`-decomposition. This is the form of Theorem B in `PLAN_17_DESDE_13_16_20261010.md` §1, with
the hinge hypothesis removed and the fractional hypothesis replaced by `BalancedWeights`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {t : ℕ}
end PartitionedTriangleAbsorption.BlowupB
