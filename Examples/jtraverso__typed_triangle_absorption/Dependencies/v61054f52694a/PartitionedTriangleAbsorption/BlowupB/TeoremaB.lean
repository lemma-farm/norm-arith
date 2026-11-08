/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.TypicalReserveMain
/-! # BlowupB.TeoremaB — Theorem B (nearly complete blowups, every family) from Keevash

**`teoremaB_of_keevash`**. Let `F` be a family of 3-element types and assume the typed Keevash
interface `KeevashTypedSpec F`. For every `γ, ω₁ > 0` there are `ε, δ > 0` and `N` such that
every graph `G` on `n ≥ N` vertices using only allowed pairs, with at most `δ n` allowed
non-neighbours per vertex and classes of size `≥ γ n`, which is integrally `F`-divisible
(Definition 13.5) and admits **type weights** `ω₁ ≤ wt τ ≤ 1/ω₁` solving the load equations of
the complete blowup up to `ε`,

`|∑_τ wt τ · (∑_{c : c ::ₘ {a,b} = τ} (|V_c| - count c {a,b})) / n - 1| ≤ ε` for allowed `ab`,

has an `F`-decomposition. No hinge hypothesis is needed. The weight condition is the
fractional hypothesis required by `typeLoad_obstruction_001_012` (it fails for `{001, 012}` with
equal classes).

Proof: `G` is `CNExt` (common neighbourhoods lose at most `h δ n`), `TriRegular` by
`triRegular_union` with `L = ∅` (typed-thirds counts are within `2 δ n + 2 t` of the complete
counts), and `IsIntDiv`; apply the interface.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {t : ℕ}
section Host
variable {V : Type*} [Fintype V] [DecidableEq V]
end Host
end PartitionedTriangleAbsorption.BlowupB
