/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.RainbowTrails
/-! # BlowupB.RainbowTarget — the windmill target for rainbow trails

Positions `I` with a permutation `σ` and a phase `κ : I → Fin 3` increasing by one along `σ`
(for rainbow trails, `κ i` is the class of `x i`). Fresh vertices are given by an injective
`g : Slot3 I σ → W`: a centre `Z o` for every cycle `o` of `σ`, and `U j`, `Wt j` for every
position. The target trail

  `y i = Z ⟦i⟧`, `U (σ⁻¹ i)`, `Wt (σ⁻² i)` according as `κ i = 0, 1, 2`

is a **windmill** at every cycle: its edges are the triangles `{Z ⟦j⟧, U j, Wt j}` over the
positions `j` of phase `0` (`srcE_windmill`), hence it decomposes (`windmill_hasDecomp`). The
trail data `y i ≠ y (σ i)` and injectivity of the trail edges also hold.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset Equiv
variable {I : Type*} [Fintype I] [DecidableEq I] (σ : Perm I)
/-- The cycles of `σ`. -/
abbrev Orb : Type _ := Quotient (Perm.SameCycle.setoid σ)
/-- Slots of fresh target vertices: centres, `U`, `Wt`. -/
abbrev Slot3 : Type _ := Orb σ ⊕ (I ⊕ I)
variable {σ} {W : Type*} [DecidableEq W] (g : Slot3 σ → W) (κ : I → Fin 3)
variable {g κ}
section Phase
variable (hκ : ∀ i, κ (σ i) = κ i + 1)
include hκ
end Phase
section Decomp
variable (hκ : ∀ i, κ (σ i) = κ i + 1) (hg : Function.Injective g)
include hκ hg
end Decomp
end PartitionedTriangleAbsorption.BlowupB
