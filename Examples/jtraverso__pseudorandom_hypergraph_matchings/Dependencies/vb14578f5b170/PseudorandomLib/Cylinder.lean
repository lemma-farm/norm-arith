/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__pseudorandom_hypergraph_matchings.Dependencies.vb14578f5b170.PseudorandomLib.Bernstein
public import Mathlib
set_option relaxedAutoImplicit false
/-! # Concentration of weighted counts of monochromatic sets

Colour every coordinate `v ∈ ι` independently and uniformly with one of `m` colours. For a
family of sets `B s ⊆ ι` with weights `w s ≥ 0`, consider the weighted number of sets that are
entirely coloured with the fixed colour `a`:

  `cyl S w B a ω = ∑_{s ∈ S} w s · [ω ≡ a on B s]`.

Its expectation is `∑ w s m^{-|B s|}`, and it is concentrated by the Bernstein-type
bounded-differences inequality of `Bernstein.lean`: coordinate `v` changes it by at most
`c v = ∑_{s : v ∈ B s} w s`, and only if one of the two colours is `a`.
-/
@[expose] public section
namespace Pseudorandom
open Finset
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]
/-- The uniform distribution on `m` colours at every coordinate. -/
noncomputable def unif (ι : Type*) (m : ℕ) : ι → Fin m → ℝ := fun _ _ => 1 / m
end Pseudorandom
