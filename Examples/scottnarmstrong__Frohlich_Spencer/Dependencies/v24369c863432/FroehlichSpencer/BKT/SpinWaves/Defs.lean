/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v24369c863432.FroehlichSpencer.BKT.FiniteGraph.Basic
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v24369c863432.FroehlichSpencer.BKT.Surface.DensityCenter
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v24369c863432.FroehlichSpencer.BKT.Charges.DensityNeighbourhood
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Spin-wave energy from KP §4.3

The canonical `Multigraph.comparableDensities` and `Multigraph.densityDomainPlus` carriers, with
their KP characterizations, live in `Charges.DensityNeighbourhood`.

This file adds the spin-wave
energy functional (KP (2.12)); source-facing declarations remain internal until .
-/
@[expose] public section
namespace FroehlichSpencer.BKT.SpinWaves
universe u v
/-- KP (2.12): the linear charge term minus half the edge-once Dirichlet energy. -/
noncomputable def energyFunctional {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (β : ℝ) (a : V → ℝ) (ρ : V → ℤ) : ℝ :=
  Multigraph.pairing a (fun j => (ρ j : ℝ)) - (β / 2) * G.energy a
/-- The candidate energy functional is KP (2.12), with each multigraph edge counted once. -/
theorem energyFunctional_eq_KP {V : Type u} {E : Type v} [Fintype V] [Fintype E]
    (G : Multigraph V E) (β : ℝ) (a : V → ℝ) (ρ : V → ℤ) :
    energyFunctional G β a ρ =
      (∑ j, a j * (ρ j : ℝ)) - (β / 2) * ∑ e, (G.grad a e) ^ 2 := by
  simp [energyFunctional, Multigraph.pairing, Multigraph.energy]
end FroehlichSpencer.BKT.SpinWaves
end
