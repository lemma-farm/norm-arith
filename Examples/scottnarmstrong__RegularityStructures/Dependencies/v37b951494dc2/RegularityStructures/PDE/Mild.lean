/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v37b951494dc2.RegularityStructures.PDE.Duhamel
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Mild solutions of semilinear heat equations on `T³`

For a continuous nonlinearity `G : ℝ × T³ × E → E` and `u₀ ∈ C(T³, E)`, a path
`u : ℝ → C(T³, E)` is a mild solution of `∂_t u = Δu + G(t, x, u)`, `u(0) = u₀`, on `[0, T]` if
`u(t) = P_t u₀ + ∫₀ᵗ P_{t-s} G(s, ·, u(s)) ds` for `t ∈ [0, T]`.

## Main results

* `IsMildSolution.eqOn`: two continuous mild solutions agree on `[0, T]` when `G` is Lipschitz in
  `u` (Grönwall);
* `exists_isMildSolution`: a continuous mild solution exists on `[0, T]` when `G` is globally
  Lipschitz in `u` for `t ∈ [0, T]` (Banach's fixed point theorem in the weighted norm
  `sup_t e^{-λt} ‖u(t)‖`, which makes the Picard map a contraction on the whole interval).
-/
@[expose] public noncomputable section
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The Nemytskii operator `v ↦ G(s, ·, v(·))` on `C(T³, E)`. -/
def nemytskii (G : C(ℝ × Torus3 × E, E)) (s : ℝ) (v : C(Torus3, E)) : C(Torus3, E) :=
  ⟨fun x => G (s, x, v x), by fun_prop⟩
end RegularityStructures.PDE
end
public section
open MeasureTheory Set Filter Topology Real
open scoped NNReal
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
section Nemytskii
omit [NormedSpace ℝ E]
theorem continuous_nemytskii (G : C(ℝ × Torus3 × E, E)) :
    Continuous fun p : ℝ × C(Torus3, E) => nemytskii G p.1 p.2 := by
  let H : C((ℝ × C(Torus3, E)) × Torus3, E) :=
    ⟨fun q => G (q.1.1, q.2, q.1.2 q.2), by fun_prop⟩
  exact H.curry.continuous
theorem continuous_nemytskii_comp (G : C(ℝ × Torus3 × E, E)) {u : ℝ → C(Torus3, E)}
    (hu : Continuous u) : Continuous fun s => nemytskii G s (u s) :=
  (continuous_nemytskii G).comp (continuous_id.prodMk hu)
end Nemytskii
section Existence
variable (G : C(ℝ × Torus3 × E, E)) (u₀ : C(Torus3, E)) {T : ℝ} (hT : 0 ≤ T) (lam : ℝ)
end Existence
end RegularityStructures.PDE
end
