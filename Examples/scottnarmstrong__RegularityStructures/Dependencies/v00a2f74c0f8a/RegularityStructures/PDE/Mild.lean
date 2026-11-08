/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.PDE.Duhamel
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
end RegularityStructures.PDE
end
public section
open MeasureTheory Set Filter Topology Real
open scoped NNReal
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
section Nemytskii
omit [NormedSpace ℝ E]
end Nemytskii
section Existence
variable (G : C(ℝ × Torus3 × E, E)) (u₀ : C(Torus3, E)) {T : ℝ} (hT : 0 ≤ T) (lam : ℝ)
end Existence
end RegularityStructures.PDE
end
