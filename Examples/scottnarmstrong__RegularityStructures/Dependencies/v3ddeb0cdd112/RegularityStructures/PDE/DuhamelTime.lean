/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.PDE.HeatTime
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.PDE.Duhamel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The time derivative of the Duhamel integral

* `norm_heatOp_apply_sub_le`: for `g` with two continuous derivatives, `t ↦ P_t g(x)` is
  Lipschitz on `ℝ` with constant `‖Δg‖`;
* `hasDerivAt_duhamel_apply`: if every `H(s)`, `s ∈ [0, T]`, has two continuous derivatives and the
  Laplacians form a continuous path, then for `t ∈ (0, T)`
  `∂_t ∫₀ᵗ P_{t-s} H(s) ds = H(t) + ∫₀ᵗ P_{t-s} ΔH(s) ds`.

For the second statement write `∫₀ᵗ P_{t-s} H(s) ds = ∫₀ᵀ (P_{t-s} H(s) - H(s)) ds + ∫₀ᵗ H(s) ds`;
the first integrand vanishes for `s ≥ t` because `P_τ` is the identity for `τ ≤ 0`, and is
Lipschitz in `t` uniformly in `s`, so it can be differentiated under the integral sign.
-/
public section
open MeasureTheory Set Filter Topology Real
open scoped Interval
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E]
omit [CompleteSpace E] in
/-- The Laplacian is postcomposition with the trace map `Fin 3 → Fin 3 → E → E`. -/
theorem torusLap_eq_compLeft (D2g : C(Torus3, Fin 3 → Fin 3 → E)) :
    torusLap D2g = (∑ i : Fin 3, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => E) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → E) i)).compLeftContinuous
        ℝ Torus3 D2g := by
  ext x
  simp [torusLap_apply]
end RegularityStructures.PDE
end
