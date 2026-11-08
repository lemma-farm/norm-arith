/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v3ddeb0cdd112.RegularityStructures.PDE.HeatOp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The Duhamel integral

For a continuous path `h : ℝ → C(T³, E)`,
`duhamel h t = ∫₀ᵗ P_{t-s} h(s) ds`, a Bochner integral in the Banach space `C(T³, E)`. This is the
solution operator of the inhomogeneous heat equation `∂_t v = Δv + h`, `v(0) = 0`, in mild form.

## Main results

* `continuous_duhamel`: `t ↦ duhamel h t` is continuous;
* `duhamel_apply`: the integral may be evaluated pointwise in `x`;
* `norm_duhamel_le`: `‖duhamel h t‖ ≤ ∫₀ᵗ ‖h s‖ ds`;
* linearity in `h`, commutation with translations and with linear maps of the values;
* `duhamel_congr`: `duhamel h t` only depends on `h` on `[0, t]`.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.PDE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end RegularityStructures.PDE
end
public section
open MeasureTheory Set Filter Topology
namespace RegularityStructures.PDE
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
variable [CompleteSpace E] [CompleteSpace F]
end RegularityStructures.PDE
end
