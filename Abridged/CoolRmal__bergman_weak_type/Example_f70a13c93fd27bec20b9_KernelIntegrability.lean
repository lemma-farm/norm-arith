module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntegrableOn

-- ==== Examples.CoolRmal__bergman_weak_type.Dependencies.vdcb2924e9310.BergmanWeakType.Definitions ====
public section
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
set_option autoImplicit false
/-! # Bergman projections and their weak type constants -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BergmanWeakType
/-- The open unit disk in the complex plane. -/
def disk : Set ℂ := Metric.ball 0 1

def weightedKernel (α : ℝ) (z w : ℂ) : ℂ := (1 - z * star w) ^ (-(α + 2) : ℂ)
end BergmanWeakType

end
end
end

-- ==== Examples.CoolRmal__bergman_weak_type.Examples.Example_f70a13c93fd27bec20b9_KernelIntegrability ====
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
set_option autoImplicit false
/-! # Integrability of the Bergman integral formulas

For each interior output point, both kernel columns are bounded on the input disk. Consequently
their products with integrable inputs are integrable. The Bochner integrals defining the complex
projections therefore represent genuine integrable functions, and the positive outputs are finite.
-/
public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BergmanWeakType


set_option linter.unusedVariables false in
theorem norm_weightedKernel_le {α : ℝ} (hα : -1 < α) {z w : ℂ}
    (hz : z ∈ disk) (hw : w ∈ disk) 
    (h_BergmanWeakType_kernel_denominator_norm_lower : ∀ (z : ℂ) {w : ℂ}, w ∈ BergmanWeakType.disk → 1 - ‖z‖ ≤ ‖1 - z * Star.star w‖)
    (h_BergmanWeakType_norm_weightedKernel : ∀ (α : ℝ) (z w : ℂ), ‖BergmanWeakType.weightedKernel α z w‖ = ‖1 - z * Star.star w‖ ^ (-(α + 2)))
    (h_BergmanWeakType_mem_disk_iff : ∀ (z : ℂ), z ∈ BergmanWeakType.disk ↔ ‖z‖ < 1)
    :
    ‖weightedKernel α z w‖ ≤ (1 - ‖z‖) ^ (-(α + 2)) := by
  rw [h_BergmanWeakType_norm_weightedKernel]
  exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ((h_BergmanWeakType_mem_disk_iff z).mp hz))
    (h_BergmanWeakType_kernel_denominator_norm_lower z hw) (by linarith)
end BergmanWeakType
