module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_c9a6922966835e030745_LaplaceNullFunction ====
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # A nonzero bounded continuous function with vanishing Laplace transforms at `k(k-1)/2` -/
@[expose] public section
namespace Rhone.Analysis
open MeasureTheory Set Filter Complex
open scoped Topology FourierTransform
theorem norm_sq_add_sq_ge (β : ℂ) (y : ℝ) :
    min (β ^ 2).re 1 * (1 + y ^ 2) ≤ ‖β ^ 2 + (y : ℂ) ^ 2‖ := by
  have hre : (β ^ 2 + (y : ℂ) ^ 2).re = (β ^ 2).re + y ^ 2 := by
    simp [← Complex.ofReal_pow]
  calc min (β ^ 2).re 1 * (1 + y ^ 2) = min (β ^ 2).re 1 + min (β ^ 2).re 1 * y ^ 2 := by ring
    _ ≤ (β ^ 2).re + y ^ 2 := by
        gcongr
        · exact min_le_left _ _
        · calc min (β ^ 2).re 1 * y ^ 2 ≤ 1 * y ^ 2 := by
                gcongr; exact min_le_right _ _
            _ = y ^ 2 := one_mul _
    _ = (β ^ 2 + (y : ℂ) ^ 2).re := hre.symm
    _ ≤ ‖β ^ 2 + (y : ℂ) ^ 2‖ := Complex.re_le_norm _
end Rhone.Analysis
