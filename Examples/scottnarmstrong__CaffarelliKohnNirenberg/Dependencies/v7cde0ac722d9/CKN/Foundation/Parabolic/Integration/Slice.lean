-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Parabolic.Integration.Average
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
set_option warningAsError true
/-!
# Spatial and space-time averages

This file gives named wrappers for the two averages used on parabolic cylinders.
The definitions remain the ordinary Mathlib set averages, so existing `average`,
`eLpNorm`, and restriction lemmas apply without a second normalization convention.
-/
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
noncomputable section
namespace CKN.Foundation.Parabolic.Integration
theorem setAverage_norm_rpow_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {s : Set α} {f : α → E} {p : ℝ}
    (hp : 1 ≤ p) (hsPos : 0 < μ s) (hsTop : μ s < ∞)
    (hf : IntegrableOn f s μ)
    (hfp : IntegrableOn (fun x => ‖f x‖ ^ p) s μ) :
    ‖⨍ x in s, f x ∂μ‖ ^ p ≤ ⨍ x in s, ‖f x‖ ^ p ∂μ := by
  calc
    ‖⨍ x in s, f x ∂μ‖ ^ p ≤ (⨍ x in s, ‖f x‖ ∂μ) ^ p := by
      exact Real.rpow_le_rpow (norm_nonneg _) (setAverage_norm_le μ s f)
        (zero_le_one.trans hp)
    _ ≤ ⨍ x in s, ‖f x‖ ^ p ∂μ := by
      have hfnorm : IntegrableOn (fun x => ‖f x‖) s μ := by
        change Integrable (fun x => ‖f x‖) (μ.restrict s)
        exact hf.norm
      exact (convexOn_rpow hp).map_set_average_le
        (Real.continuous_rpow_const (zero_le_one.trans hp)).continuousOn isClosed_Ici
        hsPos.ne' hsTop.ne (ae_of_all _ fun x => norm_nonneg (f x)) hfnorm hfp
end CKN.Foundation.Parabolic.Integration
