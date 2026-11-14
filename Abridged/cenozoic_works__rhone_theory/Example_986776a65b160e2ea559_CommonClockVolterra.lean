module

public import Mathlib
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.Positivity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_986776a65b160e2ea559_CommonClockVolterra ====
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Volterra uniqueness and Gronwall bounds for the common-clock equations -/
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option linter.unusedVariables false in
theorem commonClock_volterra_unique {K : ℝ → ℝ → ℝ} {b u v : ℝ → ℝ} {T M : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hKi : ∀ t ∈ Icc 0 T, IntervalIntegrable (K t) volume 0 t)
    (hKb : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, |K t s| ≤ M)
    (huEq : ∀ t ∈ Icc 0 T, u t = b t + ∫ s in (0 : ℝ)..t, K t s * u s)
    (hvEq : ∀ t ∈ Icc 0 T, v t = b t + ∫ s in (0 : ℝ)..t, K t s * v s) 
    (h_Rhone_Statistics_Identifiability_commonClock_integral_gronwall_zero : ∀ {h : ℝ → ℝ} {T K : ℝ},
      0 ≤ T →
        IntervalIntegrable h MeasureTheory.MeasureSpace.volume 0 T →
          (∀ t ∈ Set.Icc 0 T, 0 ≤ h t) →
            (∀ t ∈ Set.Icc 0 T, h t ≤ K * ∫ (s : ℝ) in 0..t, h s) →
              Set.EqOn h (fun (x : ℝ) ↦ 0) (Set.Icc 0 T))
    :
    EqOn u v (Icc 0 T) := by
  have hcont : ContinuousOn (fun s => |u s - v s|) (Icc 0 T) :=
    (hu.sub hv).abs
  have hz := h_Rhone_Statistics_Identifiability_commonClock_integral_gronwall_zero hT
    (hcont.intervalIntegrable_of_Icc hT) (fun _ _ => abs_nonneg _) (K := M) ?_
  · intro t ht
    exact sub_eq_zero.mp (abs_eq_zero.mp (hz ht))
  intro t ht
  have hs : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hui : IntervalIntegrable (fun s => K t s * u s) volume 0 t :=
    (hKi t ht).mul_continuousOn ((hu.mono hs).mono (by rw [uIcc_of_le ht.1]))
  have hvi : IntervalIntegrable (fun s => K t s * v s) volume 0 t :=
    (hKi t ht).mul_continuousOn ((hv.mono hs).mono (by rw [uIcc_of_le ht.1]))
  have he : u t - v t = ∫ s in (0 : ℝ)..t, K t s * (u s - v s) := by
    rw [huEq t ht, hvEq t ht]
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hui hvi]
    ring
  rw [he]
  calc
    |∫ s in (0 : ℝ)..t, K t s * (u s - v s)| ≤
        ∫ s in (0 : ℝ)..t, |K t s * (u s - v s)| :=
      by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm
            (f := fun s => K t s * (u s - v s)) ht.1)
    _ ≤ ∫ s in (0 : ℝ)..t, M * |u s - v s| := by
      apply intervalIntegral.integral_mono_on ht.1
      · simpa only [mul_sub] using (hui.sub hvi).abs
      · exact ((hcont.mono hs).intervalIntegrable_of_Icc ht.1).const_mul M
      · intro s hs'
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hKb t ht s hs') (abs_nonneg _)
    _ = M * ∫ s in (0 : ℝ)..t, |u s - v s| := intervalIntegral.integral_const_mul _ _
end Rhone.Statistics.Identifiability
