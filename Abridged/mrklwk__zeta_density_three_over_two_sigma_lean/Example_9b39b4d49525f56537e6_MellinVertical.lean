module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_9b39b4d49525f56537e6_MellinVertical ====
-- Reversible module-visibility port of the audited development.
/-
Selected actual contour convergence proofs adapted from Scott McColm,
PointMeanMellinVertical.lean and PointMeanContourBasic.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_SHIFT_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
The local proved Gamma kernel and Abel continuation replace source imports.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set MeasureTheory Filter Topology

open scoped ComplexOrder
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean


set_option linter.unusedVariables false in
theorem ford_norm_riemannZeta_le_real
    {sigma t : ℝ} (hsigma : 1 < sigma) 
    (h_MathCollab_Density_Stronger_PointMean_ford_norm_eq_re_of_nonneg : ∀ {z : ℂ}, 0 ≤ z → ‖z‖ = z.re)
    :
    ‖riemannZeta ((sigma : ℂ) + Complex.I * t)‖ ≤
      ‖riemannZeta (sigma : ℂ)‖ := by
  let s : ℂ := (sigma : ℂ) + Complex.I * t
  have hs : 1 < s.re := by simp [s, hsigma]
  have hsumS : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_one_iff.mpr hs
  have hsumSigma : LSeriesSummable (1 : ℕ → ℂ) (sigma : ℂ) :=
    LSeriesSummable_one_iff.mpr hsigma
  rw [← LSeries_one_eq_riemannZeta hs,
    ← LSeries_one_eq_riemannZeta hsigma, LSeries, LSeries]
  calc
    ‖∑' n, LSeries.term (1 : ℕ → ℂ) s n‖ ≤
        ∑' n, ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
      norm_tsum_le_tsum_norm hsumS.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      apply hsumS.norm.tsum_le_tsum
        (fun n => LSeries.norm_term_le_of_re_le_re
          (1 : ℕ → ℂ) (by simp [s]) n)
        hsumSigma.norm
    _ = ‖∑' n, LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ := by
      have hnonneg (n : ℕ) :
          0 ≤ LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n :=
        LSeries.term_nonneg (by norm_num : (0 : ℂ) ≤ 1) sigma
      have hnormTerm (n : ℕ) :
          ‖LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n‖ =
            (LSeries.term (1 : ℕ → ℂ) (sigma : ℂ) n).re := by
        exact h_MathCollab_Density_Stronger_PointMean_ford_norm_eq_re_of_nonneg (hnonneg n)
      simp_rw [hnormTerm]
      rw [← Complex.re_tsum hsumSigma]
      exact (h_MathCollab_Density_Stronger_PointMean_ford_norm_eq_re_of_nonneg (tsum_nonneg hnonneg)).symm

end MathCollab.Density.Stronger.PointMean
