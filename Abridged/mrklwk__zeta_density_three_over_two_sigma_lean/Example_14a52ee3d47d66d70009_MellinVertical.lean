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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.ved8caad72527.MathCollab.Density.Stronger.PointMean.FiniteRectangle ====
public section
-- Reversible module-visibility port of the audited development.
/-
Selected native Heath--Brown point-mean contour proofs adapted from
Scott McColm, exact revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1,
PointMeanGammaPole.lean and PointMeanLemmaThreeContour.lean.
MIT-0, Copyright 2026 S. McColm. See ../../../../../third_party/twelfth/POINT_MEAN_RECTANGLE_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
The local imported rectangle residue machinery retains its Apache-2.0 attribution.
No source project module is imported; no point-mean or moment bound is assumed.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set MeasureTheory Filter

open scoped Topology Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.PointMean
/-- The literal Gamma--zeta-square Mellin kernel of the native point-mean proof. -/
def heathBrownZetaSquareMellinIntegrand (s w : ℂ) : ℂ :=
  Complex.Gamma w * riemannZeta (s + w) ^ 2

end MathCollab.Density.Stronger.PointMean

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_14a52ee3d47d66d70009_MellinVertical ====
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
private theorem integrable_heathBrownZetaSquareMellinIntegrand_of_exp
    {s : ℂ} {a G : ℝ}
    (haLower : -(1 : ℝ) < a) (ha0 : a ≠ 0)
    (hsRe : 1 / 4 ≤ s.re + a) (hpole : s.re + a ≠ 1) (hG : 0 ≤ G)
    (hGamma : ∀ v : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        G * Real.exp (-|v|)) 
    (h_MathCollab_Density_Stronger_PointMean_continuous_heathBrownZetaSquareMellinIntegrand_vertical : ∀ {s : ℂ} {a : ℝ},
      -1 < a →
        a ≠ 0 →
          s.re + a ≠ 1 →
            Continuous fun (v : ℝ) ↦
              MathCollab.Density.Stronger.PointMean.heathBrownZetaSquareMellinIntegrand s
                ((↑a : ℂ) + (↑v : ℂ) * Complex.I))
    (h_MathCollab_Density_Stronger_PointMean_integrable_abs_sq_mul_exp_neg_abs : MeasureTheory.Integrable (fun (v : ℝ) ↦ |v| ^ 2 * Real.exp (-|v|)) MeasureTheory.MeasureSpace.volume)
    (h_MathCollab_Density_ZetaGrowth_norm_riemannZeta_le_five_mul_norm : ∀ {s : ℂ}, 1 / 4 ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ 5 * ‖s‖)
    :
    Integrable (fun v : ℝ =>
      heathBrownZetaSquareMellinIntegrand s
        ((a : ℂ) + (v : ℂ) * I)) := by
  let f : ℝ → ℂ := fun v =>
    heathBrownZetaSquareMellinIntegrand s
      ((a : ℂ) + (v : ℂ) * I)
  let B : ℝ := |s.re + a| + |s.im| + 2
  let M : ℝ := 100 * G
  let g : ℝ → ℝ := fun v => M * (|v| ^ 2 * Real.exp (-|v|))
  have hBone : 1 ≤ B := by
    dsimp only [B]
    linarith [abs_nonneg (s.re + a), abs_nonneg s.im]
  have hBpos : 0 < B := zero_lt_one.trans_le hBone
  have hCont : Continuous f := by
    simpa [f] using
      h_MathCollab_Density_Stronger_PointMean_continuous_heathBrownZetaSquareMellinIntegrand_vertical
        haLower ha0 hpole
  have hg : Integrable g := h_MathCollab_Density_Stronger_PointMean_integrable_abs_sq_mul_exp_neg_abs.const_mul M
  have hPos : IntegrableOn f (Ioi B) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hvPos : 0 < v := hBpos.trans hv
    have hfar : |s.re + a| + |s.im| + 2 ≤ |v| := by
      rw [abs_of_pos hvPos]
      exact hv.le
    have hheight : 1 ≤ |s.im + v| := by
      have htri := abs_sub_abs_le_abs_sub v (-s.im)
      rw [abs_neg, sub_neg_eq_add] at htri
      rw [add_comm]
      linarith [abs_nonneg (s.re + a)]
    have hzetaRe : (1 / 4 : ℝ) ≤
        (s + ((a : ℂ) + (v : ℂ) * I)).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      exact hsRe
    have hzeta := h_MathCollab_Density_ZetaGrowth_norm_riemannZeta_le_five_mul_norm hzetaRe
      (by simpa using hheight)
    have hnorm :
        ‖s + ((a : ℂ) + (v : ℂ) * I)‖ ≤ 2 * |v| := by
      calc
        ‖s + ((a : ℂ) + (v : ℂ) * I)‖ ≤
            |(s + ((a : ℂ) + (v : ℂ) * I)).re| +
              |(s + ((a : ℂ) + (v : ℂ) * I)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |s.re + a| + |s.im + v| := by congr 1 <;> simp
        _ ≤ |s.re + a| + (|s.im| + |v|) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * |v| := by linarith
    have hzeta' :
        ‖riemannZeta (s + ((a : ℂ) + (v : ℂ) * I))‖ ≤
          5 * (2 * |v|) :=
      hzeta.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
    change ‖heathBrownZetaSquareMellinIntegrand s
      ((a : ℂ) + (v : ℂ) * I)‖ ≤ g v
    rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow]
    dsimp only [g, M]
    calc
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ *
          ‖riemannZeta (s + ((a : ℂ) + (v : ℂ) * I))‖ ^ 2 ≤
        (G * Real.exp (-|v|)) * (5 * (2 * |v|)) ^ 2 := by
          exact mul_le_mul (hGamma v)
            (pow_le_pow_left₀ (norm_nonneg _) hzeta' 2)
            (by positivity) (by positivity)
      _ = 100 * G * (|v| ^ 2 * Real.exp (-|v|)) := by ring
  have hNeg : IntegrableOn f (Iio (-B)) := by
    apply hg.integrableOn.mono' hCont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with v hv
    have hvNeg : v < 0 := hv.trans_le (neg_nonpos.mpr hBpos.le)
    have hfar : |s.re + a| + |s.im| + 2 ≤ |v| := by
      rw [abs_of_neg hvNeg]
      change v < -(|s.re + a| + |s.im| + 2) at hv
      linarith
    have hheight : 1 ≤ |s.im + v| := by
      have htri := abs_sub_abs_le_abs_sub v (-s.im)
      rw [abs_neg, sub_neg_eq_add] at htri
      have hlower : |v| - |s.im| ≤ |v + s.im| := htri
      rw [add_comm] at hlower
      linarith [abs_nonneg (s.re + a)]
    have hzetaRe : (1 / 4 : ℝ) ≤
        (s + ((a : ℂ) + (v : ℂ) * I)).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      exact hsRe
    have hzeta := h_MathCollab_Density_ZetaGrowth_norm_riemannZeta_le_five_mul_norm hzetaRe
      (by simpa using hheight)
    have hnorm :
        ‖s + ((a : ℂ) + (v : ℂ) * I)‖ ≤ 2 * |v| := by
      calc
        ‖s + ((a : ℂ) + (v : ℂ) * I)‖ ≤
            |(s + ((a : ℂ) + (v : ℂ) * I)).re| +
              |(s + ((a : ℂ) + (v : ℂ) * I)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |s.re + a| + |s.im + v| := by congr 1 <;> simp
        _ ≤ |s.re + a| + (|s.im| + |v|) := by
          gcongr
          exact abs_add_le _ _
        _ ≤ 2 * |v| := by linarith
    have hzeta' :
        ‖riemannZeta (s + ((a : ℂ) + (v : ℂ) * I))‖ ≤
          5 * (2 * |v|) :=
      hzeta.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
    change ‖heathBrownZetaSquareMellinIntegrand s
      ((a : ℂ) + (v : ℂ) * I)‖ ≤ g v
    rw [heathBrownZetaSquareMellinIntegrand, norm_mul, norm_pow]
    dsimp only [g, M]
    calc
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ *
          ‖riemannZeta (s + ((a : ℂ) + (v : ℂ) * I))‖ ^ 2 ≤
        (G * Real.exp (-|v|)) * (5 * (2 * |v|)) ^ 2 := by
          exact mul_le_mul (hGamma v)
            (pow_le_pow_left₀ (norm_nonneg _) hzeta' 2)
            (by positivity) (by positivity)
      _ = 100 * G * (|v| ^ 2 * Real.exp (-|v|)) := by ring
  have hMid : IntegrableOn f (Icc (-B) B) :=
    hCont.continuousOn.integrableOn_Icc
  have hNegClosed : IntegrableOn f (Iic (-B)) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hNeg
  have hLeft := hNegClosed.union hMid
  have hLeftSet : Iic (-B) ∪ Icc (-B) B = Iic B := by
    ext v
    simp only [mem_union, mem_Iic, mem_Icc]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases hv : v ≤ -B
      · exact Or.inl hv
      · exact Or.inr ⟨by linarith, h⟩
  rw [hLeftSet] at hLeft
  rw [← integrableOn_univ]
  have hAll := hLeft.union hPos
  have hAllSet : Iic B ∪ Ioi B = Set.univ := by
    ext v
    simp only [mem_union, mem_Iic, mem_Ioi, mem_univ, iff_true]
    exact le_or_gt v B
  rwa [hAllSet] at hAll
end MathCollab.Density.Stronger.PointMean
