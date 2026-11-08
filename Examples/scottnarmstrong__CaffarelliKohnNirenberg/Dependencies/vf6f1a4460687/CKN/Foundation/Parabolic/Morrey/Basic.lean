-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Parabolic.Integration.Scaling
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Parabolic.Doubling
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic Morrey cells and norms

This module records the extended-real Morrey seminorm on the backward
parabolic cylinders already defined by the parabolic geometry module.  The
metric-ball version is kept alongside it; the two versions are compared by
the inclusions between cylinders and metric balls.
-/
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic.Morrey
private abbrev Q := (5 : ℝ)
/-- The integral part of a Morrey cell on a parabolic cylinder. -/
def cylinderPowerIntegral (p : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w| ^ p
def morreyCell (p q : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r) ^ (-(Q * (1 - p / q) / p)) *
    (cylinderPowerIntegral p f z r) ^ (1 / p)
/-! The fixed homogeneous dimension in the cylinder normalization. -/
def morreyNorm (p q : ℝ) (f : ParabolicPoint → ℝ) : ℝ≥0∞ :=
  ⨆ z : ParabolicPoint, ⨆ r : {r : ℝ // 0 < r}, morreyCell p q f z r.1
private lemma holder_exponents {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    (q / p).HolderConjugate (q / (q - p)) := by
  apply Real.holderConjugate_iff.mpr
  constructor
  · exact (one_lt_div hp).mpr hpq
  · have hq : q ≠ 0 := (lt_of_lt_of_le hp hpq.le).ne'
    field_simp [hp.ne', hq, sub_ne_zero.mpr hpq.ne']
    ring
private lemma cylinderPowerIntegral_holder {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral p f z r ≤
      (cylinderPowerIntegral q f z r) ^ (p / q) *
        (volume (parabolicCylinder z.1 z.2 r)) ^ (1 - p / q) := by
  let μ : Measure ParabolicPoint := volume.restrict (parabolicCylinder z.1 z.2 r)
  let F : ParabolicPoint → ℝ≥0∞ := fun w => ENNReal.ofReal |f w|
  have hF : AEMeasurable F μ := by
    simpa only [F, Real.norm_eq_abs] using hf.norm.restrict.ennreal_ofReal
  have hone : AEMeasurable (fun _ : ParabolicPoint => (1 : ℝ≥0∞)) μ := aemeasurable_const
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (holder_exponents hp hpq)
    (hF.pow_const p) hone
  have hpqpow : ∀ w, (F w ^ p) ^ (q / p) = F w ^ q := by
    intro w
    rw [← ENNReal.rpow_mul]
    field_simp [hp.ne']
  have hleft : (∫⁻ w, F w ^ p ∂μ) = cylinderPowerIntegral p f z r := by
    simp only [μ, F, cylinderPowerIntegral]
  have hq : (∫⁻ w, F w ^ q ∂μ) = cylinderPowerIntegral q f z r := by
    rfl
  have hq' : (∫⁻ w, (F w ^ p) ^ (q / p) ∂μ) =
      cylinderPowerIntegral q f z r := by
    calc
      _ = ∫⁻ w, F w ^ q ∂μ := by
        apply lintegral_congr
        exact hpqpow
      _ = _ := hq
  have honeint : (∫⁻ _w, (1 : ℝ≥0∞) ^ (q / (q - p)) ∂μ) =
      volume (parabolicCylinder z.1 z.2 r) := by
    simp [μ]
  simp only [Pi.mul_apply, mul_one] at hH
  rw [hleft, hq', honeint] at hH
  have hq0 : q ≠ 0 := (lt_of_lt_of_le hp hpq.le).ne'
  have h_exp1 : 1 / (q / p) = p / q := by
    field_simp [hp.ne', hq0]
  have h_exp2 : 1 / (q / (q - p)) = 1 - p / q := by
    field_simp [hq0, sub_ne_zero.mpr hpq.ne']
  rw [h_exp1, h_exp2] at hH
  exact hH
private lemma morreyCell_lower_p {p' p q : ℝ} (hp' : 0 < p') (hpp : p' < p)
    {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume)
    (z : ParabolicPoint) {r : ℝ} (hr : 0 < r) :
    morreyCell p' q f z r ≤
      (volume (parabolicCylinder 0 0 1)) ^ (1 / p' - 1 / p) *
        morreyCell p q f z r := by
  let V : ℝ≥0∞ := volume (parabolicCylinder z.1 z.2 r)
  let V₁ : ℝ≥0∞ := volume (parabolicCylinder 0 0 1)
  have hlocal := cylinderPowerIntegral_holder hp' hpp hf z r
  have hroot : (cylinderPowerIntegral p' f z r) ^ (1 / p') ≤
      (cylinderPowerIntegral p f z r) ^ (1 / p) *
        V ^ (1 / p' - 1 / p) := by
    have hlocal' := ENNReal.rpow_le_rpow hlocal (one_div_nonneg.mpr hp'.le)
    calc
      (cylinderPowerIntegral p' f z r) ^ (1 / p') ≤
          ((cylinderPowerIntegral p f z r) ^ (p' / p) *
            V ^ (1 - p' / p)) ^ (1 / p') := hlocal'
      _ = (cylinderPowerIntegral p f z r) ^ (1 / p) *
          V ^ (1 / p' - 1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp'.le),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1
        · field_simp [hp'.ne', (lt_of_lt_of_le hp' hpp.le).ne']
        · field_simp [hp'.ne', (lt_of_lt_of_le hp' hpp.le).ne']
  have hV : V = V₁ * (ENNReal.ofReal r) ^ (5 : ℝ) := by
    dsimp [V, V₁]
    have ht := Integration.volume_parabolicCylinder_translate
      z.1 (0 : Vec3) z.2 0 r
    have hs := volume_parabolicCylinder_radius_scale
      (x := (0 : Vec3)) (t := 0) (r := 1) (a := r) hr
    have ht' : volume (parabolicCylinder z.1 z.2 r) =
        volume (parabolicCylinder 0 0 r) := by
      simpa using ht
    have hs' : volume (parabolicCylinder 0 0 r) =
        ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder 0 0 1) := by
      calc
        volume (parabolicCylinder 0 0 r) =
            volume (parabolicCylinder 0 0 (r * 1)) := by rw [mul_one]
        _ = _ := hs
    calc
      volume (parabolicCylinder z.1 z.2 r) =
          volume (parabolicCylinder 0 0 r) := ht'
      _ = ENNReal.ofReal (r ^ 5) * V₁ := hs'
      _ = V₁ * (ENNReal.ofReal r) ^ (5 : ℝ) := by
        rw [ENNReal.ofReal_pow hr.le, ← ENNReal.rpow_natCast]
        ac_rfl
  have hrpow : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hrpowtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hd : 0 ≤ 1 / p' - 1 / p := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hp' hpp.le)
  have hfactor : (ENNReal.ofReal r) ^
      (-(5 * (1 - p' / q) / p')) * V ^ (1 / p' - 1 / p) =
      V₁ ^ (1 / p' - 1 / p) *
        (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) := by
    rw [hV, ENNReal.mul_rpow_of_nonneg _ _ hd, ← ENNReal.rpow_mul]
    let d : ℝ := 1 / p' - 1 / p
    have he : -(5 * (1 - p' / q) / p') + 5 * d =
        -(5 * (1 - p / q) / p) := by
      dsimp [d]
      field_simp [hp'.ne', (lt_of_lt_of_le hp' hpp.le).ne']
      ring
    calc
      (ENNReal.ofReal r) ^ (-(5 * (1 - p' / q) / p')) *
          (V₁ ^ d * (ENNReal.ofReal r) ^ (5 * d)) =
          V₁ ^ d * ((ENNReal.ofReal r) ^
            (-(5 * (1 - p' / q) / p')) *
            (ENNReal.ofReal r) ^ (5 * d)) := by ac_rfl
      _ = V₁ ^ d * (ENNReal.ofReal r) ^
          (-(5 * (1 - p' / q) / p') + 5 * d) := by
        exact congrArg (fun x => V₁ ^ d * x)
          (ENNReal.rpow_add _ _ hrpow hrpowtop).symm
      _ = _ := by rw [he]
  unfold morreyCell
  calc
    (ENNReal.ofReal r) ^ (-(5 * (1 - p' / q) / p')) *
        (cylinderPowerIntegral p' f z r) ^ (1 / p') ≤
      (ENNReal.ofReal r) ^ (-(5 * (1 - p' / q) / p')) *
        ((cylinderPowerIntegral p f z r) ^ (1 / p) *
          V ^ (1 / p' - 1 / p)) := mul_le_mul_right hroot _
    _ = V₁ ^ (1 / p' - 1 / p) *
        ((ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
          (cylinderPowerIntegral p f z r) ^ (1 / p)) := by
      calc
        _ = ((ENNReal.ofReal r) ^ (-(5 * (1 - p' / q) / p')) *
          V ^ (1 / p' - 1 / p)) *
          (cylinderPowerIntegral p f z r) ^ (1 / p) := by ac_rfl
        _ = _ := by rw [hfactor]; ac_rfl
theorem morreyNorm_lower_p {p' p q : ℝ} (hp' : 1 ≤ p') (hpp : p' ≤ p)
    (hpq : p ≤ q) {f : ParabolicPoint → ℝ} (hf : AEMeasurable f volume) :
    morreyNorm p' q f ≤
      (volume (parabolicCylinder 0 0 1)) ^ (1 / p' - 1 / p) *
        morreyNorm p q f := by
  have hp'0 : 0 < p' := lt_of_lt_of_le zero_lt_one hp'
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  rcases hpp.eq_or_lt with rfl | hpp
  · simp only [sub_self, ENNReal.rpow_zero, one_mul]
    exact le_iSup_of_le z
      (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p' q f z s.1) r)
  · exact (morreyCell_lower_p hp'0 hpp hf z r.2).trans
      (mul_le_mul_right (le_iSup_of_le z
        (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell p q f z s.1) r)) _)
end CKN.Foundation.Parabolic.Morrey
