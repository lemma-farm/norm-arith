/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Decay.lean.  Two sections, `GBounds` and `Psi`.
Names and statements here are used by the umbrella Zeta23/Taper.lean (and the Params layer)
and by downstream files.
Canonical text: the paper, §2.2 [subsec:family].  See Zeta23/Taper.lean header for conventions:
generic parameters (ϱ : ℝ → ℝ) (L w : ℝ); paper's side condition is 1 ≤ w ≤ L/8 [eq:wrange];
each lemma carries the minimal hypothesis it needs.
-/
import Mathlib
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.v7e32a7e85554.Zeta23.Taper.Norms
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.v7e32a7e85554.Zeta23.Taper.Strip
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23
namespace Taper
/-! ### [eq:gbounds]: "`(L − 2w − |y|)₊ ≤ g(y) ≤ A_φ(y) ≤ (L − |y|)₊`" -/
section GBounds
variable {ϱ : ℝ → ℝ} {L w : ℝ}
/-! Helpers on the autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] of a real function:
evenness (translation invariance of Lebesgue measure), the interval-overlap length
`|[−M,M] ∩ ([−M,M] − y)| = (2M − |y|)₊`, the two comparison bounds, vanishing for `|y| ≥ 2M`,
and continuity in `y` (parametric integral over the compact support). -/
theorem volume_Icc_inter_shift (M y : ℝ) :
    (volume (Icc (-M) M ∩ Icc (-M - y) (M - y))).toReal = max (2 * M - |y|) 0 := by
  rw [Icc_inter_Icc, Real.volume_Icc, ENNReal.toReal_ofReal']
  congr 1
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith), min_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right (by linarith), min_eq_left (by linarith)]; ring
theorem integrable_indicator_Icc_inter (M y : ℝ) :
    Integrable ((Icc (-M) M ∩ Icc (-M - y) (M - y)).indicator (1 : ℝ → ℝ)) := by
  rw [Icc_inter_Icc]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    ((integrableOn_const_iff).mpr (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)))
/-- Upper comparison: `0 ≤ v ≤ 1` and `v = 0` off `(−M, M)` ⟹ `(v⋆v)(y) ≤ (2M − |y|)₊`. -/
theorem autocorr_le_of_support (v : ℝ → ℝ) {M : ℝ} (h0 : ∀ u, 0 ≤ v u) (h1 : ∀ u, v u ≤ 1)
    (hz : ∀ u, M ≤ |u| → v u = 0) (y : ℝ) :
    Params.autocorr v y ≤ max (2 * M - |y|) 0 := by
  unfold Params.autocorr
  set S := Icc (-M) M ∩ Icc (-M - y) (M - y) with hS
  have hSm : MeasurableSet S := measurableSet_Icc.inter measurableSet_Icc
  have hle : ∀ u, v u * v (u + y) ≤ S.indicator 1 u := by
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu, Pi.one_apply]
      exact mul_le_one₀ (h1 u) (h0 _) (h1 _)
    · rw [indicator_of_notMem hu]
      simp only [hS, mem_inter_iff, mem_Icc, not_and_or, not_le] at hu
      rcases hu with (hu | hu) | (hu | hu)
      · rw [hz u (by linarith [neg_le_abs u]), zero_mul]
      · rw [hz u (by linarith [le_abs_self u]), zero_mul]
      · rw [hz (u + y) (by linarith [neg_le_abs (u + y)]), mul_zero]
      · rw [hz (u + y) (by linarith [le_abs_self (u + y)]), mul_zero]
  calc ∫ u, v u * v (u + y) ≤ ∫ u, S.indicator 1 u :=
        integral_mono_of_nonneg (ae_of_all _ fun u => mul_nonneg (h0 _) (h0 _))
          (integrable_indicator_Icc_inter M y) (ae_of_all _ hle)
    _ = (volume S).toReal := integral_indicator_one hSm
    _ = max (2 * M - |y|) 0 := volume_Icc_inter_shift M y
/-- Lower comparison: `0 ≤ v`, `v = 1` on `[−M, M]`, integrand integrable ⟹ `(2M − |y|)₊ ≤ (v⋆v)(y)`. -/
theorem le_autocorr_of_plateau (v : ℝ → ℝ) {M : ℝ} (h0 : ∀ u, 0 ≤ v u)
    (hp : ∀ u, |u| ≤ M → v u = 1) {y : ℝ} (hint : Integrable fun u => v u * v (u + y)) :
    max (2 * M - |y|) 0 ≤ Params.autocorr v y := by
  unfold Params.autocorr
  set S := Icc (-M) M ∩ Icc (-M - y) (M - y) with hS
  have hSm : MeasurableSet S := measurableSet_Icc.inter measurableSet_Icc
  have hle : ∀ u, S.indicator 1 u ≤ v u * v (u + y) := by
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu, Pi.one_apply]
      simp only [hS, mem_inter_iff, mem_Icc] at hu
      rw [hp u (abs_le.mpr ⟨hu.1.1, hu.1.2⟩), hp (u + y) (abs_le.mpr ⟨by linarith, by linarith⟩),
        mul_one]
    · rw [indicator_of_notMem hu]
      exact mul_nonneg (h0 _) (h0 _)
  calc max (2 * M - |y|) 0 = (volume S).toReal := (volume_Icc_inter_shift M y).symm
    _ = ∫ u, S.indicator 1 u := (integral_indicator_one hSm).symm
    _ ≤ ∫ u, v u * v (u + y) :=
        integral_mono_of_nonneg (ae_of_all _ fun u => Set.indicator_nonneg (fun _ _ => zero_le_one) u)
          hint (ae_of_all _ hle)
theorem phi_sq_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ) (hu : L / 2 ≤ |u|) :
    phi ϱ L w u ^ 2 = 0 := by
  rw [phi_eq_zero hϱ hw hu, zero_pow two_ne_zero]
theorem integrable_phi_mul_shift (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    Integrable fun u => phi ϱ L w u * phi ϱ L w (u + y) := by
  have hc := phi_continuous hϱ hw hwL
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  refine HasCompactSupport.intro (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc fun u hu => ?_
  rw [phi_eq_zero hϱ hw ?_, zero_mul]
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · linarith [neg_le_abs u]
  · linarith [le_abs_self u]
theorem integrable_phi_sq_mul_shift (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    Integrable fun u => phi ϱ L w u ^ 2 * phi ϱ L w (u + y) ^ 2 := by
  have hc := phi_continuous hϱ hw hwL
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  refine HasCompactSupport.intro (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc fun u hu => ?_
  rw [phi_sq_eq_zero hϱ hw u ?_, zero_mul]
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · linarith [neg_le_abs u]
  · linarith [le_abs_self u]
theorem g_ge (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    max (L - 2 * w - |y|) 0 ≤ g ϱ L w y := by
  have h := le_autocorr_of_plateau (fun u => phi ϱ L w u ^ 2) (M := L / 2 - w)
    (fun u => sq_nonneg _) (fun u hu => by rw [phi_eq_one hϱ hw hu, one_pow])
    (integrable_phi_sq_mul_shift hϱ hw hwL y)
  rw [show 2 * (L / 2 - w) = L - 2 * w by ring] at h
  exact h
theorem g_le_Aphi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    g ϱ L w y ≤ Aphi ϱ L w y := by
  unfold g Aphi Params.autocorr
  refine integral_mono_of_nonneg (ae_of_all _ fun u => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (integrable_phi_mul_shift hϱ hw hwL y) (ae_of_all _ fun u => ?_)
  have h0 := phi_nonneg (L := L) (w := w) hϱ
  have h1 := phi_le_one (L := L) (w := w) hϱ
  exact mul_le_mul (pow_le_of_le_one (h0 _) (h1 _) two_ne_zero)
    (pow_le_of_le_one (h0 _) (h1 _) two_ne_zero) (sq_nonneg _) (h0 _)
theorem Aphi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (_hwL : 2 * w ≤ L) (y : ℝ) :
    Aphi ϱ L w y ≤ max (L - |y|) 0 := by
  have h := autocorr_le_of_support (phi ϱ L w) (M := L / 2) (phi_nonneg hϱ) (phi_le_one hϱ)
    (fun u hu => phi_eq_zero hϱ hw hu) y
  rw [show 2 * (L / 2) = L by ring] at h
  exact h
theorem g_nonneg (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    0 ≤ g ϱ L w y :=
  le_trans (le_max_right _ _) (g_ge hϱ hw hwL y)
end GBounds
/-! ### [eq:psidef]: "`max(|φ̂(r)|, |Φ(r)|) ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`"
We give the three bounds separately (division-free) and then the `ψ` form. -/
section Psi 
variable {ϱ : ℝ → ℝ} {L w : ℝ}
/-! #### Helpers: first-order [eq:hfbound], and the ℂ-valued φ² -/
theorem psi_nonneg (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    0 ≤ psi ϱ L w r := by
  have hL : 0 ≤ L := by linarith
  have hc : 0 ≤ cRho ϱ := le_trans (by norm_num) (four_le_cRho hϱ)
  unfold psi
  split_ifs with hr
  · exact hL
  · exact le_min hL (le_min (by positivity) (by positivity))
theorem psi_le_L (_hϱ : TaperProfile ϱ) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r ≤ L := by
  unfold psi
  split_ifs with hr
  · exact le_rfl
  · exact min_le_left _ _
theorem psi_mul_abs_le (_hϱ : TaperProfile ϱ) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r * |r| ≤ 2 := by
  unfold psi
  split_ifs with hr
  · simp [hr]
  · have hra : 0 < |r| := abs_pos.mpr hr
    rw [← le_div_iff₀ hra]
    exact (min_le_right _ _).trans (min_le_left _ _)
theorem psi_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r * r ^ 2 ≤ cRho ϱ / w := by
  have hw0 : 0 < w := by linarith
  have hc : 0 ≤ cRho ϱ := le_trans (by norm_num) (four_le_cRho hϱ)
  unfold psi
  split_ifs with hr
  · simp [hr]; positivity
  · have hr2 : 0 < r ^ 2 := by positivity
    rw [← le_div_iff₀ hr2, div_div, mul_comm]
    exact (min_le_right _ _).trans (min_le_right _ _)
/-! #### Measurability / integrability of ψ -/
theorem psi_abs (r : ℝ) : psi ϱ L w |r| = psi ϱ L w r := by
  unfold psi
  simp only [abs_eq_zero, abs_abs, sq_abs]
theorem psi_measurable : Measurable (psi ϱ L w) := by
  have h1 : Measurable (fun r : ℝ => min L (min (2 / |r|) (cRho ϱ / (w * r ^ 2)))) :=
    measurable_const.min ((measurable_const.div continuous_abs.measurable).min
      (measurable_const.div (measurable_const.mul (measurable_id.pow_const 2))))
  have : psi ϱ L w = Set.piecewise {(0:ℝ)} (fun _ => L) (fun r => min L (min (2 / |r|) (cRho ϱ / (w * r ^ 2)))) := by
    funext r
    unfold psi
    by_cases hr : r = 0
    · rw [if_pos hr, Set.piecewise_eq_of_mem _ _ _ (by simp [hr])]
    · rw [if_neg hr, Set.piecewise_eq_of_notMem _ _ _ (by simp [hr])]
  rw [this]
  exact Measurable.piecewise (measurableSet_singleton 0) measurable_const h1
/-- For r > 0: ψ(r) ≤ (c_ϱ/w) · r^{−2} (rpow form). -/
theorem psi_le_rpow_neg_two (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) {r : ℝ}
    (hr : 0 < r) : psi ϱ L w r ≤ cRho ϱ / w * r ^ (-2:ℝ) := by
  have h := psi_mul_sq_le hϱ hw hwL r
  rw [Real.rpow_neg hr.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h
/-- The common integrable plateau majorant: `a` on [−1,1] and `b·|r|⁻²` outside (ψ: a = L, b = c_ϱ/w;
r²-moments: a = 4, b = C²).  ∫ = 2a + 2b. -/
private noncomputable def plateauMaj (a b : ℝ) (r : ℝ) : ℝ :=
  (Icc (-1:ℝ) 1).indicator (fun _ => a) r
    + b * ((Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) r + (Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) (-r))
private theorem tail_indicator_integrable :
    Integrable ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).integrable_indicator measurableSet_Ioi
private theorem plateauMaj_integrable (a b : ℝ) : Integrable (plateauMaj a b) :=
  ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).add
    ((tail_indicator_integrable.add tail_indicator_integrable.comp_neg).const_mul _)
private noncomputable abbrev psiMaj (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ → ℝ := plateauMaj L (cRho ϱ / w)
private theorem psiMaj_integrable : Integrable (psiMaj ϱ L w) := plateauMaj_integrable _ _
private theorem psi_le_psiMaj (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r ≤ psiMaj ϱ L w r := by
  have hw0 : 0 < w := by linarith
  have hc : 0 ≤ cRho ϱ := le_trans (by norm_num) (four_le_cRho hϱ)
  have hind : ∀ s : ℝ, 0 ≤ (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) s := fun s =>
    Set.indicator_nonneg (fun x hx => Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hx)) _) _
  unfold psiMaj plateauMaj
  by_cases h : r ∈ Icc (-1:ℝ) 1
  · rw [Set.indicator_of_mem h]
    have := psi_le_L hϱ hw hwL r
    nlinarith [hind r, hind (-r), div_nonneg hc hw0.le]
  · rw [Set.indicator_of_notMem h, zero_add]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · -- r < -1
      have hr : 0 < -r := by linarith
      rw [Set.indicator_of_notMem (show r ∉ Ioi (1:ℝ) by simp; linarith),
        Set.indicator_of_mem (show -r ∈ Ioi (1:ℝ) by simp; linarith), zero_add]
      have := psi_le_rpow_neg_two hϱ hw hwL hr
      rw [← psi_abs, abs_of_neg (by linarith)]
      exact this
    · -- 1 < r
      have hr : 0 < r := by linarith
      rw [Set.indicator_of_mem (show r ∈ Ioi (1:ℝ) from h),
        Set.indicator_of_notMem (show -r ∉ Ioi (1:ℝ) by simp; linarith), add_zero]
      exact psi_le_rpow_neg_two hϱ hw hwL hr
private theorem psiints_consts (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    0 < 2 / L ∧ 0 < cRho ϱ / (2 * w) ∧ 2 / L ≤ cRho ϱ / (2 * w) ∧
    (cRho ϱ / (2 * w)) / (2 / L) = cRho ϱ * L / (4 * w) := by
  have hc := four_le_cRho hϱ
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ hL (by positivity)]; nlinarith
  · field_simp; ring
/-- On (0, ∞), ψ is dominated by the three-piece majorant L·1_{(0,A]} + (2/r)·1_{(A,B]} +
(c_ϱ/w) r⁻²·1_{(B,∞)} (in fact with equality; ≤ is all we use). -/
private theorem indicator_psi_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) (r : ℝ) :
    (Ioi (0:ℝ)).indicator (psi ϱ L w) r
      ≤ (Ioc 0 (2 / L)).indicator (fun _ => L) r
        + (Ioc (2 / L) (cRho ϱ / (2 * w))).indicator (fun x => 2 * x⁻¹) r
        + (Ioi (cRho ϱ / (2 * w))).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := by
  obtain ⟨hA, hB, hAB, -⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  by_cases hr : r ∈ Ioi (0:ℝ)
  · have hr0 : 0 < r := hr
    rw [indicator_of_mem hr]
    by_cases h1 : r ≤ 2 / L
    · rw [indicator_of_mem (show r ∈ Ioc 0 (2 / L) from ⟨hr0, h1⟩),
        indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
          fun h => not_lt.mpr h1 h.1),
        indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from
          fun h => not_lt.mpr (h1.trans hAB) h), add_zero, add_zero]
      exact psi_le_L hϱ hw hwL' r
    · rw [not_le] at h1
      by_cases h2 : r ≤ cRho ϱ / (2 * w)
      · rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => not_le.mpr h1 h.2),
          indicator_of_mem (show r ∈ Ioc (2 / L) (cRho ϱ / (2 * w)) from ⟨h1, h2⟩),
          indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from fun h => not_lt.mpr h2 h),
          zero_add, add_zero]
        have := psi_mul_abs_le hϱ hw hwL' r
        rw [abs_of_pos hr0] at this
        rw [← div_eq_mul_inv, le_div_iff₀ hr0]
        exact this
      · rw [not_le] at h2
        rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => not_le.mpr h1 h.2),
          indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
            fun h => not_le.mpr h2 h.2),
          indicator_of_mem (show r ∈ Ioi (cRho ϱ / (2 * w)) from h2), zero_add, zero_add]
        exact psi_le_rpow_neg_two hϱ hw hwL' hr0
  · rw [indicator_of_notMem hr]
    have hr0 : r ≤ 0 := not_lt.mp hr
    rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => hr h.1),
      indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
        fun h => hr (lt_trans hA h.1)),
      indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from fun h => hr (lt_trans hB h)),
      add_zero, add_zero]
/-- [eq:psiints]: Ψ₀ := ∫₀^∞ ψ(r) dr ≤ 4 + 2 log(c_ϱ L/(4w)) (paper: "="). -/
theorem integral_psi_Ioi_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r in Ioi 0, psi ϱ L w r ≤ 4 + 2 * Real.log (cRho ϱ * L / (4 * w)) := by
  obtain ⟨hA, hB, hAB, hBA⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  have hc0 : 0 < cRho ϱ := lt_of_lt_of_le (by norm_num) (four_le_cRho hϱ)
  set A := 2 / L with hAdef
  set B := cRho ϱ / (2 * w) with hBdef
  -- integrability of the three pieces
  have i1 : IntegrableOn (fun _ : ℝ => L) (Ioc 0 A) := integrableOn_const (by simp)
  have i2 : IntegrableOn (fun x : ℝ => 2 * x⁻¹) (Ioc A B) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.mul
      ((continuousOn_inv₀).mono fun x hx => ne_of_gt (lt_of_lt_of_le hA hx.1))
  have i3 : IntegrableOn (fun x : ℝ => cRho ϱ / w * x ^ (-2:ℝ)) (Ioi B) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hB).const_mul _
  have I1 := i1.integrable_indicator measurableSet_Ioc
  have I2 := i2.integrable_indicator measurableSet_Ioc
  have I3 := i3.integrable_indicator measurableSet_Ioi
  -- the three integrals
  have e1 : ∫ r, (Ioc 0 A).indicator (fun _ => L) r = 2 := by
    rw [integral_indicator measurableSet_Ioc, setIntegral_const, measureReal_def,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, sub_zero, hAdef]
    field_simp
  have e2 : ∫ r, (Ioc A B).indicator (fun x => 2 * x⁻¹) r = 2 * Real.log (B / A) := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hAB,
      intervalIntegral.integral_const_mul, integral_inv]
    exact fun h => by
      have := (Set.mem_uIcc.mp h); rcases this with h | h <;> linarith [h.1, h.2]
  have e3 : ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r = 2 := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hB]
    norm_num
    rw [Real.rpow_neg_one, hBdef]
    field_simp
  have I12 : Integrable (fun r => (Ioc 0 A).indicator (fun _ => L) r
      + (Ioc A B).indicator (fun x => 2 * x⁻¹) r) := I1.add I2
  calc ∫ r in Ioi 0, psi ϱ L w r
      = ∫ r, (Ioi (0:ℝ)).indicator (psi ϱ L w) r := (integral_indicator measurableSet_Ioi).symm
    _ ≤ ∫ r, ((Ioc 0 A).indicator (fun _ => L) r
          + (Ioc A B).indicator (fun x => 2 * x⁻¹) r
          + (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => ?_) ((I1.add I2).add I3)
          (Eventually.of_forall fun r => indicator_psi_le hϱ hw hwL r)
        exact Set.indicator_nonneg (fun x _ => psi_nonneg hϱ hw hwL' x) _
    _ = (∫ r, ((Ioc 0 A).indicator (fun _ => L) r + (Ioc A B).indicator (fun x => 2 * x⁻¹) r))
          + ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := integral_add I12 I3
    _ = ((∫ r, (Ioc 0 A).indicator (fun _ => L) r) + ∫ r, (Ioc A B).indicator (fun x => 2 * x⁻¹) r)
          + ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := by
        rw [integral_add I1 I2]
    _ = 2 + 2 * Real.log (B / A) + 2 := by rw [e1, e2, e3]
    _ = 4 + 2 * Real.log (cRho ϱ * L / (4 * w)) := by rw [hBA]; ring
theorem integral_psi_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, psi ϱ L w r ^ 2 ≤ 8 * L := by
  obtain ⟨hA, -, -, -⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  set A := 2 / L with hAdef
  have hred : ∫ r, psi ϱ L w r ^ 2 = 2 * ∫ r in Ioi 0, psi ϱ L w r ^ 2 := by
    have h := integral_comp_abs (f := fun x => psi ϱ L w x ^ 2)
    simp only [psi_abs] at h
    exact h
  rw [hred]
  have i1 : IntegrableOn (fun _ : ℝ => L ^ 2) (Ioc 0 A) := integrableOn_const (by simp)
  have i2 : IntegrableOn (fun x : ℝ => 4 * x ^ (-2:ℝ)) (Ioi A) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hA).const_mul _
  have I1 := i1.integrable_indicator measurableSet_Ioc
  have I2 := i2.integrable_indicator measurableSet_Ioi
  have I12 : Integrable (fun r => (Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r
      + (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r) := I1.add I2
  have hpt : ∀ r, (Ioi (0:ℝ)).indicator (fun x => psi ϱ L w x ^ 2) r
      ≤ (Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r + (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r := by
    intro r
    have h0 := psi_nonneg hϱ hw hwL' r
    by_cases hr : 0 < r
    · rw [indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr)]
      by_cases h1 : r ≤ A
      · rw [indicator_of_mem (show r ∈ Ioc 0 A from ⟨hr, h1⟩),
          indicator_of_notMem (show r ∉ Ioi A from fun h => not_lt.mpr h1 h), add_zero]
        exact pow_le_pow_left₀ h0 (psi_le_L hϱ hw hwL' r) 2
      · have h1' : A < r := not_le.mp h1
        rw [indicator_of_notMem (show r ∉ Ioc 0 A from fun h => h1 h.2),
          indicator_of_mem (show r ∈ Ioi A from h1'), zero_add]
        have h := psi_mul_abs_le hϱ hw hwL' r
        rw [abs_of_pos hr] at h
        have h2 : psi ϱ L w r ≤ 2 * r⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hr]; exact h
        calc psi ϱ L w r ^ 2 ≤ (2 * r⁻¹) ^ 2 := pow_le_pow_left₀ h0 h2 2
          _ = 4 * r ^ (-2:ℝ) := by
              rw [Real.rpow_neg hr.le, Real.rpow_two]; ring
    · rw [indicator_of_notMem (show r ∉ Ioi (0:ℝ) from hr),
        indicator_of_notMem (show r ∉ Ioc 0 A from fun h => hr h.1),
        indicator_of_notMem (show r ∉ Ioi A from fun h => hr (lt_trans hA h)), add_zero]
  have e1 : ∫ r, (Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r = 2 * L := by
    rw [integral_indicator measurableSet_Ioc, setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, sub_zero, hAdef]
    field_simp
  have e2 : ∫ r, (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r = 2 * L := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hA]
    norm_num
    rw [Real.rpow_neg_one, hAdef]
    field_simp
    ring
  calc 2 * ∫ r in Ioi 0, psi ϱ L w r ^ 2
      = 2 * ∫ r, (Ioi (0:ℝ)).indicator (fun x => psi ϱ L w x ^ 2) r := by
        rw [integral_indicator measurableSet_Ioi]
    _ ≤ 2 * ∫ r, ((Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r
          + (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r) :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (Eventually.of_forall fun r => Set.indicator_nonneg (fun x _ => sq_nonneg _) _) I12
          (Eventually.of_forall hpt)) (by norm_num)
    _ = 2 * (2 * L + 2 * L) := by rw [integral_add I1 I2, e1, e2]
    _ = 8 * L := by ring
theorem psi_integrable (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (psi ϱ L w) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine (psiMaj_integrable (ϱ := ϱ) (L := L) (w := w)).mono'
    psi_measurable.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_of_nonneg (psi_nonneg hϱ hw hwL' r)]
  exact psi_le_psiMaj hϱ hw hwL' r
theorem psi_sq_integrable (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun r => psi ϱ L w r ^ 2) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine ((psi_integrable hϱ hw hwL).const_mul L).mono'
    (psi_measurable.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  have h0 := psi_nonneg hϱ hw hwL' r
  have h1 := psi_le_L hϱ hw hwL' r
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith
end Psi
end Taper
end Zeta23
