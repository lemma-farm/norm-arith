module

public import Mathlib

-- ==== Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Examples.Example_4b6a970711a121b3dcc1_PolarRep ====
/-!
# Polar coordinates on `ℝ²` and a Cauchy–Pompeiu type representation

Auxiliary analysis for the two-dimensional interpolation inequality (Lemma 6.1).
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
noncomputable section
namespace AnomDiss


set_option linter.unusedVariables false in
/-- Hölder's inequality in polar coordinates with the radial weight `r`, for a continuous
function supported in the annulus `r₀ < r < ρ`. -/
lemma polar_holder {p q : ℝ} (hpq : p.HolderConjugate q) (Φ : ℝ × ℝ → ℝ) (hΦc : Continuous Φ)
    (hΦ0 : ∀ x, 0 ≤ Φ x) {r₀ ρ : ℝ} (hr₀ : 0 ≤ r₀) (hρ : r₀ < ρ)
    (hsupp : ∀ r θ, 0 < r → (r ≤ r₀ ∨ ρ ≤ r) → Φ (r, θ) = 0)
    (hw : IntegrableOn (fun r : ℝ => r ^ (-(q / p))) (Ioo r₀ ρ)) 
    (h_AnomDiss_volume_polar_box_ne_top : ∀ (r₀ ρ : ℝ),
      (MeasureTheory.MeasureSpace.volume : Set (ℝ × ℝ) → ENNReal)
          (Set.Ioo r₀ ρ ×ˢ Set.Ioo (-Real.pi) Real.pi) ≠
        ⊤)
    (h_AnomDiss_integrableOn_target_of_radius : ∀ {E : Type} [inst : NormedAddCommGroup E] (F : ℝ × ℝ → E),
      Continuous F →
        ∀ (R : ℝ),
          (∀ (r θ : ℝ), R ≤ r → F (r, θ) = 0) →
            MeasureTheory.IntegrableOn F polarCoord.target MeasureTheory.MeasureSpace.volume)
    :
    ∫ x in polarCoord.target, Φ x ≤
      (∫ x in polarCoord.target, x.1 * Φ x ^ p) ^ (1 / p) *
        (2 * π * ∫ r in Ioo r₀ ρ, r ^ (-(q / p))) ^ (1 / q) := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set S : Set (ℝ × ℝ) := Ioo r₀ ρ ×ˢ Ioo (-π) π with hS
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hST : S ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono (fun r hr => lt_of_le_of_lt hr₀ hr.1) le_rfl
  haveI : IsFiniteMeasure (volume.restrict S) :=
    isFiniteMeasure_restrict.2 (h_AnomDiss_volume_polar_box_ne_top r₀ ρ)
  have hpos : ∀ x ∈ S, 0 < x.1 := fun x hx => lt_of_le_of_lt hr₀ hx.1.1
  -- step 1: restrict to the box
  have e1 : ∫ x in polarCoord.target, Φ x = ∫ x in S, Φ x := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      polarCoord.open_target.measurableSet hST fun x hx => ?_
    obtain ⟨hxT, hxS⟩ := hx
    rw [polarCoord_target] at hxT
    refine hsupp x.1 x.2 hxT.1 ?_
    by_contra hcon
    push_neg at hcon
    exact hxS ⟨⟨hcon.1, hcon.2⟩, hxT.2⟩
  -- step 2: factor
  set F : ℝ × ℝ → ℝ := fun x => x.1 ^ (1 / p) * Φ x with hF
  set G : ℝ × ℝ → ℝ := fun x => x.1 ^ (-(1 / p)) with hG
  have e2 : ∫ x in S, Φ x = ∫ x in S, F x * G x := by
    refine setIntegral_congr_fun hSm fun x hx => ?_
    simp only [hF, hG]
    rw [mul_comm (x.1 ^ (1 / p)), mul_assoc, ← Real.rpow_add (hpos x hx), add_neg_cancel,
      Real.rpow_zero, mul_one]
  have hFc : Continuous F := (( Real.continuous_rpow_const (by positivity)).comp
    continuous_fst).mul hΦc
  have hGm : Measurable G := by simp only [hG]; fun_prop
  have hF0 : 0 ≤ᵐ[volume.restrict S] F := ae_restrict_of_forall_mem hSm fun x hx =>
    mul_nonneg (Real.rpow_nonneg (hpos x hx).le _) (hΦ0 x)
  have hG0 : 0 ≤ᵐ[volume.restrict S] G := ae_restrict_of_forall_mem hSm fun x hx =>
    Real.rpow_nonneg (hpos x hx).le _
  have hFL : MemLp F (ENNReal.ofReal p) (volume.restrict S) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (s := Icc r₀ ρ ×ˢ Icc (-π) π) hFc.continuousOn
    refine MemLp.of_bound hFc.aestronglyMeasurable C (ae_restrict_of_forall_mem hSm fun x hx => ?_)
    exact hC x (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hx)
  have hrestr : volume.restrict S =
      (volume.restrict (Ioo r₀ ρ)).prod (volume.restrict (Ioo (-π) π)) := by
    rw [hS, Measure.volume_eq_prod, Measure.prod_restrict]
  have hwI : Integrable (fun x : ℝ × ℝ => x.1 ^ (-(q / p)) * (1 : ℝ)) (volume.restrict S) := by
    rw [hrestr]
    haveI : IsFiniteMeasure (volume.restrict (Ioo (-π) π)) :=
      isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
    exact Integrable.mul_prod (f := fun r : ℝ => r ^ (-(q / p))) (g := fun _ : ℝ => (1 : ℝ))
      hw (integrable_const 1)
  have hGq : ∀ x ∈ S, ‖G x‖ ^ q = x.1 ^ (-(q / p)) * 1 := by
    intro x hx
    simp only [hG, mul_one]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hpos x hx).le _), ← Real.rpow_mul (hpos x hx).le]
    congr 1; ring
  have hGL : MemLp G (ENNReal.ofReal q) (volume.restrict S) := by
    rw [← integrable_norm_rpow_iff hGm.aestronglyMeasurable (by simpa using hq0)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]
    exact hwI.congr (ae_restrict_of_forall_mem hSm fun x hx => (hGq x hx).symm)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hF0 hG0 hFL hGL
  have hGq' : ∀ x ∈ S, G x ^ q = x.1 ^ (-(q / p)) * 1 := fun x hx => by
    rw [← hGq x hx, Real.norm_of_nonneg (Real.rpow_nonneg (hpos x hx).le _)]
  have hn1 : 0 ≤ (∫ x in S, G x ^ q) ^ (1 / q) :=
    Real.rpow_nonneg (integral_nonneg_of_ae (hG0.mono fun x hx => Real.rpow_nonneg hx q)) _
  have hn2 : 0 ≤ (∫ x in polarCoord.target, x.1 * Φ x ^ p) ^ (1 / p) := by
    refine Real.rpow_nonneg (setIntegral_nonneg polarCoord.open_target.measurableSet
      fun x hx => ?_) _
    rw [polarCoord_target] at hx
    exact mul_nonneg hx.1.le (Real.rpow_nonneg (hΦ0 x) _)
  rw [e1, e2]
  refine hH.trans (mul_le_mul ?_ (le_of_eq ?_) hn1 hn2)
  · -- first factor
    refine Real.rpow_le_rpow (integral_nonneg_of_ae (hF0.mono fun x hx => by
      simpa using Real.rpow_nonneg hx p)) ?_ (by positivity)
    have e3 : ∫ x in S, F x ^ p = ∫ x in S, x.1 * Φ x ^ p := by
      refine setIntegral_congr_fun hSm fun x hx => ?_
      simp only [hF]
      rw [Real.mul_rpow (Real.rpow_nonneg (hpos x hx).le _) (hΦ0 x), ← Real.rpow_mul
        (hpos x hx).le, one_div_mul_cancel hp0.ne', Real.rpow_one]
    rw [e3]
    have hcont : Continuous fun x : ℝ × ℝ => x.1 * Φ x ^ p :=
      continuous_fst.mul ((Real.continuous_rpow_const hp0.le).comp hΦc)
    refine setIntegral_mono_set (h_AnomDiss_integrableOn_target_of_radius _ hcont ρ ?_) ?_
      (Eventually.of_forall hST)
    · intro r θ hr
      by_cases h0 : 0 < r
      · simp [hsupp r θ h0 (Or.inr hr), Real.zero_rpow hp0.ne']
      · exfalso; linarith
    · refine ae_restrict_of_forall_mem polarCoord.open_target.measurableSet fun x hx => ?_
      rw [polarCoord_target] at hx
      exact mul_nonneg hx.1.le (Real.rpow_nonneg (hΦ0 x) _)
  · -- second factor
    congr 1
    rw [setIntegral_congr_fun hSm (fun x hx => hGq' x hx), hrestr]
    rw [integral_prod_mul (fun r : ℝ => r ^ (-(q / p))) (fun _ : ℝ => (1 : ℝ))]
    simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
      Real.volume_real_Ioo_of_le (show -π ≤ π by linarith [Real.pi_pos])]
    ring
end AnomDiss
