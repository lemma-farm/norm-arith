-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Core.HeatPotential.HeatFarStripBound
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplitData
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Parabolic.BallDisplays
set_option autoImplicit false
set_option warningAsError true
/-!
# Geometry of a far shell and the mass of its source

Fix a base point `z`, a radius `r > 0` and a shell index `j ≥ 6`, and write
`R = 2 ^ j r` for the inner radius of the shell
`multiplierHeatShellSet z r j`.  Two facts about that shell are used by every
far estimate.

* **Separation.**  An observation point `q` in the closed ball of radius `r`
  around `z` is separated from every shell point `v` whose time lies below
  `q.2`: the parabolic gauge
  `max ‖q.1 - v.1‖ √(q.2 - v.2)` is at least `R / 2`.  The shell is at
  parabolic distance at least `R` from `z` while `q` is at distance at most
  `r ≤ R / 64`, so the excess `R - r` survives in whichever of the two
  coordinates carries the shell separation.  When the shell separates in time
  and the shell point lies *after* `z`, no such `q` exists at all, which is
  why the causal restriction `q.2 ≥ v.2` is part of the statement.

* **Mass.**  The shell sits inside a parabolic cylinder of radius `4 R`, so
  the Morrey seminorm of the source controls its absolute mass by
  `R ^ (5 - 5/θ)` and the source is integrable there.

Both statements fix their constants before the source and before the shell
data.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Foundation.Euclidean CKN.Foundation.Heat
theorem farShellAssembly_shell_subset_ball (z : ParabolicPoint) (r : ℝ) (j : ℕ) :
    multiplierHeatShellSet z r j ⊆ Metric.ball z (2 * ((2 : ℝ) ^ j * r)) := by
  intro v hv
  have h := hv.1
  rwa [show (2 : ℝ) ^ (j + 1) * r = 2 * ((2 : ℝ) ^ j * r) by rw [pow_succ]; ring] at h
/-- **Source mass on a far shell.**  One constant, fixed before the source and
before the shell data, bounds the absolute mass of a finite-Morrey source on
the shell of inner radius `2 ^ j r` by `(2 ^ j r) ^ (5 - 5/θ)` times its
Morrey seminorm, and the source is integrable there. -/
theorem farShellAssembly_exists_shell_mass_bound {P θ : ℝ} (hP : 1 ≤ P)
    (hPθ : P ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {G : ParabolicPoint → ℝ}, AEMeasurable G volume → morreyNorm P θ G < ∞ →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r →
          IntegrableOn G (multiplierHeatShellSet z r j) volume ∧
          (∫ v in multiplierHeatShellSet z r j, |G v|) ≤
            C * ((2 : ℝ) ^ j * r) ^ (5 - 5 / θ) *
              (morreyNorm P θ G).toReal := by
  obtain ⟨C, hC, hB⟩ := exists_stripAbsIntegral_bound hP hPθ
  have hθpos : (0 : ℝ) < θ := lt_of_lt_of_le zero_lt_one (hP.trans hPθ)
  refine ⟨1024 * C, by positivity, ?_⟩
  intro G hG hGM z r j hr
  set R : ℝ := (2 : ℝ) ^ j * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hincl : multiplierHeatShellSet z r j ⊆
      parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R) := by
    rw [parabolicStrip_self]
    intro v hv
    have hball := farShellAssembly_shell_subset_ball z r j hv
    have hcyl := metricBall_subset_parabolicCylinder_doubled z
      (r := 2 * R) (by positivity) hball
    rwa [show 2 * (2 * R) = 4 * R by ring] at hcyl
  obtain ⟨hint, hbd⟩ := hB hG hGM z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R)
    (by positivity) le_rfl
  refine ⟨hint.mono_set hincl, ?_⟩
  have habs : IntegrableOn (fun v => |G v|)
      (parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R)) volume := hint.abs
  have hmono : (∫ v in multiplierHeatShellSet z r j, |G v|) ≤
      ∫ v in parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R), |G v| := by
    refine setIntegral_mono_set habs ?_ (Filter.Eventually.of_forall hincl)
    exact Filter.Eventually.of_forall fun v => abs_nonneg _
  refine hmono.trans (hbd.trans ?_)
  have hMnn : (0 : ℝ) ≤ (morreyNorm P θ G).toReal := ENNReal.toReal_nonneg
  refine mul_le_mul_of_nonneg_right ?_ hMnn
  have h4 : (4 * R) ^ (2 - 5 / θ : ℝ) ≤ 16 * R ^ (2 - 5 / θ : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hRpos.le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hRpos.le _)
    have hle : (4 : ℝ) ^ (2 - 5 / θ : ℝ) ≤ (4 : ℝ) ^ (2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (0 : ℝ) ≤ 5 / θ := by positivity
      linarith only [this]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hle
    norm_num at hle
    exact hle
  have hcube : (4 * R) ^ 3 = 64 * R ^ 3 := by ring
  have hsplit : R ^ 3 * R ^ (2 - 5 / θ : ℝ) = R ^ (5 - 5 / θ : ℝ) := by
    rw [show (R : ℝ) ^ 3 = R ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_add hRpos]
    congr 1
    push_cast
    ring
  have hrnn : (0 : ℝ) ≤ R ^ (2 - 5 / θ : ℝ) := Real.rpow_nonneg hRpos.le _
  calc C * (4 * R) ^ 3 * (4 * R) ^ (2 - 5 / θ : ℝ)
      = (C * (64 * R ^ 3)) * (4 * R) ^ (2 - 5 / θ : ℝ) := by rw [hcube]
    _ ≤ (C * (64 * R ^ 3)) * (16 * R ^ (2 - 5 / θ : ℝ)) := by
        refine mul_le_mul_of_nonneg_left h4 ?_
        have : (0 : ℝ) ≤ R ^ 3 := by positivity
        positivity
    _ = 1024 * C * (R ^ 3 * R ^ (2 - 5 / θ : ℝ)) := by ring
    _ = 1024 * C * R ^ (5 - 5 / θ : ℝ) := by rw [hsplit]
end CKN.Core.HeatPotential
