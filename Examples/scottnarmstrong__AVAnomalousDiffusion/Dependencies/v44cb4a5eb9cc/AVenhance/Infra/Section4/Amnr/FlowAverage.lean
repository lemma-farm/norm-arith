-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.Cutoff
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.Seed
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Differentiation and estimates for the actual locally finite cutoff-flow sum. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
theorem amnrWord_mul_abs_le_at {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f g : AmnrSpace → ℝ} {N : ℕ}
    (hb : ContDiffOn ℝ N b U) (hf : ContDiffOn ℝ N f U)
    (hg : ContDiffOn ℝ N g U) {S H F G : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hF : 0 ≤ F) (_hG : 0 ≤ G)
    (w : List (Option (Fin 2))) (hw : amnrBudget w ≤ N)
    {z : AmnrSpace} (hz : z ∈ U)
    (hfb : ∀ v, v.Sublist w →
      |amnrWord b v f z| ≤ F * amnrWeight S H v)
    (hgb : ∀ v, v.Sublist w →
      |amnrWord b v g z| ≤ G * amnrWeight S H v) :
    |amnrWord b w (f * g) z| ≤ (2 : ℝ) ^ w.length * F * G * amnrWeight S H w := by
  rw [amnrWord_mul hU hb hf hg w ((amnrBudget_length_le w).trans hw) hz]
  let L := (amnrSplits w).map (fun q => amnrWord b q.1 f z * amnrWord b q.2 g z)
  change |L.sum| ≤ _
  have hterm (q) (hq : q ∈ amnrSplits w) :
      |amnrWord b q.1 f z * amnrWord b q.2 g z| ≤ F * G * amnrWeight S H w := by
    have hs := amnrSplits_sublist w q hq
    rw [abs_mul]
    have hh := mul_le_mul (hfb q.1 hs.1) (hgb q.2 hs.2.1)
      (abs_nonneg _) (mul_nonneg hF (amnrWeight_nonneg hS hH q.1))
    refine hh.trans_eq ?_
    rw [mul_mul_mul_comm, amnrWeight_split S H w q hq]
  have hsum : (L.map abs).sum ≤
      ((amnrSplits w).map (fun _ => F * G * amnrWeight S H w)).sum := by
    simp only [L, List.map_map]
    exact List.sum_le_sum hterm
  refine (amnr_abs_list_sum_le L).trans (hsum.trans_eq ?_)
  simp only [List.map_const', List.sum_replicate, amnrSplits_length, nsmul_eq_mul]
  push_cast
  ring
end AVenhance.Infra.Section4
