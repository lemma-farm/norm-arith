/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
module
public import Examples.jvanwinden__PlanarFrontStability.Dependencies.vedea67ee6f55.Planarwave.Analysis.HolomorphicTimeExtension
@[expose] public section
/-! # Geometry and uniqueness for complex time sectors -/
open Filter Set Topology
namespace Planarwave
noncomputable section
/-- An open sector about the positive real axis, described without choosing arguments. -/
def complexTimeSector (η : ℝ) : Set ℂ := {z | 0 < z.re ∧ |z.im| < η * z.re}
theorem div_real_mem_complexTimeSector {η r : ℝ} {z : ℂ}
    (hz : z ∈ complexTimeSector η) (hr : 0 < r) :
    z / (r : ℂ) ∈ complexTimeSector η := by
  simp only [complexTimeSector, mem_ofPred_eq, Complex.div_ofReal_re, Complex.div_ofReal_im]
  refine ⟨div_pos hz.1 hr, ?_⟩
  rw [abs_div, abs_of_pos hr, ← mul_div_assoc]
  exact div_lt_div_of_pos_right hz.2 hr
theorem mem_positiveTimeNeighborhood_of_sector {η : ℝ} {z : ℂ}
    (hz : z ∈ complexTimeSector η) (hz₁ : z.re ≤ 1) :
    z ∈ positiveTimeNeighborhood η :=
  mem_positiveTimeNeighborhood_of_im_lt hz.1 (by simpa only [min_eq_left hz₁] using hz.2)
end
end Planarwave
