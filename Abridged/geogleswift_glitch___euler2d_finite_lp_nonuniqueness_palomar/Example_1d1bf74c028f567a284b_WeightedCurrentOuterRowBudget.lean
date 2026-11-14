module

public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.vf15e846202ba.RequestProject.Euler.BanachWeightedTrajectoryEnvelope ====
public section
/-! Weighted norms of already existing trajectories obey an actual
integral inequality directly from their derivatives and the original
self-field Lipschitz bound. No new trajectory or linear propagator
is assumed or constructed. -/
@[expose] public section
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal
namespace Euler2D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def weightedFamilyDifference (h : ℝ) (k : ℕ) (x : ℕ → E) : Fin k → E :=
  fun j => (h ^ (k - (j : ℕ)))⁻¹ • x j
def weightedFamilyNorm (h : ℝ) (k : ℕ) (x : ℕ → E) : ℝ :=
  ‖weightedFamilyDifference h k x‖

end Euler2D
end

end
end

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_1d1bf74c028f567a284b_WeightedCurrentOuterRowBudget ====
/-! The current target is outside the ancestor maximum. Its complete
outer row is still O(rho^8), uniformly in the prefix length. It can be
absorbed into a fixed rho^6 polynomial forcing margin by choosing rho
after the weighted bound and all row constants. -/
@[expose] public section
set_option maxHeartbeats 3500000
noncomputable section
open Set
open scoped BigOperators NNReal
namespace Euler2D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option linter.unusedVariables false in
theorem weighted_current_outer_row_sum_bound {b C₀ ρ : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hC₀ : 0 < C₀) (hρ : 0 < ρ)
    (hζ : C₀ * ρ ^ 8 < 1) (k : ℕ) (x : ℕ → E) 
    (h_Euler2D_rho_pow_down : ∀ (C₀ ρ : ℝ) (a c : ℕ), ρ ^ (2 * c) * (C₀ * ρ ^ 6) ^ (a + c) = (C₀ * ρ ^ 6) ^ a * (C₀ * ρ ^ 8) ^ c)
    (h_Euler2D_sum_pow_le_of_injOn : ∀ {ι : Type} (s : Finset ι) (φ : ι → ℕ),
      Set.InjOn φ (↑s : Set ι) →
        (∀ i ∈ s, 1 ≤ φ i) → ∀ {q : ℝ}, 0 ≤ q → q < 1 → ∑ i ∈ s, q ^ φ i ≤ q / (1 - q))
    (h_Euler2D_norm_le_weightedFamilyNorm : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {h : ℝ},
      0 < h →
        ∀ (k : ℕ) (x : ℕ → E) (j : Fin k),
          ‖x (↑j : ℕ)‖ ≤ h ^ (k - (↑j : ℕ)) * Euler2D.weightedFamilyNorm h k x)
    :
    (∑ l : Fin k, b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖) ≤
      b * weightedFamilyNorm (C₀ * ρ ^ 6) k x * ((C₀ * ρ ^ 8) / (1 - C₀ * ρ ^ 8)) := by
  let h := C₀ * ρ ^ 6
  let Z := weightedFamilyNorm h k x
  let ζ := C₀ * ρ ^ 8
  have hh : 0 < h := by dsimp [h]; positivity
  have hZ : 0 ≤ Z := norm_nonneg _
  have hζ0 : 0 ≤ ζ := by dsimp [ζ]; positivity
  have hterm (l : Fin k) :
      b ^ (k - (l : ℕ)) * ρ ^ (2 * (k - (l : ℕ))) * ‖x l‖ ≤
        (b * Z) * ζ ^ (k - (l : ℕ)) := by
    have hn := h_Euler2D_norm_le_weightedFamilyNorm hh k x l
    have hbpow : b ^ (k - (l : ℕ)) ≤ b := by
      simpa only [pow_one] using pow_le_pow_of_le_one hb.le hb1 (show 1 ≤ k - (l : ℕ) by omega)
    have hid := h_Euler2D_rho_pow_down C₀ ρ 0 (k - (l : ℕ))
    simp only [zero_add, pow_zero, one_mul] at hid
    calc
      _ ≤ (b * ρ ^ (2 * (k - (l : ℕ)))) * (h ^ (k - (l : ℕ)) * Z) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hbpow (by positivity)) hn (norm_nonneg _) (by positivity)
      _ = b * Z * (ρ ^ (2 * (k - (l : ℕ))) * (C₀ * ρ ^ 6) ^ (k - (l : ℕ))) := by dsimp [h]; ring
      _ = _ := by rw [hid]
  have hgeo := h_Euler2D_sum_pow_le_of_injOn (Finset.univ : Finset (Fin k)) (fun l => k - (l : ℕ))
    (fun a _ b' _ hab => by
      change k - (a : ℕ) = k - (b' : ℕ) at hab
      exact Fin.ext (by have ha := a.isLt; have hb' := b'.isLt; omega))
    (fun l _ => by have hl := l.isLt; change 1 ≤ k - (l : ℕ); omega) hζ0 hζ
  calc
    _ ≤ ∑ l : Fin k, (b * Z) * ζ ^ (k - (l : ℕ)) :=
      Finset.sum_le_sum (fun l _ => hterm l)
    _ = (b * Z) * ∑ l : Fin k, ζ ^ (k - (l : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ (b * Z) * (ζ / (1 - ζ)) := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = _ := rfl
end Euler2D
end
