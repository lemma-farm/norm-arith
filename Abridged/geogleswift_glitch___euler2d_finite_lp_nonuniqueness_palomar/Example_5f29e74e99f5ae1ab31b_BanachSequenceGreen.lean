module

public import Mathlib

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_5f29e74e99f5ae1ab31b_BanachSequenceGreen ====
/-! Actual bounded sequence Green operators for backward orbits.
The stable future convolution is summed in operator norm, using a true
power bound strictly below the chosen sequence weight. -/
@[expose] public section
noncomputable section
open Set Filter Topology
open scoped BoundedContinuousFunction
namespace Euler2D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def natSequenceShiftCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.compContinuous ⟨fun n => n + k, continuous_of_discreteTopology⟩
      map_add' := fun f g => by ext n; rfl
      map_smul' := fun a f => by ext n; rfl }
    1 (fun f => by
      change ‖f.compContinuous ⟨fun n => n + k, continuous_of_discreteTopology⟩‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using
        BoundedContinuousFunction.norm_compContinuous_le f
          ⟨fun n => n + k, continuous_of_discreteTopology⟩)

def stableSequenceGreenTermCLM (ρ : ℝ) (A : E →L[ℝ] E) (k : ℕ) :
    (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  (ρ⁻¹) ^ (k + 1) • ((A ^ k).compLeftContinuousBounded ℕ).comp (natSequenceShiftCLM E (k + 1))

variable [CompleteSpace E]

def stableSequenceGreenCLM (ρ : ℝ) (A : E →L[ℝ] E) :
    (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) := ∑' k : ℕ, stableSequenceGreenTermCLM ρ A k
set_option linter.unusedVariables false in
theorem norm_stableSequenceGreenCLM_le {ρ β C : ℝ}
    (hρ : 0 < ρ) (hβ0 : 0 ≤ β) (hβρ : β < ρ) (A : E →L[ℝ] E)
    (hA : ∀ k : ℕ, ‖A ^ k‖ ≤ C * β ^ k) 
    (h_Euler2D_norm_stableSequenceGreenTermCLM_le_geometric : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {ρ β C : ℝ},
      0 < ρ →
        ∀ (A : E →L[ℝ] E),
          (∀ (k : ℕ), ‖A ^ k‖ ≤ C * β ^ k) →
            ∀ (k : ℕ), ‖Euler2D.stableSequenceGreenTermCLM ρ A k‖ ≤ C / ρ * (β / ρ) ^ k)
    :
    ‖stableSequenceGreenCLM ρ A‖ ≤ C / (ρ - β) := by
  have hr : ‖β / ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hβ0 hρ.le)]
    exact (div_lt_one hρ).mpr hβρ
  have hb := tsum_of_norm_bounded ((summable_geometric_of_norm_lt_one hr).mul_left (C / ρ)).hasSum
    (fun k => h_Euler2D_norm_stableSequenceGreenTermCLM_le_geometric hρ A hA k)
  change ‖∑' k : ℕ, stableSequenceGreenTermCLM ρ A k‖ ≤ _
  calc
    _ ≤ ∑' k : ℕ, (C / ρ) * (β / ρ) ^ k := hb
    _ = (C / ρ) * (1 - β / ρ)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
    _ = C / (ρ - β) := by
      field_simp [hρ.ne', (sub_pos.mpr hβρ).ne', (sub_pos.mpr ((div_lt_one hρ).mpr hβρ)).ne'] <;> ring
end Euler2D
end
