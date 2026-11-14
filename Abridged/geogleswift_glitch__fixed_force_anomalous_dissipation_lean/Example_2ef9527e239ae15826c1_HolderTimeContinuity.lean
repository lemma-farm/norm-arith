module

public import Mathlib

-- ==== Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.Basic ====
public section
/-!
# Section 1: definitions (torus calculus, function spaces, classical solutions)

Conventions used throughout the formalization.

* A point of the torus `𝕋^d = ℝ^d / ℤ^d` is represented by a point of its lift `Pt d = Fin d → ℝ`;
  functions on the torus are `ℤ^d`-periodic functions on `Pt d` (`IsPeriodic`).
* Normalized Lebesgue measure on `𝕋^d` is Lebesgue measure on the unit cell `cell d = [0,1]^d`.
* Spatial derivatives are partial derivatives `pd i h x` (Fréchet derivative applied to the
  `i`-th basis vector).  Divergence, Laplacian, convective derivative, gradient and the squared
  Frobenius norm of the gradient are defined explicitly from them.
* Time derivatives on `[0,T]` are derivatives within `[0,T]` (`dt`).
* The parabolic Hölder spaces `C^{1+β/2,2+β}` and `C^{β/2,1+β}` are encoded by the predicates
  `IsParabolicC12` and `IsParabolicC01` (standard Hölder conditions with respect to the parabolic
  distance `|x-y| + |t-s|^{1/2}`).
-/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace AnomDiss
/-- Points of the lift `ℝ^d` of the torus `𝕋^d`. -/
abbrev Pt (d : ℕ) := Fin d → ℝ

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def holderNorm (α : ℝ) (h : Pt d → E) : ℝ≥0∞ :=
  (⨆ x, ‖h x‖ₑ) + ⨆ x, ⨆ y, ‖h x - h y‖ₑ / ‖x - y‖ₑ ^ α

end AnomDiss

end
end
end

-- ==== Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.ForceRegularity ====
public section
/-!
# Lemma 4.6: regularity of the fixed horizontal force

The force `g_ω` is a sum of rescaled pulses supported in disjoint open subintervals of the
pulse intervals `I_j`.  Its `r`-th time derivative is the corresponding sum of the pieces
`(k_j δ_j^{r+2})⁻¹ (∂ₛ^{r+1} b_{ω_j})((t - s_j)/δ_j, k_j x)`.  Each piece is bounded in `C^α`
by `C k_j^{α-1} δ_j^{-r-2}`, which tends to zero (even after division by `η_j`), so all time
derivatives extend by zero across the accumulation time `T_*`.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
/-! ### The pieces -/
axiom holderNorm_zero' {d : ℕ} {E : Type*} [NormedAddCommGroup E] (α : ℝ) :
    holderNorm α (0 : Pt d → E) = 0
axiom holderNorm_add_le {d : ℕ} {E : Type*} [NormedAddCommGroup E] (α : ℝ) (f g : Pt d → E) :
    holderNorm α (f + g) ≤ holderNorm α f + holderNorm α g
end AnomDiss

end
end
end

-- ==== Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Examples.Example_2ef9527e239ae15826c1_HolderTimeContinuity ====
/-!
# Continuity of every Hölder-valued time derivative

The difference-quotient definition in `IsSmoothHolderValued` already forces
continuity of every derivative in the full Hölder norm. This uses the norm
triangle inequality and homogeneity, without any PDE existence input.
-/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace AnomDiss
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
axiom holderNorm_smul (α c : ℝ) (f : Pt d → E) :
    holderNorm α (c • f) = ‖c‖ₑ * holderNorm α f
/-- A derivative in the full Hölder norm implies continuity in that same norm. -/
theorem holderNorm_increment_tendsto_zero {α : ℝ} {f : ℝ → Pt d → E}
    {f' : Pt d → E} {t : ℝ} (hfin : holderNorm α f' < ⊤)
    (hd : Tendsto (fun h : ℝ => holderNorm α
      (h⁻¹ • (f (t + h) - f t) - f')) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => holderNorm α (f (t + h) - f t)) (𝓝 0) (𝓝 0) := by
  let C : ℝ≥0∞ := 1 + holderNorm α f'
  have hC : C ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨by simp, hfin.ne⟩
  have herr : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      holderNorm α (h⁻¹ • (f (t + h) - f t) - f') < 1 :=
    hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  have hb : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      holderNorm α (f (t + h) - f t) ≤ ‖h‖ₑ * C := by
    filter_upwards [herr, self_mem_nhdsWithin] with h he hh
    have hn : h ≠ 0 := by simpa using hh
    have heq : h⁻¹ • (f (t + h) - f t) =
        (h⁻¹ • (f (t + h) - f t) - f') + f' := by abel
    have hquot : holderNorm α (h⁻¹ • (f (t + h) - f t)) ≤ C := by
      rw [heq]
      exact (holderNorm_add_le _ _ _).trans (add_le_add he.le le_rfl)
    calc
      holderNorm α (f (t + h) - f t) =
          holderNorm α (h • (h⁻¹ • (f (t + h) - f t))) := by
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      _ = ‖h‖ₑ * holderNorm α (h⁻¹ • (f (t + h) - f t)) := holderNorm_smul _ _ _
      _ ≤ ‖h‖ₑ * C := mul_le_mul_right hquot _
  have hb' : ∀ᶠ h : ℝ in 𝓝 0,
      holderNorm α (f (t + h) - f t) ≤ ‖h‖ₑ * C := by
    filter_upwards [eventually_nhdsWithin_iff.mp hb] with h hh
    by_cases hn : h = 0
    · simp [hn, holderNorm_zero']
    · exact hh (by simpa using hn)
  have hnorm : Tendsto (fun h : ℝ => ‖h‖ₑ) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, ofReal_norm_eq_enorm, norm_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (continuous_norm.tendsto (0 : ℝ))
  have hbound := ENNReal.Tendsto.mul_const hnorm (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_mul] using hbound) (Eventually.of_forall fun _ => zero_le) hb'
end AnomDiss
