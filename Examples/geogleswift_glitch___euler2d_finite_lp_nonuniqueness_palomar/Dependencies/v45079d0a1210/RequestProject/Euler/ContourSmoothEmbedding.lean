module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.LittleContourSpace
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourChordArc
/-!
# Genuine smooth periodic functions in the contour Banach space

All actual smooth 2π-periodic functions, including the reference circles,
embed in the little C¹ Hölder space for 0 < γ ≤ 1.  The derivative Hölder
bound is proved using true shortest circle representatives and a bound on
the actual second derivative of the periodic function.
-/
@[expose] public section
noncomputable section
open Set Filter Topology Metric Complex
open scoped NNReal ENNReal BoundedContinuousFunction ContDiff
namespace Euler2D
theorem lipschitzWith_contour_of_deriv_bound {f : ContourCircle → ℂ} {C : ℝ≥0}
    (hf : ContDiff ℝ 1 (fun θ : ℝ => f (θ : ContourCircle)))
    (hd : ∀ θ : ℝ, ‖deriv (fun t : ℝ => f (t : ContourCircle)) θ‖ ≤ C) :
    LipschitzWith C f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨θ, φ, hθ, hφ, _, hdist⟩ := exists_short_contour_representatives x y
  have hb := norm_sub_le_of_contDiff_deriv_bound hf C.coe_nonneg hd θ φ
  rw [hθ, hφ, ← hdist] at hb
  simpa only [dist_eq_norm] using hb
lemma contour_dist_le_pi (x y : ContourCircle) : dist x y ≤ Real.pi := by
  obtain ⟨_, _, _, _, hb, hd⟩ := exists_short_contour_representatives x y
  rwa [hd]
/-- A genuine Lipschitz function is Hölder for all exponents at most one
in the genuine circle metric. -/
theorem memHolder_contour_of_lipschitz {γ C : ℝ≥0} {f : ContourCircle → ℂ}
    (hγ : γ ≤ 1) (hf : LipschitzWith C f) : MemHolder γ f := by
  have hb (x y : ContourCircle) : edist x y ≤ ENNReal.ofReal Real.pi := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (contour_dist_le_pi x y)
  exact (hf.holderWith.of_le (D := Real.toNNReal Real.pi) hb hγ).memHolder
end Euler2D
end
