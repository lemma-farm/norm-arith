module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.Reparam
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.CurveContinuity
/-!
# Rescaled-arclength parametrizations of Lipschitz Jordan curves

A Lipschitz, `2π`-periodic curve `γ` which is injective on `[0, 2π)` can be reparametrized by
rescaled arclength: there is a curve `γ̃` with the same image of `[0, 2π]`, again Lipschitz,
`2π`-periodic and injective on `[0, 2π)`, with `‖γ̃'‖` equal to a positive constant almost
everywhere, with the same signed-area integral `∫₀^{2π} Im(conj γ · γ')`, and with
`γ = γ̃ ∘ τ` for a monotone Lipschitz `τ` fixing `0` and `2π` (`exists_constSpeed_reparam`).
Reversing the direction changes the sign of this integral
(`exists_reverse_param`).

These are the analytic steps that turn a Lipschitz Jordan parametrization of the boundary into
a positively oriented rescaled-arclength parametrization (Definition 10.1 of the paper).
-/
@[expose] public section
open MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
lemma norm_deriv_le_of_lipschitzWith {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (x : ℝ) : ‖deriv γ x‖ ≤ K :=
  norm_deriv_le_of_lipschitz hK
lemma locallyIntegrable_of_bounded {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} {M : ℝ} (hf : AEStronglyMeasurable f volume) (hB : ∀ x, ‖f x‖ ≤ M) :
    LocallyIntegrable f volume := by
  refine locallyIntegrable_iff.mpr fun k hk => ?_
  exact Measure.integrableOn_of_bounded (M := M) hk.measure_lt_top.ne
    hf (Eventually.of_forall hB)
/-- The primitive of a bounded locally integrable function is Lipschitz. -/
lemma lipschitzWith_primitive {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {M : NNReal} (hf : AEStronglyMeasurable f volume) (hB : ∀ x, ‖f x‖ ≤ M)
    (a : ℝ) : LipschitzWith M (fun x => ∫ t in a..x, f t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_bounded hf hB _ _) (intervalIntegrable_of_bounded hf hB _ _),
    Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hB t
/-- Fundamental theorem of calculus for Lipschitz curves. -/
theorem integral_deriv_of_lipschitz {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (a b : ℝ) : ∫ x in a..b, deriv γ x = γ b - γ a := by
  have hloc : LocallyIntegrable (deriv γ) volume :=
    locallyIntegrable_of_bounded (measurable_deriv γ).aestronglyMeasurable
      (norm_deriv_le_of_lipschitzWith hK)
  have hF := lipschitzWith_primitive (measurable_deriv γ).aestronglyMeasurable
      (norm_deriv_le_of_lipschitzWith hK) a
  have hg : LipschitzWith (K + K) (fun x => γ x - ∫ t in a..x, deriv γ t) := hK.sub hF
  have g_ac : AbsolutelyContinuousOnInterval (fun x => γ x - ∫ t in a..x, deriv γ t) a b :=
    (hg.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval
  have g_ae : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun x => γ x - ∫ t in a..x, deriv γ t) 0 x := by
    filter_upwards [hK.ae_differentiableAt (μ := volume),
      ae_hasDerivAt_integral_of_locallyIntegrable hloc] with x hx₁ hx₂ _
    have := hx₁.hasDerivAt.sub (hx₂ a)
    rw [sub_self] at this
    exact this
  obtain ⟨C, hC⟩ := g_ac.const_of_ae_hasDerivAt_zero g_ae
  have h1 := hC a (by simp)
  have h2 := hC b (by simp)
  simp only [intervalIntegral.integral_same, sub_zero] at h1 h2
  rw [← h1] at h2
  linear_combination -h2
section ArcLen
variable {γ : ℝ → ℂ} {K : NNReal}
end ArcLen
end PolyaNeumann
