module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v081b08e93cc6.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Weights
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Bounds of weighted smoothings and their partials by `∫ (1 + |y - y'|)² Φ_h dm`

For a bounded measurable weight `f` (`|f| ≤ Cf`), the weighted smoothing of `m` and its first and
second coordinate partials are bounded pointwise by `Cf`, `Cf |C₁|`, `Cf |C₂|` times
`smoothWeight2`, where `C_k` is the constant of the derivative bound of the Gaussian flow estimates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ} {lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h : ℝ}
  {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}
  (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]
theorem abs_integral_weighted_le {g : EvolutionAmbientState d → ℝ} (hh : 0 < h)
    (y : EvolutionAmbientState d) (A : ℝ)
    (hg : ∀ a, |f a * g (y - a)| ≤ A * weight2 Φ h (y - a)) :
    |∫ a, f a * g (y - a) ∂m| ≤ A * smoothWeight2 Φ h m y := by
  have := norm_integral_le_of_norm_le (f := fun a => f a * g (y - a))
    ((integrable_weight2_translate (Φ := Φ) m hh y).const_mul A)
    (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hg a)
  rw [integral_const_mul] at this
  simpa [Real.norm_eq_abs, smoothWeight2] using this
theorem abs_coordPartial_smoothWeighted_le (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) {C1 : ℝ}
    (hC1 : ∀ z, ‖iteratedFDeriv ℝ 1 (Φ.kernel h) z‖ ≤ C1 * (1 + ‖z‖) ^ 1 * Φ.kernel h z)
    (c : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    |coordPartial c (smoothWeighted Φ h f m) y| ≤ Cf * |C1| * smoothWeight2 Φ h m y := by
  rw [coordPartial_smoothWeighted hh hf hfb c]
  refine abs_integral_weighted_le (g := coordPartial c (Φ.kernel h)) m hh y (Cf * |C1|)
    (fun a => ?_)
  have h1 := abs_coordPartial_le c (Φ.kernel h) (y - a)
  have h2 : ‖fderiv ℝ (Φ.kernel h) (y - a)‖ ≤ |C1| * weight2 Φ h (y - a) := by
    have := hC1 (y - a)
    rw [norm_iteratedFDeriv_one] at this
    refine this.trans ?_
    have hp := Φ.pos hh (y - a)
    have hn := norm_nonneg (y - a)
    unfold weight2
    calc C1 * (1 + ‖y - a‖) ^ 1 * Φ.kernel h (y - a)
        ≤ |C1| * ((1 + ‖y - a‖) ^ 1 * Φ.kernel h (y - a)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C1| * ((1 + ‖y - a‖) ^ 2 * Φ.kernel h (y - a)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hp.le) (abs_nonneg _)
          nlinarith
  rw [abs_mul]
  calc |f a| * |coordPartial c (Φ.kernel h) (y - a)| ≤ Cf * (|C1| * weight2 Φ h (y - a)) :=
        mul_le_mul (hfb a) (h1.trans h2) (abs_nonneg _) ((abs_nonneg _).trans (hfb a))
    _ = Cf * |C1| * weight2 Φ h (y - a) := by ring
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
