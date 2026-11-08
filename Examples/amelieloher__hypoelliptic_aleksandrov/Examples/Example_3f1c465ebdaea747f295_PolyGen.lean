module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vd26ff82a3ffe.HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.PolyClass
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Iterated derivatives of the Gaussian exponential

The iterated coordinate derivatives of `K * G_θ` are polynomial multiples `K * P_θ * G_θ`, with
`P` in the class `PG` of the length of the derivative word. This is the polynomial structure behind
the derivative bounds of the Gaussian flow.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
variable {d : ℕ}
theorem abs_coord_le (y : EvolutionAmbientState d) (i : Fin d) :
    |y.1 i| ≤ ‖y‖ ∧ |y.2 i| ≤ ‖y‖ := by
  constructor
  · calc |y.1 i| = ‖y.1 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖y.1‖ := norm_le_pi_norm y.1 i
      _ ≤ ‖y‖ := norm_fst_le y
  · calc |y.2 i| = ‖y.2 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖y.2‖ := norm_le_pi_norm y.2 i
      _ ≤ ‖y‖ := norm_snd_le y
theorem abs_genT_le {S : ℝ} {θ : Theta} (hθ : θ ∈ Coef S) (δ : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) : |genT θ δ y| ≤ 3 * S * (1 + ‖y‖) := by
  obtain ⟨ha, hb, hc⟩ := hθ
  have hS : 0 ≤ S := (abs_nonneg _).trans ha
  have hn := norm_nonneg y
  rcases δ with i | i
  · obtain ⟨h1, h2⟩ := abs_coord_le y i
    unfold genT gen
    calc |θ.2.1 * y.2 i + 2 * θ.2.2 * y.1 i|
        ≤ |θ.2.1 * y.2 i| + |2 * θ.2.2 * y.1 i| := abs_add_le _ _
      _ = |θ.2.1| * |y.2 i| + 2 * |θ.2.2| * |y.1 i| := by
          rw [abs_mul, abs_mul, abs_mul]; norm_num
      _ ≤ S * ‖y‖ + 2 * S * ‖y‖ := by
          gcongr
      _ ≤ 3 * S * (1 + ‖y‖) := by nlinarith
  · obtain ⟨h1, h2⟩ := abs_coord_le y i
    unfold genT gen
    calc |2 * θ.1 * y.2 i + θ.2.1 * y.1 i|
        ≤ |2 * θ.1 * y.2 i| + |θ.2.1 * y.1 i| := abs_add_le _ _
      _ = 2 * |θ.1| * |y.2 i| + |θ.2.1| * |y.1 i| := by
          rw [abs_mul, abs_mul, abs_mul]; norm_num
      _ ≤ 2 * S * ‖y‖ + S * ‖y‖ := by
          gcongr
      _ ≤ 3 * S * (1 + ‖y‖) := by nlinarith
end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient
