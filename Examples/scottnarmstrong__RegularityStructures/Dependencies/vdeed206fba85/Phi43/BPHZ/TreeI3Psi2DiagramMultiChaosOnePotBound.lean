/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePot
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Cross terms and pairings of potentials, general exponents

Generalisations of `chaosOne_cross_le` and `chaosOne_pp_le` to potentials of kernels of order
`3 + ε₂` against majorants `s(w)^(-3) s(z - w)^(-(2+ε₁))` of the weight `h`:

* `chaosOne_cross_gen`: `∫ s(z - y)^(-(3+ε₃)) Pot_J h (y) dy ≤ C (s(z')^(-η) + s(z)^(-η))`,
  `η = 1 + ε₁ + ε₂ + ε₃`;
* `chaosOne_pp_gen`: `∫ Pot_{J₁} h₁ Pot_{J₂} h₂ dy ≤ C (s(z)^(-η) s(z')^(-ε₁') + s(z')^(-(ε₁'+η)))`,
  `η = 1 + ε₁ + ε₂ + ε₂'`.
-/
public section
open MeasureTheory
namespace RegularityStructures
/-- The cross term `∫ s(z - y)^(-(3+ε₃)) Pot_J h(y) dy`. -/
theorem chaosOne_cross_gen {ε₁ ε₂ ε₃ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hε₃ : 0 ≤ ε₃)
    (hs : ε₁ + ε₂ + ε₃ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J h : SpaceTime → ℝ} {BJ Hc : ℝ}, 0 ≤ BJ → 0 ≤ Hc → Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ BJ * torusParabolicSize x ^ (-(3 + ε₂))) →
      Measurable h → (∀ w, 0 ≤ h w) → ∀ z z' : SpaceTime, 0 < torusParabolicSize z →
        0 < torusParabolicSize z' →
        (∀ᵐ w : SpaceTime ∂volume,
          h w ≤ Hc * (singularPow 3 0 w * singularPow (2 + ε₁) z' w)) →
          Integrable (fun y => singularPow (3 + ε₃) z y * i3Psi2Pot J h y) ∧
            ∫ y, singularPow (3 + ε₃) z y * i3Psi2Pot J h y ≤
              C * Hc * BJ * (torusParabolicSize z' ^ (-(1 + ε₁ + ε₂ + ε₃)) +
                torusParabolicSize z ^ (-(1 + ε₁ + ε₂ + ε₃))) := by
  obtain ⟨Cp, hCp, hp⟩ := power_mul_abs_J_le_gen (a := 3 + ε₃) (j := 3 + ε₂) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨Cl, hCl, hl⟩ := singularIntLe_mul_three (a := 2 + ε₁) (b := 1 + ε₂ + ε₃) (c := 3)
    (η := 1 + ε₁ + ε₂ + ε₃) (by linarith) (by linarith) (by linarith) (by norm_num)
    (by norm_num) (by linarith) (by ring)
  refine ⟨Cp * Cl, mul_nonneg hCp hCl, ?_⟩
  intro J h BJ Hc hBJ hHc hJm hJ hhm hh0 z z' hz hz' hH
  have pz : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz' : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  have hX : SingularIntLe (fun w => (Hc * (singularPow 3 0 w * singularPow (2 + ε₁) z' w)) *
      ((Cp * BJ) * singularPow (1 + ε₂ + ε₃) z w))
      (Cp * Cl * Hc * BJ * (torusParabolicSize z' ^ (-(1 + ε₁ + ε₂ + ε₃)) +
        torusParabolicSize z ^ (-(1 + ε₁ + ε₂ + ε₃)))) := by
    have := ((hl z' z 0 pz' pz).const_mul (c := Hc * (Cp * BJ))
      (mul_nonneg hHc (mul_nonneg hCp hBJ)))
    simp only [sub_zero] at this
    exact (this.congr_fun (g := fun w => (Hc * (singularPow 3 0 w * singularPow (2 + ε₁) z' w)) *
      ((Cp * BJ) * singularPow (1 + ε₂ + ε₃) z w)) (fun w => by ring)).mono_right
      (le_of_eq (by ring))
  refine integral_mul_pot_le (H := fun w => Hc * (singularPow 3 0 w *
    singularPow (2 + ε₁) z' w)) (U := fun w => (Cp * BJ) * singularPow (1 + ε₂ + ε₃) z w) hJm
    (fun y => singularPow_nonneg _ _ _) (measurable_singularPow _ _) hh0 hhm hH ?_ hX
  filter_upwards [ae_torusParabolicSize_sub_pos z] with w hw
  obtain ⟨i, b⟩ := hp hBJ hJm hJ z w hw
  have e : (5 - (3 + ε₃) - (3 + ε₂) : ℝ) = -(1 + ε₂ + ε₃) := by ring
  rw [e] at b
  refine ⟨i, ?_⟩
  simpa [singularPow, mul_assoc] using b
end RegularityStructures
end
