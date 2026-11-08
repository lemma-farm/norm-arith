/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/BorelCalculus.lean
-/
/-
# The Borel functional calculus of a self-adjoint operator (Stage C2)

Proof layer of the von Neumann root `exists_modulusFamily` (nodes 1.3.1/1.3.2).

For a self-adjoint bounded operator `E` on a complex Hilbert space and a
bounded Borel function `g : ℝ → ℝ`, `bfc E hE g` is the bounded operator whose
sesquilinear form is the polarization
`pol g ξ η = (Q(ξ+η) − Q(ξ−η) − i Q(ξ+iη) + i Q(ξ−iη))/4`,
`Q(ζ) = ∫ g dν_ζ`, of the spectral measures of `VN/SpectralMeasure.lean`.

The only analytic input is the **transfer principle**: every algebraic identity
of the forms `pol g` that holds for continuous `g` (where `pol g ξ η =
⟪ξ, cfc g E η⟫` by the polarization identity) holds for bounded Borel `g`,
because both sides are "combinations" `g ↦ (∫ g dμ₁ − ∫ g dμ₂) + i (∫ g dμ₃ −
∫ g dμ₄)` of finite measures, and finite Borel measures on `ℝ` are determined
by `C_c(ℝ)`. This gives sesquilinearity and boundedness (hence the operator, by
Riesz–Fréchet), self-adjointness, agreement with `cfc` on continuous functions,
linearity, and — through the identity `pol g ξ (bfc h η) = pol (g h) ξ η`,
proved first for continuous `g` by transfer in `h`, then by transfer in `g` —
**multiplicativity** `bfc (g h) = bfc g * bfc h`. Order properties follow from
the quadratic form. Nothing here is a manuscript statement.
-/
module
public import Mathlib
public import Examples.vidick__MIPRE_formalization.Dependencies.v1bfcfb1edd13.MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralMeasure
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace CommutingRepetition
namespace BorelCalc
open scoped InnerProductSpace Topology ENNReal NNReal ComplexConjugate CompactlySupported
open Filter MeasureTheory
set_option linter.unusedSectionVars false
/-! ### Bounded Borel functions -/
/-- Bounded Borel functions on `ℝ`: the domain of the Borel functional calculus. -/
def Bdd (g : ℝ → ℝ) : Prop := Measurable g ∧ ∃ C, ∀ t, |g t| ≤ C
namespace Bdd
end Bdd
/-! ### Combinations of finite measures and the transfer principle -/
/-- `Φ` is a *combination*: `Φ g = (∫ g dμ₁ − ∫ g dμ₂) + i (∫ g dμ₃ − ∫ g dμ₄)` for
bounded Borel `g`, with `μ₁, …, μ₄` finite measures on `ℝ`. -/
def IsCombo (Φ : (ℝ → ℝ) → ℂ) : Prop :=
  ∃ μ₁ μ₂ μ₃ μ₄ : Measure ℝ, IsFiniteMeasure μ₁ ∧ IsFiniteMeasure μ₂ ∧ IsFiniteMeasure μ₃ ∧
    IsFiniteMeasure μ₄ ∧ ∀ g, Bdd g → Φ g =
      (((∫ t, g t ∂μ₁) - ∫ t, g t ∂μ₂ : ℝ) : ℂ) +
        Complex.I * (((∫ t, g t ∂μ₃) - ∫ t, g t ∂μ₄ : ℝ) : ℂ)
namespace IsCombo
end IsCombo
/-! ### The polarized form -/
section Pol
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)
/-- The quadratic form `Q g ξ = ∫ g dν_ξ` (as a complex number). -/
noncomputable def Q (g : ℝ → ℝ) (ξ : 𝓗) : ℂ := ((∫ t, g t ∂(ν E hE ξ) : ℝ) : ℂ)
/-- The polarized form: `pol g ξ η = ⟪ξ, g(E) η⟫` for continuous `g`. -/
noncomputable def pol (g : ℝ → ℝ) (ξ η : 𝓗) : ℂ :=
  (Q E hE g (ξ + η) - Q E hE g (ξ - η) - Complex.I * Q E hE g (ξ + Complex.I • η) +
    Complex.I * Q E hE g (ξ - Complex.I • η)) / 4
theorem norm_Q_le {g : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |g t| ≤ C) (ξ : 𝓗) :
    ‖Q E hE g ξ‖ ≤ C * ‖ξ‖ ^ 2 := by
  rw [Q, Complex.norm_real, Real.norm_eq_abs]
  exact abs_integral_ν_le E hE ξ hC
theorem norm_pol_le_sq {g : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |g t| ≤ C) (ξ η : 𝓗) :
    ‖pol E hE g ξ η‖ ≤ C * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h1 := norm_Q_le E hE hC (ξ + η)
  have h2 := norm_Q_le E hE hC (ξ - η)
  have h3 := norm_Q_le E hE hC (ξ + Complex.I • η)
  have h4 := norm_Q_le E hE hC (ξ - Complex.I • η)
  have p1 : ‖ξ + η‖ ^ 2 + ‖ξ - η‖ ^ 2 = 2 * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ ξ η
    nlinarith [this]
  have p2 : ‖ξ + Complex.I • η‖ ^ 2 + ‖ξ - Complex.I • η‖ ^ 2 = 2 * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ ξ (Complex.I • η)
    rw [norm_smul, Complex.norm_I, one_mul] at this
    nlinarith [this]
  have hn : ‖pol E hE g ξ η‖ ≤ (‖Q E hE g (ξ + η)‖ + ‖Q E hE g (ξ - η)‖ +
      ‖Q E hE g (ξ + Complex.I • η)‖ + ‖Q E hE g (ξ - Complex.I • η)‖) / 4 := by
    unfold pol
    rw [norm_div, Complex.norm_ofNat]
    gcongr
    calc ‖Q E hE g (ξ + η) - Q E hE g (ξ - η) - Complex.I * Q E hE g (ξ + Complex.I • η) +
          Complex.I * Q E hE g (ξ - Complex.I • η)‖
        ≤ ‖Q E hE g (ξ + η) - Q E hE g (ξ - η) - Complex.I * Q E hE g (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q E hE g (ξ - Complex.I • η)‖ := norm_add_le _ _
      _ ≤ ‖Q E hE g (ξ + η) - Q E hE g (ξ - η)‖ + ‖Complex.I * Q E hE g (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q E hE g (ξ - Complex.I • η)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖Q E hE g (ξ + η)‖ + ‖Q E hE g (ξ - η)‖ + ‖Complex.I * Q E hE g (ξ + Complex.I • η)‖ +
          ‖Complex.I * Q E hE g (ξ - Complex.I • η)‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
  calc ‖pol E hE g ξ η‖ ≤ _ := hn
    _ ≤ (C * ‖ξ + η‖ ^ 2 + C * ‖ξ - η‖ ^ 2 + C * ‖ξ + Complex.I • η‖ ^ 2 +
        C * ‖ξ - Complex.I • η‖ ^ 2) / 4 := by gcongr
    _ = C * (‖ξ‖ ^ 2 + ‖η‖ ^ 2) := by linear_combination (C / 4) * p1 + (C / 4) * p2
end Pol
/-! ### The Borel functional calculus -/
section Bfc
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)
end Bfc
end BorelCalc
end CommutingRepetition
end
