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
public import Examples.vidick__MIPRE_formalization.Dependencies.vb56476c3629b.MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralMeasure
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
theorem measurable {g : ℝ → ℝ} (hg : Bdd g) : Measurable g := hg.1
theorem integrable {g : ℝ → ℝ} (hg : Bdd g) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable g μ := by
  obtain ⟨C, hC⟩ := hg.2
  exact integrable_of_bdd hg.1 hC
theorem add {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) : Bdd (g + h) := by
  obtain ⟨C, hC⟩ := hg.2
  obtain ⟨D, hD⟩ := hh.2
  exact ⟨hg.1.add hh.1, C + D, fun t =>
    (abs_add_le _ _).trans (add_le_add (hC t) (hD t))⟩
theorem neg {g : ℝ → ℝ} (hg : Bdd g) : Bdd (-g) := by
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨hg.1.neg, C, fun t => by rw [Pi.neg_apply, abs_neg]; exact hC t⟩
theorem sub {g h : ℝ → ℝ} (hg : Bdd g) (hh : Bdd h) : Bdd (g - h) := by
  rw [sub_eq_add_neg]; exact hg.add hh.neg
theorem of_continuous {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) : Bdd g :=
  ⟨hg.measurable, C, hC⟩
theorem of_compactlySupported (f : C_c(ℝ, ℝ)) : Bdd f :=
  of_continuous f.continuous (C := ‖f.toBoundedContinuousFunction‖) fun t => by
    have := BoundedContinuousFunction.norm_coe_le_norm f.toBoundedContinuousFunction t
    simpa [Real.norm_eq_abs] using this
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
theorem integral (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsCombo fun g => ((∫ t, g t ∂μ : ℝ) : ℂ) :=
  ⟨μ, 0, 0, 0, inferInstance, inferInstance, inferInstance, inferInstance, fun g _ => by
    simp⟩
theorem add {Φ Ψ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) (hΨ : IsCombo Ψ) :
    IsCombo fun g => Φ g + Ψ g := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  obtain ⟨ν₁, ν₂, ν₃, ν₄, k₁, k₂, k₃, k₄, hΨ⟩ := hΨ
  refine ⟨μ₁ + ν₁, μ₂ + ν₂, μ₃ + ν₃, μ₄ + ν₄, inferInstance, inferInstance, inferInstance,
    inferInstance, fun g hg => ?_⟩
  dsimp only
  rw [hΦ g hg, hΨ g hg, integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _),
    integral_add_measure (hg.integrable _) (hg.integrable _)]
  push_cast
  ring
theorem smul_real (r : ℝ) {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) :
    IsCombo fun g => (r : ℂ) * Φ g := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  rcases le_total 0 r with hr | hr
  · refine ⟨ENNReal.ofReal r • μ₁, ENNReal.ofReal r • μ₂, ENNReal.ofReal r • μ₃,
      ENNReal.ofReal r • μ₄, isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top, fun g hg => ?_⟩
    dsimp only
    rw [hΦ g hg]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal hr, smul_eq_mul]
    push_cast
    ring
  · refine ⟨ENNReal.ofReal (-r) • μ₂, ENNReal.ofReal (-r) • μ₁, ENNReal.ofReal (-r) • μ₄,
      ENNReal.ofReal (-r) • μ₃, isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top,
      isFiniteMeasure_smul_of_ne_top ENNReal.ofReal_ne_top, fun g hg => ?_⟩
    dsimp only
    rw [hΦ g hg]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal (neg_nonneg.mpr hr), smul_eq_mul]
    push_cast
    ring
theorem smul_I {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) : IsCombo fun g => Complex.I * Φ g := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  refine ⟨μ₄, μ₃, μ₁, μ₂, h₄, h₃, h₁, h₂, fun g hg => ?_⟩
  dsimp only
  rw [hΦ g hg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring
theorem smul (c : ℂ) {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) : IsCombo fun g => c * Φ g := by
  have : (fun g => c * Φ g) = fun g => (c.re : ℂ) * Φ g + Complex.I * ((c.im : ℂ) * Φ g) := by
    funext g
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  rw [this]
  exact (hΦ.smul_real c.re).add (hΦ.smul_real c.im).smul_I
theorem neg {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) : IsCombo fun g => -Φ g := by
  have : (fun g => -Φ g) = fun g => (-1 : ℂ) * Φ g := by funext g; ring
  rw [this]
  exact hΦ.smul (-1)
theorem sub {Φ Ψ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) (hΨ : IsCombo Ψ) :
    IsCombo fun g => Φ g - Ψ g := by
  have : (fun g => Φ g - Ψ g) = fun g => Φ g + -Ψ g := by funext g; ring
  rw [this]
  exact hΦ.add hΨ.neg
theorem transfer {Φ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ)
    (h : ∀ g : ℝ → ℝ, Continuous g → Bdd g → Φ g = 0) {g : ℝ → ℝ} (hg : Bdd g) : Φ g = 0 := by
  obtain ⟨μ₁, μ₂, μ₃, μ₄, h₁, h₂, h₃, h₄, hΦ⟩ := hΦ
  have key : ∀ f : ℝ → ℝ, Bdd f → Φ f = 0 → (∫ t, f t ∂μ₁ = ∫ t, f t ∂μ₂) ∧
      (∫ t, f t ∂μ₃ = ∫ t, f t ∂μ₄) := by
    intro f hf h0
    rw [hΦ f hf] at h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im,
      zero_mul, one_mul, sub_zero, zero_add, add_zero, mul_zero] at hre him
    exact ⟨sub_eq_zero.mp hre, sub_eq_zero.mp him⟩
  have e12 : μ₁ = μ₂ := Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    (key f (Bdd.of_compactlySupported f) (h f f.continuous (Bdd.of_compactlySupported f))).1
  have e34 : μ₃ = μ₄ := Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    (key f (Bdd.of_compactlySupported f) (h f f.continuous (Bdd.of_compactlySupported f))).2
  rw [hΦ g hg, e12, e34]
  simp
/-- Two combinations agreeing on bounded continuous functions agree on bounded Borel
functions. -/
theorem eq {Φ Ψ : (ℝ → ℝ) → ℂ} (hΦ : IsCombo Φ) (hΨ : IsCombo Ψ)
    (h : ∀ g : ℝ → ℝ, Continuous g → Bdd g → Φ g = Ψ g) {g : ℝ → ℝ} (hg : Bdd g) : Φ g = Ψ g :=
  sub_eq_zero.mp ((hΦ.sub hΨ).transfer (fun g hgc hgb => sub_eq_zero.mpr (h g hgc hgb)) hg)
/-! #### Multiplying the test function by a fixed bounded Borel function -/
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
theorem isCombo_Q (ξ : 𝓗) : IsCombo fun g => Q E hE g ξ := IsCombo.integral _
theorem isCombo_pol (ξ η : 𝓗) : IsCombo fun g => pol E hE g ξ η := by
  unfold pol
  simp_rw [div_eq_inv_mul]
  exact IsCombo.smul _ ((((isCombo_Q E hE _).sub (isCombo_Q E hE _)).sub
    ((isCombo_Q E hE _).smul _)).add ((isCombo_Q E hE _).smul _))
theorem pol_cfc {g : ℝ → ℝ} (hg : Continuous g) (ξ η : 𝓗) :
    pol E hE g ξ η = ⟪ξ, cfc g E η⟫_ℂ := by
  have hsa : IsSelfAdjoint (cfc g E) := cfc_predicate g E
  have key : ∀ ζ, Q E hE g ζ = ⟪((cfc g E : 𝓗 →L[ℂ] 𝓗) : 𝓗 →ₗ[ℂ] 𝓗) ζ, ζ⟫_ℂ := fun ζ => by
    rw [Q, integral_ν_complex E hE ζ hg, ContinuousLinearMap.coe_coe, inner_sa hsa]
  rw [inner_sa hsa, ← ContinuousLinearMap.coe_coe (cfc g E), inner_map_polarization']
  unfold pol
  simp only [key]
theorem pol_smul_left {g : ℝ → ℝ} (hg : Bdd g) (c : ℂ) (ξ η : 𝓗) :
    pol E hE g (c • ξ) η = conj c * pol E hE g ξ η :=
  IsCombo.eq (isCombo_pol E hE _ _) ((isCombo_pol E hE _ _).smul _)
    (fun g hgc _ => by simp only [pol_cfc E hE hgc, inner_smul_left]) hg
theorem pol_smul_right {g : ℝ → ℝ} (hg : Bdd g) (c : ℂ) (ξ η : 𝓗) :
    pol E hE g ξ (c • η) = c * pol E hE g ξ η :=
  IsCombo.eq (isCombo_pol E hE _ _) ((isCombo_pol E hE _ _).smul _)
    (fun g hgc _ => by simp only [pol_cfc E hE hgc, map_smul, inner_smul_right]) hg
theorem pol_zero_left {g : ℝ → ℝ} (hg : Bdd g) (η : 𝓗) : pol E hE g 0 η = 0 := by
  have := pol_smul_left E hE hg 0 0 η
  rwa [zero_smul, map_zero, zero_mul] at this
theorem pol_zero_right {g : ℝ → ℝ} (hg : Bdd g) (ξ : 𝓗) : pol E hE g ξ 0 = 0 := by
  have := pol_smul_right E hE hg 0 ξ 0
  rwa [zero_smul, zero_mul] at this
/-! #### Boundedness -/
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
theorem norm_pol_le {g : ℝ → ℝ} (hg : Bdd g) {C : ℝ} (hC : ∀ t, |g t| ≤ C) (ξ η : 𝓗) :
    ‖pol E hE g ξ η‖ ≤ 2 * C * ‖ξ‖ * ‖η‖ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  by_cases hξ : ξ = 0
  · subst hξ
    rw [pol_zero_left E hE hg, norm_zero, norm_zero]
    simp
  by_cases hη : η = 0
  · subst hη
    rw [pol_zero_right E hE hg, norm_zero, norm_zero]
    simp
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hηn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  set t : ℝ := Real.sqrt (‖η‖ / ‖ξ‖) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hηn hξn)
  have htsq : t ^ 2 = ‖η‖ / ‖ξ‖ := Real.sq_sqrt (div_pos hηn hξn).le
  have hscale : pol E hE g ξ η = pol E hE g ((t : ℂ) • ξ) (((t⁻¹ : ℝ) : ℂ) • η) := by
    rw [pol_smul_left E hE hg, pol_smul_right E hE hg, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ htpos.ne', Complex.ofReal_one, one_mul]
  rw [hscale]
  refine (norm_pol_le_sq E hE hC _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos htpos, abs_of_pos (inv_pos.mpr htpos), mul_pow, mul_pow,
    htsq, inv_pow, htsq]
  field_simp
  ring
end Pol
/-! ### The Borel functional calculus -/
section Bfc
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)
end Bfc
end BorelCalc
end CommutingRepetition
end
