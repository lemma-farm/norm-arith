module

public import Mathlib

-- ==== Examples.vidick__MIPRE_formalization.Dependencies.v3b258185e654.MIPRE.Background.Repetition.CommutingRepetition.VN.SpectralMeasure ====
public section
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/SpectralMeasure.lean
-/
/-
# Spectral measures of vector states (Stage C1 of `PLAN-modulus-family.md`)

Proof layer of the von Neumann root `exists_modulusFamily` (nodes 1.3.1/1.3.2).

For a self-adjoint bounded operator `E` on a complex Hilbert space and a vector
`ξ`, the positive functional `f ↦ ⟪ξ, f(E) ξ⟫` on `C(spectrum ℝ E, ℝ)` is
represented (Riesz–Markov–Kakutani, Mathlib `RealRMK.rieszMeasure`) by a finite
measure on the compact spectrum; pushed forward to `ℝ` it is the **spectral
measure** `ν E hE ξ`, with `∫ g dν = ⟪ξ, cfc g E ξ⟫` for every continuous
`g : ℝ → ℝ` (`integral_ν`).

The **transfer principle** `transfer`/`transferC`: a linear identity among the
integrals of finitely many finite Borel measures on `ℝ` that holds for every
continuous test function holds for every bounded Borel function. (Finite Borel
measures on `ℝ` are regular and determined by `C_c(ℝ, ℝ)`; the signed
combination is split into two positive finite measures.) This is the only
uniqueness input of the Borel functional calculus in `VN/BorelCalculus.lean`.
Nothing here is a manuscript statement.
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace CommutingRepetition
namespace BorelCalc
open scoped InnerProductSpace Topology ENNReal CompactlySupported
open Filter MeasureTheory
set_option linter.unusedSectionVars false
/-! ### Finite measures on `ℝ` and the transfer principle -/
section Transfer

end Transfer
/-! ### Self-adjoint operators: elementary inner-product facts -/
section SelfAdjoint
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

end SelfAdjoint
/-! ### The spectral measure of a vector state -/
section Spectral
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)
/-- The vector state `f ↦ re ⟪ξ, f(E) ξ⟫` on `C(spectrum ℝ E, ℝ)`, real-linear. -/
noncomputable def stateLin (ξ : 𝓗) : C(spectrum ℝ E, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (⟪ξ, cfcHom hE f ξ⟫_ℂ).re
  map_add' f g := by
    rw [map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  map_smul' c f := by
    have e : c • cfcHom hE f ξ = ((c : ℂ)) • cfcHom hE f ξ :=
      @RCLike.real_smul_eq_coe_smul ℂ 𝓗 _ _ _ _ _ c (cfcHom hE f ξ)
    rw [map_smul, ContinuousLinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, e,
      inner_smul_right, Complex.re_ofReal_mul]

set_option linter.unusedVariables false in
axiom _root_.CommutingRepetition.BorelCalc.stateLin_nonneg.{w_u_1} : ∀ {𝓗 : Type w_u_1} [inst : NormedAddCommGroup 𝓗] [inst_1 : InnerProductSpace ℂ 𝓗]
  [inst_2 : CompleteSpace 𝓗] (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) (ξ : 𝓗)
  {f : C((↑(spectrum ℝ E) : Type), ℝ)},
  0 ≤ f → 0 ≤ (CommutingRepetition.BorelCalc.stateLin E hE ξ : C((↑(spectrum ℝ E) : Type), ℝ) → ℝ) f
/-- The vector state as a positive linear functional on `C_c(spectrum ℝ E, ℝ)`. -/
noncomputable def Λ (ξ : 𝓗) : C_c(spectrum ℝ E, ℝ) →ₚ[ℝ] ℝ where
  toFun f := stateLin E hE ξ f.toContinuousMap
  map_add' f g := (stateLin E hE ξ).map_add f.toContinuousMap g.toContinuousMap
  map_smul' c f := (stateLin E hE ξ).map_smul c f.toContinuousMap
  monotone' f g hfg := by
    have h0 : 0 ≤ g.toContinuousMap - f.toContinuousMap := by
      rw [sub_nonneg]
      exact ContinuousMap.le_def.mpr fun t => CompactlySupportedContinuousMap.le_def.mp hfg t
    have := stateLin_nonneg E hE ξ h0
    rw [map_sub, sub_nonneg] at this
    exact this

/-- The Riesz measure of the vector state, on the compact spectrum. -/
noncomputable def ν₀ (ξ : 𝓗) : Measure (spectrum ℝ E) := RealRMK.rieszMeasure (Λ E hE ξ)

/-- **The spectral measure** of the vector state `ξ` for the self-adjoint
operator `E`: the Riesz measure of `f ↦ ⟪ξ, f(E) ξ⟫`, pushed forward to `ℝ`. -/
noncomputable def ν (ξ : 𝓗) : Measure ℝ := (ν₀ E hE ξ).map Subtype.val

end Spectral
end BorelCalc
end CommutingRepetition
end

end

-- ==== Examples.vidick__MIPRE_formalization.Dependencies.v3b258185e654.MIPRE.Background.Repetition.CommutingRepetition.VN.BorelCalculus ====
public section
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

namespace IsCombo

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

set_option linter.unusedVariables false in
axiom _root_.CommutingRepetition.BorelCalc.pol_add_left.{w_u_1} : ∀ {𝓗 : Type w_u_1} [inst : NormedAddCommGroup 𝓗] [inst_1 : InnerProductSpace ℂ 𝓗]
  [inst_2 : CompleteSpace 𝓗] (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) {g : ℝ → ℝ},
  CommutingRepetition.BorelCalc.Bdd g →
    ∀ (ξ ξ' η : 𝓗),
      CommutingRepetition.BorelCalc.pol E hE g (ξ + ξ') η =
        CommutingRepetition.BorelCalc.pol E hE g ξ η + CommutingRepetition.BorelCalc.pol E hE g ξ' η
set_option linter.unusedVariables false in
axiom _root_.CommutingRepetition.BorelCalc.pol_smul_left.{w_u_1} : ∀ {𝓗 : Type w_u_1} [inst : NormedAddCommGroup 𝓗] [inst_1 : InnerProductSpace ℂ 𝓗]
  [inst_2 : CompleteSpace 𝓗] (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) {g : ℝ → ℝ},
  CommutingRepetition.BorelCalc.Bdd g →
    ∀ (c : ℂ) (ξ η : 𝓗),
      CommutingRepetition.BorelCalc.pol E hE g (c • ξ) η =
        (starRingEnd ℂ : ℂ → ℂ) c * CommutingRepetition.BorelCalc.pol E hE g ξ η
set_option linter.unusedVariables false in
axiom _root_.CommutingRepetition.BorelCalc.pol_add_right.{w_u_1} : ∀ {𝓗 : Type w_u_1} [inst : NormedAddCommGroup 𝓗] [inst_1 : InnerProductSpace ℂ 𝓗]
  [inst_2 : CompleteSpace 𝓗] (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) {g : ℝ → ℝ},
  CommutingRepetition.BorelCalc.Bdd g →
    ∀ (ξ η η' : 𝓗),
      CommutingRepetition.BorelCalc.pol E hE g ξ (η + η') =
        CommutingRepetition.BorelCalc.pol E hE g ξ η + CommutingRepetition.BorelCalc.pol E hE g ξ η'
set_option linter.unusedVariables false in
axiom _root_.CommutingRepetition.BorelCalc.pol_smul_right.{w_u_1} : ∀ {𝓗 : Type w_u_1} [inst : NormedAddCommGroup 𝓗] [inst_1 : InnerProductSpace ℂ 𝓗]
  [inst_2 : CompleteSpace 𝓗] (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) {g : ℝ → ℝ},
  CommutingRepetition.BorelCalc.Bdd g →
    ∀ (c : ℂ) (ξ η : 𝓗),
      CommutingRepetition.BorelCalc.pol E hE g ξ (c • η) =
        c * CommutingRepetition.BorelCalc.pol E hE g ξ η

/-! #### Boundedness -/

set_option linter.unusedVariables false in
axiom _root_.CommutingRepetition.BorelCalc.norm_pol_le.{w_u_1} : ∀ {𝓗 : Type w_u_1} [inst : NormedAddCommGroup 𝓗] [inst_1 : InnerProductSpace ℂ 𝓗]
  [inst_2 : CompleteSpace 𝓗] (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E) {g : ℝ → ℝ},
  CommutingRepetition.BorelCalc.Bdd g →
    ∀ {C : ℝ},
      (∀ (t : ℝ), |g t| ≤ C) →
        ∀ (ξ η : 𝓗), ‖CommutingRepetition.BorelCalc.pol E hE g ξ η‖ ≤ 2 * C * ‖ξ‖ * ‖η‖
/-- The polarized form as a bounded sesquilinear map. -/
noncomputable def polForm {g : ℝ → ℝ} (hg : Bdd g) : 𝓗 →L⋆[ℂ] 𝓗 →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (pol E hE g) (pol_add_left E hE hg)
      (fun c ξ η => by rw [pol_smul_left E hE hg, smul_eq_mul]) (pol_add_right E hE hg)
      (fun c ξ η => by rw [pol_smul_right E hE hg, smul_eq_mul]; rfl))
    (2 * hg.2.choose) (fun ξ η => norm_pol_le E hE hg hg.2.choose_spec ξ η)

end Pol
/-! ### The Borel functional calculus -/
section Bfc
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)
/-- **The Borel functional calculus** `g(E)` for a bounded Borel function `g` (junk value
`0` otherwise): the operator of the polarized form of the spectral measures. -/
noncomputable def bfc (g : ℝ → ℝ) : 𝓗 →L[ℂ] 𝓗 := by
  classical
  exact if hg : Bdd g then InnerProductSpace.continuousLinearMapOfBilin (polForm E hE hg) else 0

/-! #### Linearity -/

/-! #### Multiplicativity -/

/-! #### Order -/

end Bfc
end BorelCalc
end CommutingRepetition
end

end

-- ==== Examples.vidick__MIPRE_formalization.Dependencies.v3b258185e654.MIPRE.Background.Repetition.CommutingRepetition.VN.ComplexBorel ====
public section
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/ComplexBorel.lean
-/
/-
# Complex-valued bounded Borel calculus of a self-adjoint operator (stage E4 infrastructure)

`cbfc E hE G := bfc (Re G) + i · bfc (Im G)` for bounded measurable
`G : ℝ → ℂ`, on top of the real Borel calculus `bfc` of
`VN/BorelCalculus.lean`.  Multiplicative, unital, `*`-compatible,
`⟪ξ, G(E) ξ⟫ = ∫ G dν_ξ`, `‖G(E) ξ‖² = ∫ |G|² dν_ξ`, eigenvectors
(`E ξ = c ξ ⇒ G(E) ξ = G(c) ξ`), dominated convergence, commutation and
membership in a von Neumann algebra containing `E`.  Used for the modular
group `Δ^{it} = ((2−R)/R)^{it}` of Rieffel–van Daele (`VN/Modular/ModularGroup.lean`).
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace CommutingRepetition
namespace BorelCalc
open scoped InnerProductSpace ComplexConjugate
open Filter Topology MeasureTheory
set_option linter.unusedSectionVars false
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
/-! ## Bounded measurable complex functions -/

namespace CBdd
variable {G H : ℝ → ℂ}

end CBdd
/-! ## The complex Borel calculus -/
variable (E : 𝓗 →L[ℂ] 𝓗) (hE : IsSelfAdjoint E)
/-- `G(E) := (Re G)(E) + i (Im G)(E)`. -/
noncomputable def cbfc (G : ℝ → ℂ) : 𝓗 →L[ℂ] 𝓗 :=
  bfc E hE (fun t => (G t).re) + Complex.I • bfc E hE (fun t => (G t).im)

/-! ## Eigenvectors -/

/-! ## Commutation, membership, dominated convergence -/

end BorelCalc
end CommutingRepetition
end

end

-- ==== Examples.vidick__MIPRE_formalization.Dependencies.v3b258185e654.MIPRE.Background.Repetition.CommutingRepetition.VN.Modular.CentralExp ====
public section
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/CentralExp.lean
-/
/-
# Exponentials of central elements and the perturbed vector (density stage E6.2a)

For `a ∈ M` self-adjoint in the centralizer (`[a, R] = 0`): the exponentials `e^{ra}`, the
reflected element `a' = J a J ∈ M'`, the perturbed vector `ξ = e^{-a/2} Ω` (cyclic and
separating), the transport of the standard subspace `𝒦(M, ξ) = e^{-a'/2} 𝒦(M, Ω)`, and the
unitary groups `e^{itE}` with the factorization `e^{it(b-a)} = e^{itb} e^{-ita}` for commuting
`a, b` (via the joint Borel calculus).
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace CommutingRepetition
namespace VN
namespace Modular
open scoped InnerProductSpace ComplexConjugate
open Filter Topology MeasureTheory BorelCalc ClosedSubmodule
set_option linter.unusedSectionVars false
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (M : VonNeumannAlgebra K) (Ω : K)

/-! ## `J · J` as a real star-algebra homomorphism -/

/-! ## Exponentials of a self-adjoint operator -/

section expA
variable {E : K →L[ℂ] K} (hE : IsSelfAdjoint E)

end expA
/-! ## The reflected element `a' = J a J` -/
section Central
variable {a : K →L[ℂ] K} (ha : a ∈ M) (hsa : IsSelfAdjoint a) 

/-! ## The perturbed vector `ξ = e^{-a/2} Ω` -/

/-! ## Transport of the standard subspace: `𝒦(M, ξ) = e^{-a'/2} 𝒦(M, Ω)` -/

end Central
/-! ## Unitary groups and the factorization `e^{it(b-a)} = e^{itb} e^{-ita}` -/
section UnitaryGroup
variable {E : K →L[ℂ] K} (hE : IsSelfAdjoint E)
/-- The function `l ↦ e^{itl}`. -/
noncomputable def eitf (t l : ℝ) : ℂ := Complex.exp (((t * l : ℝ) : ℂ) * Complex.I)

/-- The unitary group `e^{itE}`. -/
noncomputable def eit (E : K →L[ℂ] K) (hE : IsSelfAdjoint E) (t : ℝ) : K →L[ℂ] K :=
  cbfc E hE (eitf t)

end UnitaryGroup
/-! ## Clamped representatives of exponentials

`clamp`, `continuous_clamp`, `abs_clamp_le`, `bdd_clamp` and `clamp_eq_of_abs_le` come from
`VN/Modular/LinearRN.lean`. -/

section Pair
variable {a b : K →L[ℂ] K} (hsa : IsSelfAdjoint a) (hsb : IsSelfAdjoint b) (hab : Commute a b)

/-! ### The product rule for exponentials of a commuting pair -/
section ClampPair
variable {C : ℝ} (hCa : ‖a‖ ≤ C) (hCb : ‖b‖ ≤ C)

end ClampPair
end Pair
end Modular
end VN
end CommutingRepetition
end

end

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_66c65a791c6a0772c27f_HaarSpectrum ====
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit cfa2f1bf, 2026-09-11) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: lean/CommutingRepetition/VN/Modular/HaarSpectrum.lean
-/
/-
# The spectral measure of a Haar-distributed unitary (density stage E6.5b)

Let `E` be self-adjoint with `spectrum E ⊆ [0, 2π]`, so that `u := e^{iE}` is a unitary
with `E = −i Log u`, and let `ζ` be a vector for which the "moments" vanish,
`⟪ζ, e^{ikE} ζ⟫ = 0` for every nonzero integer `k` (HJX Lemma 2.2: this is what
`λ(2^{-n})` does to `Ω̂` in the crossed product, where `e^{ikE} = λ(k2^{-n})`).

The only consequence needed downstream is a **uniform tail estimate for the spectral
measure `ν = ν_{E,ζ}` near the branch cut**: for `0 < δ ≤ 1`,

    ν((δ, 2π−δ)ᶜ) ≤ 4 ‖ζ‖² δ ,

with a constant that does not depend on `E`. It follows from the Fejér majorant
`Q_N := 4(N+1)^{-2}|∑_{k≤N} e^{ikθ}|²`: this is a nonnegative trigonometric polynomial
which is `≥ 1` on `|θ| ≤ 1/N` (because `cos x ≥ 1 − x²/2 ≥ 1/2` there) and whose
`ν`-integral is `4‖ζ‖²/(N+1)` (because the vectors `e^{ikE}ζ` are orthonormal up to the
factor `‖ζ‖`).

Combined with `‖·‖`-approximation of the identity function by trigonometric polynomials
away from the cut, this gives `‖Eζ − P(u)ζ‖` small with `P` independent of `E`.
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Upstream builds with Lean's default `autoImplicit = true`; this repository turns it
-- off in `lakefile.toml`. Inserted by scripts/vendor-repetition.py.
set_option autoImplicit true
@[expose] public section
namespace CommutingRepetition
namespace VN
namespace Modular
open scoped InnerProductSpace ComplexConjugate Real
open Filter Topology MeasureTheory BorelCalc
set_option linter.unusedSectionVars false
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]
/-! ## Finite sums in the complex Borel calculus -/

/-! ## The Dirichlet kernel and the Fejér majorant -/

/-! ## Haar-distributed vectors -/
section Haar
variable {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (ζ : 𝓗)
/-- `ζ` is **Haar distributed** for `E`: the Fourier moments `⟪ζ, e^{ikE}ζ⟫` vanish for
every nonzero integer `k` (HJX Lemma 2.2). -/
def IsHaarVec : Prop := ∀ k : ℤ, k ≠ 0 → ⟪ζ, eit E hE (k : ℝ) ζ⟫_ℂ = 0


set_option linter.unusedVariables false in
theorem norm_sum_eit_sq (h : IsHaarVec hE ζ) (N : ℕ) 
    (h_CommutingRepetition_VN_Modular_inner_eit_eit_nat : ∀ {𝓗 : Type u_1} [inst : NormedAddCommGroup 𝓗] [inst_1 : InnerProductSpace ℂ 𝓗]
      [inst_2 : CompleteSpace 𝓗] {E : 𝓗 →L[ℂ] 𝓗} (hE : IsSelfAdjoint E) (ζ : 𝓗),
      CommutingRepetition.VN.Modular.IsHaarVec hE ζ →
        ∀ (j k : ℕ),
          Inner.inner ℂ ((CommutingRepetition.VN.Modular.eit E hE (↑j : ℝ) : 𝓗 → 𝓗) ζ)
              ((CommutingRepetition.VN.Modular.eit E hE (↑k : ℝ) : 𝓗 → 𝓗) ζ) =
            if j = k then Inner.inner ℂ ζ ζ else 0)
    :
    ‖(∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ)) ζ‖ ^ 2 = ((N : ℝ) + 1) * ‖ζ‖ ^ 2 := by
  have happ : (∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ)) ζ
      = ∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ) ζ := by
    simp
  set v := ∑ k ∈ Finset.range (N + 1), eit E hE (k : ℝ) ζ with hv
  have key : ⟪v, v⟫_ℂ = ((((N : ℝ) + 1 : ℝ)) : ℂ) * ⟪ζ, ζ⟫_ℂ := by
    calc ⟪v, v⟫_ℂ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
            ⟪eit E hE (j : ℝ) ζ, eit E hE (k : ℝ) ζ⟫_ℂ := by
          rw [hv, sum_inner]
          exact Finset.sum_congr rfl fun j _ => inner_sum _ _ _
      _ = ∑ _j ∈ Finset.range (N + 1), ⟪ζ, ζ⟫_ℂ := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.sum_congr rfl fun k _ => h_CommutingRepetition_VN_Modular_inner_eit_eit_nat hE ζ h j k,
            Finset.sum_ite_eq (Finset.range (N + 1)) j fun _ => ⟪ζ, ζ⟫_ℂ, if_pos hj]
      _ = ((((N : ℝ) + 1 : ℝ)) : ℂ) * ⟪ζ, ζ⟫_ℂ := by
          rw [Finset.sum_const, Finset.card_range]
          push_cast
          ring
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul] at hre
  rw [happ, ← inner_self_eq_norm_sq (𝕜 := ℂ) v, ← inner_self_eq_norm_sq (𝕜 := ℂ) ζ]
  exact hre

/-! ## From the tail estimate to an operator estimate -/

end Haar
/-! ## Trigonometric approximation of the identity away from the branch cut -/
section Trig

section RampFacts
variable {δ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ < 2 * π)
include hδ0 hδ2

end RampFacts

end Trig
section ExpSeries
end ExpSeries
end Modular
end VN
end CommutingRepetition
end
