/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Weak derivatives

A function `u : E → F` has weak derivative `g` along `v` on an open set `Ω` when both are locally
integrable on `Ω` and the distributional derivative `∂_{v}` of `u` is the distribution of `g`.
It has weak Fréchet derivative `G : E → E →L[ℝ] F` when this holds along every direction with
`g = (G · v)`. Both are phrased through Mathlib's `Distribution.ofFun` and the line derivative
of distributions, so that uniqueness is `Distribution.ofFun_injective` and linearity is that of
`∂_{v}`.

`E` is any finite-dimensional real normed space where it matters (uniqueness, smooth functions),
`F` any real normed space (complete for uniqueness), `μ` any measure (an additive Haar measure
for the smooth case). The open set is an `Opens E`, which is how Mathlib indexes test functions
and distributions; a set with a proof of openness enters as `⟨Ω, hΩ⟩`.

## Main declarations

* `EllipticPdes.HasWeakLineDerivOn`: weak derivative along one direction.
* `EllipticPdes.HasWeakFDerivOn`: weak Fréchet derivative.
* `EllipticPdes.hasWeakLineDerivOn_iff`: the integration by parts form, against smooth
  compactly supported functions.
* `EllipticPdes.HasWeakLineDerivOn.ae_eq`, `EllipticPdes.HasWeakFDerivOn.ae_eq`: uniqueness
  almost everywhere on `Ω`.
* `EllipticPdes.HasWeakFDerivOn.of_basis`: a weak derivative along each vector of a basis is a
  weak Fréchet derivative.
* `EllipticPdes.hasWeakFDerivOn_fderiv`: a `C¹` function has its derivative as weak derivative.
-/
@[expose] public section
open MeasureTheory TopologicalSpace Set Filter
open scoped Distributions LineDeriv
noncomputable section
namespace EllipticPdes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω Ω' : Opens E} {μ : Measure E} {v w : E} {u u' g g' : E → F} {G G' : E → E →L[ℝ] F}
/-- `g` is the weak derivative of `u` along `v` on the open set `Ω`: `u` and `g` are locally
integrable on `Ω` and the derivative of the distribution of `u` along `v` is the distribution
of `g`. In integral form, `∫ ∂_{v} φ • u ∂μ = -∫ φ • g ∂μ` for every test function `φ` on `Ω`
(`hasWeakLineDerivOn_iff`). -/
def HasWeakLineDerivOn (Ω : Opens E) (v : E) (u g : E → F) (μ : Measure E := by volume_tac) :
    Prop :=
  LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn g Ω μ ∧
    ∂_{v} (Distribution.ofFun Ω u μ ⊤) = Distribution.ofFun Ω g μ ⊤
/-- `G` is the weak Fréchet derivative of `u` on the open set `Ω`: for every direction `v`, the
function `x ↦ G x v` is the weak derivative of `u` along `v`. -/
def HasWeakFDerivOn (Ω : Opens E) (u : E → F) (G : E → E →L[ℝ] F)
    (μ : Measure E := by volume_tac) : Prop :=
  ∀ v, HasWeakLineDerivOn Ω v u (fun x => G x v) μ
/-! ### The integral form -/
/-- The derivative along `v` of the distribution of a locally integrable function, evaluated on
a test function, is minus the integral against the derivative of the test function. -/
theorem lineDerivOp_ofFun_apply (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, ℝ)) :
    ∂_{v} (Distribution.ofFun Ω u μ ⊤) φ = -∫ x, fderiv ℝ φ x v • u x ∂μ := by
  rw [Distribution.lineDerivOp_apply_apply, Distribution.ofFun_apply hu, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hd := (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv (v := v)
  simp [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, hd]
/-- **Weak derivative as integration by parts.** `g` is the weak derivative of `u` along `v` on
`Ω` if and only if both are locally integrable on `Ω` and `∫ ∂_{v} φ • u = -∫ φ • g` for every
smooth function `φ` with compact support in `Ω`. -/
theorem hasWeakLineDerivOn_iff : HasWeakLineDerivOn Ω v u g μ ↔
    LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn g Ω μ ∧
      ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • g x ∂μ := by
  refine and_congr_right fun hu => and_congr_right fun hg => ?_
  have key : ∀ φ : 𝓓(Ω, ℝ), (∂_{v} (Distribution.ofFun Ω u μ ⊤) φ =
      Distribution.ofFun Ω g μ ⊤ φ ↔ ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • g x ∂μ) :=
    fun φ => by rw [lineDerivOp_ofFun_apply hu, Distribution.ofFun_apply hg, neg_eq_iff_eq_neg]
  refine ⟨fun h φ hφ hc hs => (key ⟨φ, hφ, hc, hs⟩).1 congr($h _), fun h => ?_⟩
  ext φ
  exact (key φ).2 (h φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset)
/-- The integration by parts identity of a weak derivative, against a smooth function with
compact support in `Ω`. -/
theorem HasWeakLineDerivOn.integral_eq (h : HasWeakLineDerivOn Ω v u g μ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∫ x, fderiv ℝ φ x v • u x ∂μ = -∫ x, φ x • g x ∂μ :=
  (hasWeakLineDerivOn_iff.1 h).2.2 φ hφ hc hs
section Unique
variable [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
end Unique
/-! ### Algebraic operations -/
theorem HasWeakLineDerivOn.add (h : HasWeakLineDerivOn Ω v u g μ)
    (h' : HasWeakLineDerivOn Ω v u' g' μ) : HasWeakLineDerivOn Ω v (u + u') (g + g') μ :=
  ⟨h.1.add h'.1, h.2.1.add h'.2.1, by
    rw [Distribution.ofFun_add h.1 h'.1, Distribution.ofFun_add h.2.1 h'.2.1,
      LineDeriv.lineDerivOp_add, h.2.2, h'.2.2]⟩
/-- Weak Fréchet derivatives add. -/
theorem HasWeakFDerivOn.add (h : HasWeakFDerivOn Ω u G μ) (h' : HasWeakFDerivOn Ω u' G' μ) :
    HasWeakFDerivOn Ω (u + u') (G + G') μ :=
  fun v => (h v).add (h' v)
/-- A constant multiple of a function has the same multiple of its weak derivative. -/
theorem HasWeakLineDerivOn.const_smul (h : HasWeakLineDerivOn Ω v u g μ) (c : ℝ) :
    HasWeakLineDerivOn Ω v (c • u) (c • g) μ :=
  ⟨h.1.smul c, h.2.1.smul c, by
    rw [Distribution.ofFun_smul, Distribution.ofFun_smul, LineDeriv.lineDerivOp_smul, h.2.2]⟩
/-- A constant multiple of a function has the same multiple of its weak Fréchet derivative. -/
theorem HasWeakFDerivOn.const_smul (h : HasWeakFDerivOn Ω u G μ) (c : ℝ) :
    HasWeakFDerivOn Ω (c • u) (c • G) μ :=
  fun v => (h v).const_smul c
/-- The negative of a function has the negative weak derivative. -/
theorem HasWeakLineDerivOn.neg (h : HasWeakLineDerivOn Ω v u g μ) :
    HasWeakLineDerivOn Ω v (-u) (-g) μ := by
  simpa using h.const_smul (-1)
/-- The negative of a function has the negative weak Fréchet derivative. -/
theorem HasWeakFDerivOn.neg (h : HasWeakFDerivOn Ω u G μ) : HasWeakFDerivOn Ω (-u) (-G) μ :=
  fun v => (h v).neg
/-- Weak derivatives subtract. -/
theorem HasWeakLineDerivOn.sub (h : HasWeakLineDerivOn Ω v u g μ)
    (h' : HasWeakLineDerivOn Ω v u' g' μ) : HasWeakLineDerivOn Ω v (u - u') (g - g') μ := by
  simpa [sub_eq_add_neg] using h.add h'.neg
/-- Weak Fréchet derivatives subtract. -/
theorem HasWeakFDerivOn.sub (h : HasWeakFDerivOn Ω u G μ) (h' : HasWeakFDerivOn Ω u' G' μ) :
    HasWeakFDerivOn Ω (u - u') (G - G') μ :=
  fun v => (h v).sub (h' v)
theorem HasWeakLineDerivOn.mono (h : HasWeakLineDerivOn Ω v u g μ) (hΩ : Ω' ≤ Ω) :
    HasWeakLineDerivOn Ω' v u g μ := by
  obtain ⟨hu, hg, hint⟩ := hasWeakLineDerivOn_iff.1 h
  exact hasWeakLineDerivOn_iff.2 ⟨hu.mono_set hΩ, hg.mono_set hΩ,
    fun φ hφ hc hs => hint φ hφ hc (hs.trans hΩ)⟩
/-- A weak Fréchet derivative on `Ω` is one on any smaller open set. -/
theorem HasWeakFDerivOn.mono (h : HasWeakFDerivOn Ω u G μ) (hΩ : Ω' ≤ Ω) :
    HasWeakFDerivOn Ω' u G μ :=
  fun v => (h v).mono hΩ
/-! ### Smooth functions -/
section Smooth
variable [BorelSpace E] [FiniteDimensional ℝ E]
variable [μ.IsAddHaarMeasure]
end Smooth
end EllipticPdes
