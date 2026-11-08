/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module
public import Examples.alejandro_soto_franco__EllipticPDE.Dependencies.ve6742b225530.EllipticPdes.Sobolev.Basic
public import Examples.alejandro_soto_franco__EllipticPDE.Dependencies.ve6742b225530.EllipticPdes.Sobolev.WeakDeriv
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Average
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Pointwise weak gradients on a set

## Main declarations

* `EllipticPdes.Embedding.HasWeakGradOn`: the weak gradient of a function on a set.
* `EllipticPdes.Embedding.HasWeakDerivAlong`: the weak derivative along a direction of any normed
  space.
* `EllipticPdes.Embedding.hasWeakGradOn_iff`: a weak gradient is a family of weak derivatives.
* `EllipticPdes.Embedding.HasWeakDerivAlong.comp_affine`: transport through `x ↦ e x + c`.
* `EllipticPdes.Embedding.HasWeakDerivAlong.sum`: a weak derivative is linear in the direction.

The `Lᵖ`-scale, pointwise-function analogue of `HasWeakDerivOn`: a function `u` has weak
gradient `g = (gₖ)` on `B` when the integration by parts identity is satisfied against every
smooth test function supported in `B`. This is the interface the Morrey embedding consumes; it is
stated for functions (not `Lp` classes) and for a full gradient tuple so that a
general exponent `p > d` is expressible, which the `L²`-only `HasWeakDerivOn` cannot do.
-/
@[expose] public section
open MeasureTheory Set Metric
open scoped NNReal RealInnerProductSpace
noncomputable section
namespace EllipticPdes.Embedding
open EllipticPdes.Sobolev (partialD)
variable {d : ℕ}
/-- **Integrability against a bounded factor.** An integrable class stays integrable when
multiplied by a bounded measurable one, which is how every test function and every cutoff of
this development enters an integral. -/
theorem integrableOn_mul_bounded {B : Set (EuclideanSpace ℝ (Fin d))}
    {w h : EuclideanSpace ℝ (Fin d) → ℝ} (hw : IntegrableOn w B volume) (hc : Continuous h)
    {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) : IntegrableOn (fun x => w x * h x) B volume := by
  have hbd := hw.bdd_mul (f := h) hc.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  exact hbd.congr (Filter.Eventually.of_forall fun x => mul_comm (h x) (w x))
/-- `g` is the pointwise weak gradient of `u` on `B`: integration by parts holds
against every smooth compactly supported test function whose support lies in `B`. This
mirrors `EllipticPdes.Regularity.HasWeakDerivOn` component-wise but for pointwise
functions `u, gₖ : EuclideanSpace ℝ (Fin d) → ℝ`. -/
def HasWeakGradOn (B : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ B → ∀ k : Fin d,
      ∫ x in B, u x * partialD k φ x = - ∫ x in B, g k x * φ x
/-! ### Gradient tuple as a functional -/
theorem HasWeakGradOn.const_mul {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (c : ℝ)
    (h : HasWeakGradOn B u g) :
    HasWeakGradOn B (fun x => c * u x) (fun k x => c * g k x) := by
  intro φ hφc hφcs hφs k
  have e := h φ hφc hφcs hφs k
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, e, mul_neg]
/-- **Additivity of a weak gradient.** Two classes with weak gradients on the same set add, and
so do their gradients. The finite sum of local pieces the extension operator glues is built by
iterating this. -/
theorem HasWeakGradOn.add {B : Set (EuclideanSpace ℝ (Fin d))}
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} {g h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hv : IntegrableOn v B volume)
    (hg : ∀ k, IntegrableOn (g k) B volume) (hh : ∀ k, IntegrableOn (h k) B volume)
    (hU : HasWeakGradOn B u g) (hV : HasWeakGradOn B v h) :
    HasWeakGradOn B (fun x => u x + v x) (fun k x => g k x + h k x) := by
  intro φ hφc hφcs hφs k
  have hφcont : Continuous φ := hφc.continuous
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφpcs : HasCompactSupport (partialD k φ) :=
    hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  obtain ⟨N, hN⟩ := hφpcs.exists_bound_of_continuous hφpc
  obtain ⟨P, hP⟩ := hφcs.exists_bound_of_continuous hφcont
  have hL : ∫ x in B, (u x + v x) * partialD k φ x
      = (∫ x in B, u x * partialD k φ x) + ∫ x in B, v x * partialD k φ x := by
    rw [← integral_add (integrableOn_mul_bounded hu hφpc hN)
      (integrableOn_mul_bounded hv hφpc hN)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hR : ∫ x in B, (g k x + h k x) * φ x
      = (∫ x in B, g k x * φ x) + ∫ x in B, h k x * φ x := by
    rw [← integral_add (integrableOn_mul_bounded (hg k) hφcont hP)
      (integrableOn_mul_bounded (hh k) hφcont hP)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hL, hR, hU φ hφc hφcs hφs k, hV φ hφc hφcs hφs k]
  ring
section WeakDeriv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}
/-- **Weak derivative along a direction.** `g` is the weak derivative of `u` along `v` on `B`
when `∫_B u ∂_v φ = -∫_B g φ` for every smooth test function `φ` supported in `B`. -/
def HasWeakDerivAlong (μ : Measure E) (v : E) (B : Set E) (u g : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ B →
    ∫ x in B, u x * fderiv ℝ φ x v ∂μ = -∫ x in B, g x * φ x ∂μ
theorem HasWeakDerivAlong.smul {v : E} {B : Set E} {u g : E → ℝ}
    (h : HasWeakDerivAlong μ v B u g) (c : ℝ) :
    HasWeakDerivAlong μ (c • v) B u (fun x => c * g x) := by
  intro φ hφ hc hs
  have : ∀ x, u x * fderiv ℝ φ x (c • v) = c * (u x * fderiv ℝ φ x v) := fun x => by
    simp only [map_smul, smul_eq_mul]; ring
  simp_rw [this, mul_assoc]
  rw [integral_const_mul, integral_const_mul, h φ hφ hc hs, mul_neg]
end WeakDeriv
end EllipticPdes.Embedding
