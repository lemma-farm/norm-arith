/-
Copyright (c) 2026 Yuhao Lei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuhao Lei
-/
module
public import Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.v844a6559ba7d.SharpWasserstein.Sharp.SmoothCoefficients
public import Examples.yuhaolei_ctrl__Sharp_W2_to_W2_Propagation_of_Chaos.Dependencies.v844a6559ba7d.SharpWasserstein.PeriodicParticleApproximation
/-!
# Split drift/interaction pairs with Euclidean constants

Section 5 of the paper treats the one-body drift `a` and the interaction `K` separately: the
drift of level `m` of the hierarchy is `b^{[m]}_i(x) = a(xᵢ) + N⁻¹ ∑_{j ≤ m} K(xᵢ, xⱼ)` and the
external operator is `Φψ(x, y) = ∑ᵢ K(xᵢ, y) · ∇ᵢψ(x)` (`eq:Bm-Phi`). The constants of
Lemma 5.2 (`lem:pointwise`) are the Euclidean constants `L_a, L₁, L₂, M` of Assumption A.

This file packages the hypotheses used by the sharp hierarchy in the predicate `SplitKernel`:
Assumption A for the Euclidean conjugates, and qualitative smoothness with bounded derivatives
of `a` and `K` separately. It derives the Euclidean first-derivative bounds used in Lemma 5.2,
shows that `IsSmoothCoefficients` implies `SplitKernel`, and that the predicate (with the same
constants) is preserved by the coordinatewise sine periodization used to reduce to periodic
coefficients.

## Main definitions

* `oneBodyKernel a`: the drift `a` as a kernel `(x, y) ↦ a x`.
* `SplitKernel a K La L₁ L₂ M`.

## Main statements

* `SplitKernel.norm_toLp_fderiv_first_le`, `SplitKernel.norm_toLp_fderiv_second_le`,
  `SplitKernel.norm_toLp_K_le`: `‖D_x K‖ ≤ L₁`, `‖D_y K‖ ≤ L₂`, `|K| ≤ M` in Euclidean norms.
* `SplitKernel.of_smooth`: smooth coefficients (`IsSmoothCoefficients`) form a split pair.
* `SplitKernel.sine`, `sine_oneBody_periodic`: the sine-periodized pair.
-/
@[expose] public section
noncomputable section
open scoped ContDiff
namespace SharpWasserstein.Sharp.Hierarchy
variable {d : ℕ}
/-- The one-body drift `a`, regarded as a kernel that ignores its second argument. -/
def oneBodyKernel (a : Position d → Position d) : Position d → Position d → Position d :=
  fun x _ => a x
/-- A split pair `(a, K)` for the sharp hierarchy: Assumption A for the Euclidean conjugates with
constants `La, L₁, L₂, M`, and smoothness with bounded derivatives of all orders of `a` and of
`K` separately. -/
structure SplitKernel (a : Position d → Position d) (K : Position d → Position d → Position d)
    (La L₁ L₂ M : ℝ) : Prop where
  assumptionA : SharpChaos.AssumptionA (euclidMap a) (euclidMap₂ K) La L₁ L₂ M
  smooth_a : BoundedSmoothKernel (oneBodyKernel a)
  smooth_K : BoundedSmoothKernel K
/-! ### Euclidean first-derivative bounds -/
/-- A differentiable map on coordinates whose Euclidean conjugate is `L`-Lipschitz has a
derivative of Euclidean operator norm at most `L`. -/
theorem norm_toLp_fderiv_le {f : Position d → Position d} {L : ℝ} (hL : 0 ≤ L)
    (hf : Differentiable ℝ f)
    (hlip : ∀ x x', ‖euclidMap f x - euclidMap f x'‖ ≤ L * ‖x - x'‖) (x u : Position d) :
    ‖WithLp.toLp 2 (fderiv ℝ f x u)‖ ≤ L * ‖WithLp.toLp 2 u‖ := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hl : LipschitzWith ⟨L, hL⟩ (euclidMap f) :=
    LipschitzWith.of_dist_le_mul fun x x' => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip x x'
  have hd : HasFDerivAt (euclidMap f)
      (e.symm.toContinuousLinearMap.comp ((fderiv ℝ f x).comp e.toContinuousLinearMap))
      (WithLp.toLp 2 x) := by
    have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => f (e y))
        ((fderiv ℝ f x).comp e.toContinuousLinearMap) (WithLp.toLp 2 x) :=
      (hf x).hasFDerivAt.comp _ e.hasFDerivAt
    exact e.symm.hasFDerivAt.comp _ h1
  have hn := norm_fderiv_le_of_lipschitz ℝ hl (x₀ := WithLp.toLp 2 x)
  rw [hd.fderiv] at hn
  exact (ContinuousLinearMap.le_opNorm _ (WithLp.toLp 2 u)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
namespace SplitKernel
end SplitKernel
section SmoothCoefficients
end SmoothCoefficients
namespace SplitKernel
end SplitKernel
end SharpWasserstein.Sharp.Hierarchy
