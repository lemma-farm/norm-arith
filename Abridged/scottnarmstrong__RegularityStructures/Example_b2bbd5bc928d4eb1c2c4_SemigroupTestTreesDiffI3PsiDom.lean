module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.RegularityStructures.Torus.Basic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The three-torus and space-time

We write `T³ = ℝ³/ℤ³` as `UnitAddTorus (Fin 3)` and space-time `ℝ × T³` as a product. Points of
`ℝ³` are functions `Fin 3 → ℝ`, with the Euclidean square norm written out by hand. A function on
the torus is smooth if its periodic lift to `ℝ³` is smooth.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open scoped ContDiff
namespace RegularityStructures
/-- The three-torus `T³ = ℝ³/ℤ³`. -/
abbrev Torus3 : Type := UnitAddTorus (Fin 3)
/-- Space-time `ℝ × T³`. -/
abbrev SpaceTime : Type := ℝ × Torus3
def torusRep (x : Torus3) : Fin 3 → ℝ := fun i => (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)
/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.RegularityStructures.Torus.KernelBoundsBasic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Parabolic size on space-time over `T³`

The singular estimates for the massive heat kernel use the parabolic size
`|z|_s = |t|^(1/2) + |x|`, with the spatial point represented in the centred fundamental cube
`[-1/2,1/2)^3`.  The representative is defined here rather than changing the existing `[0,1)`
representative used by `heatKernel`.

Sources: [Hai14] = arXiv:1303.5113v4, §2 and Assumption 5.1; [Hos25] = arXiv:2310.07396v2, §2.1.
-/
@[expose] public noncomputable section
open Real Set
namespace RegularityStructures
/-- The centred representative of a point of `T³`, in `[-1/2,1/2)³`. -/
def torusCenteredRep (x : Torus3) : Fin 3 → ℝ := fun i =>
  if (1 / 2 : ℝ) ≤ torusRep x i then torusRep x i - 1 else torusRep x i
/-- The Euclidean spatial norm of the centred representative. -/
def torusSpatialNorm (x : Torus3) : ℝ := √(sqNorm3 (torusCenteredRep x))
/-- The parabolic size of a space-time point. -/
def torusParabolicSize (z : SpaceTime) : ℝ :=
  √|z.1| + torusSpatialNorm z.2

axiom torusParabolicSize_nonneg (z : SpaceTime) : 0 ≤ torusParabolicSize z
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiPowers ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Integrals of products of two centred parabolic powers

For a centre `c` and exponent `a`, `singularPow a c w = s(c - w)^(-a)`.  If `0 < a, b < 5` and
`a + b > 5`, the product `singularPow a p * singularPow b q` is integrable and its integral is
at most `C * s(p - q)^(5 - a - b)` (the whole-space convolution estimate of [Hai14, Lemma 10.14],
in the form with two arbitrary centres, together with integrability of the integrand).

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14, (10.37a).
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- The parabolic power weight `s(c - w)^(-a)` centred at `c`. -/
def singularPow (a : ℝ) (c w : SpaceTime) : ℝ := torusParabolicSize (c - w) ^ (-a)
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
axiom singularPow_nonneg (a : ℝ) (c w : SpaceTime) : 0 ≤ singularPow a c w
axiom singularPow_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p q w : SpaceTime}
    (hp : 0 < torusParabolicSize (p - w)) (hq : 0 < torusParabolicSize (q - w)) :
    singularPow a p w * singularPow b q w ≤
      singularPow (a + b) p w + singularPow (a + b) q w
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiPointwise ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Pointwise bounds for the recentred kernel and the covariance

For abstract functions `K` (order `-3` with increments of order `-4`, time support `|t| ≤ 1`)
and `Q` (order `-1`, time support `|t| ≤ 2`) we bound, in terms of centred powers
`singularPow`,

* the recentred kernel `δK(z, w) = K(z - w) - K(-w)`, with and without a Hölder gain
  `s(z)^θ`;
* the covariance at a flipped argument, `|Q(w - u)| ≤ 2 B s(u - w)⁻¹`;
* the square and the cube of the covariance, the square with a loss `δ` of the exponent.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.18 and p. 167--168.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
/-- Trivial bound for the recentred kernel. -/
axiom abs_dK_le {K : SpaceTime → ℝ} {B : ℝ}
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    {z w : SpaceTime} (hz : 0 < torusParabolicSize (z - w))
    (h0 : 0 < torusParabolicSize (0 - w)) :
    |K (z - w) - K (-w)| ≤ B * (singularPow 3 z w + singularPow 3 0 w)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.SemigroupTestTreesI3PsiChain ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The chain diagram of `I(Ψ³)Ψ`, for arbitrary `z, z'`

`i3PsiChain_bound_global`: for kernels `K, Q` with `|K| ≤ B s^(-3)`, `K = 0` for `|t| > 1`,
`|Q| ≤ B s^(-1)` (no support condition on `Q`), all `z, z'` with `z, z', z - z'` away from the
origin, and `D` bounding `s(w - v)` on the slab `|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`,
`|∫∫ chain| ≤ C D^δ (s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ))`.
There is no smallness assumption on `z, z'`: the recentred kernels `K(z - ·) - K(-·)` vanish
outside the slab, and on the slab `Q(w - v)² ≤ B² D^δ s(w - v)^(-2-δ)`.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
axiom dK_eq_zero_of_abs_lt {K : SpaceTime → ℝ} (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    {z w : SpaceTime} (hw : |z.1| + 1 < |w.1|) : K (z - w) - K (-w) = 0
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiDiagramMultiChain ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The chain majorant with general exponents

The chain diagram of `I(Ψ³)Ψ` is dominated by
`(s₃(z,w) + s₃(0,w)) s_{1+α}(u,w) · (s_{4+γ}(z',v) + s_{4+γ}(0,v) + 2 s_{4+γ}(u',v)) s_{2+β}(w,v)`
(`s_a(c, w) = s(c - w)^(-a)`), which has the three exponents `α` (outer covariance), `β` (loss in
`Q²`) and `γ` (the covariance next to `δK(z', v)`) in place of `0, δ, 0`.  For `u = z, u' = z'`
(chaos-two pairing) or `u = z', u' = z` (secondary pairing) its double integral is bounded by
`C (s(z - z')^(-η) + s(z)^(-η) + s(z')^(-η))` with `η = α + β + γ`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- The chain majorant with exponents `α, β, γ`. -/
def i3PsiChainMajorant (α β γ : ℝ) (z z' u u' w v : SpaceTime) : ℝ :=
  ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) *
    ((singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v + 2 * singularPow (4 + γ) u' v) *
      singularPow (2 + β) w v)
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiDiagramMultiPointwise ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Pointwise domination by the chain and principal majorants

For the kernel `K` of order `-3`, supported in `|t| ≤ 1`, and `s(z), s(z') ≤ 1`:

* `abs_dK_dK_chain_le`: `|δK(z,w)| |δK(z',v)| · s_{1+α}(u,w) s(w-v)^(-(2+β₀)) s_{1+γ}(u',v)` is bounded
  by `B² 3^δ` times `i3PsiChainMajorant α (β₀ + δ) γ`;
* `abs_dK_dK_principal_le`: `|δK(z,w)| |δK(z',v)| · s_{3+τ}(w,v)` is bounded by
  `12 B² s(z')^θ` times `i3PsiPrincipalMajorant θ τ`.

`singularPow_flip_le` converts `s(w - u)^(-a)` to the centred power `s_a(u, w)`.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
axiom i3PsiChainMajorant_nonneg (α β γ : ℝ) (z z' u u' w v : SpaceTime) :
    0 ≤ i3PsiChainMajorant α β γ z z' u u' w v
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_b2bbd5bc928d4eb1c2c4_SemigroupTestTreesDiffI3PsiDom ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Global chain domination for the cross-mollifier difference of `I(Ψ³)Ψ`

Global versions of `abs_dK_dK_chain_le`, `abs_dK_dK_chain_flip_le` and
`abs_dK_dK_chain_flip_left_le`: the hypotheses `s(z), s(z') ≤ 1` (which are used only to restrict
to the slab `|w.1| ≤ 2` carrying the support of the recentred kernel `K(z - ·) - K(-·)` and to
bound `s(w - v) ≤ 3` there) are replaced by an explicit bound `s(w - v) ≤ D` on the slab
`|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`, and `3 ^ δ` by `D ^ δ`.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
/-- **Global chain domination.** -/
theorem abs_dK_dK_chain_le_global_i3Psi {K : SpaceTime → ℝ} {B δ α β₀ γ D : ℝ} (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hD0 : 0 ≤ D)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' u u' w v : SpaceTime}
    (hD : ∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
      torusParabolicSize (w - v) ≤ D)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
          singularPow (1 + γ) u' v) ≤
      B ^ 2 * D ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v := by
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hrhs := i3PsiChainMajorant_nonneg α (β₀ + δ) γ z z' u u' w v
  have hrhs' : 0 ≤ B ^ 2 * D ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v :=
    mul_nonneg (mul_nonneg (sq_nonneg B) n3) hrhs
  by_cases hw : |w.1| ≤ |z.1| + 1
  · by_cases hv : |v.1| ≤ |z'.1| + 1
    · have a := abs_dK_le hK h1 h0
      have b := abs_dK_le hK h1' h0'
      have e1 := singularPow_mul_le (a := 3) (b := 1 + γ) (by norm_num) (by linarith) h1' hu'
      have e2 := singularPow_mul_le (a := 3) (b := 1 + γ) (by norm_num) (by linarith) h0' hu'
      have e : (3 : ℝ) + (1 + γ) = 4 + γ := by ring
      rw [e] at e1 e2
      have nσ := singularPow_nonneg (1 + α) u w
      have nσ' := singularPow_nonneg (1 + γ) u' v
      have hL : |K (z - w) - K (-w)| * singularPow (1 + α) u w ≤
          B * ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) := by
        have := mul_le_mul_of_nonneg_right a nσ
        linarith
      have hR : |K (z' - v) - K (-v)| * singularPow (1 + γ) u' v ≤
          B * (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
            2 * singularPow (4 + γ) u' v) := by
        have := mul_le_mul_of_nonneg_right b nσ'
        have h5 : B * (singularPow 3 z' v + singularPow 3 0 v) * singularPow (1 + γ) u' v ≤
            B * (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
              2 * singularPow (4 + γ) u' v) := by
          have := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hB
          nlinarith [this]
        linarith
      have hC : torusParabolicSize (w - v) ^ (-(2 + β₀)) ≤
          D ^ δ * singularPow (2 + (β₀ + δ)) w v := by
        have hpow : torusParabolicSize (w - v) ^ (-(2 + β₀)) =
            torusParabolicSize (w - v) ^ δ * singularPow (2 + (β₀ + δ)) w v := by
          unfold singularPow
          rw [← Real.rpow_add hwv]; congr 1; ring
        rw [hpow]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hwv.le (hD w v hw hv) hδ)
          (singularPow_nonneg _ _ _)
      have nLeft : 0 ≤ B * ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) :=
        mul_nonneg hB (mul_nonneg (add_nonneg (singularPow_nonneg _ _ _)
          (singularPow_nonneg _ _ _)) nσ)
      have nRight : 0 ≤ B * (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
          2 * singularPow (4 + γ) u' v) :=
        mul_nonneg hB (add_nonneg (add_nonneg (singularPow_nonneg _ _ _)
          (singularPow_nonneg _ _ _)) (mul_nonneg (by norm_num) (singularPow_nonneg _ _ _)))
      have key : (|K (z - w) - K (-w)| * singularPow (1 + α) u w) *
          (|K (z' - v) - K (-v)| * singularPow (1 + γ) u' v) *
          torusParabolicSize (w - v) ^ (-(2 + β₀)) ≤
          (B * ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w)) *
          (B * (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
            2 * singularPow (4 + γ) u' v)) * (D ^ δ * singularPow (2 + (β₀ + δ)) w v) :=
        mul_le_mul (mul_le_mul hL hR (mul_nonneg (abs_nonneg _) nσ') nLeft) hC
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _) (mul_nonneg nLeft nRight)
      refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
      · ring
      · unfold i3PsiChainMajorant
        ring
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hv)
      rw [this, abs_zero]
      simpa using hrhs'
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hw)
    rw [this, abs_zero]
    simpa using hrhs'
end RegularityStructures
end
