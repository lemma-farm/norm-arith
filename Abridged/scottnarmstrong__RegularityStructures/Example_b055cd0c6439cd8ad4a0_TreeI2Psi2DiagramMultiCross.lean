module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.RegularityStructures.Torus.Basic ====
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

/-- The representative of a point of `T³` in `[0, 1)³`. -/
def torusRep (x : Torus3) : Fin 3 → ℝ := fun i => (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)
/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.RegularityStructures.BPHZ.TreeI2Psi2DiagramLint ====
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
# Lower-integral bounds: a small calculus

`i2Psi2LintBound μ f M` says `∫⁻ ofReal (f a) ∂μ ≤ ofReal M`.  It is the form in which the
singular-integral estimates of the tree `I(Ψ²) Ψ²` ([Hai14, (10.39)-(10.42)]) are chained: it needs
no integrability bookkeeping, is monotone, additive, scales by constants, and passes through
Tonelli (`i2Psi2LintBound.of_prod_symm`) and products of independent factors.  The final
`abs_integral_le_of_i2Psi2LintBound` turns such a bound on `|f|` into integrability of `f` and a
bound on `|∫ f|`.
-/
@[expose] public section
open MeasureTheory
namespace RegularityStructures
/-- `f` has lower integral at most `M`: `∫⁻ ofReal (f a) ∂μ ≤ ofReal M`. -/
def i2Psi2LintBound {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (M : ℝ) :
    Prop :=
  ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal M
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

axiom i2Psi2LintBound.mono {f g : α → ℝ} {M M' : ℝ}
    (h : i2Psi2LintBound μ g M) (hfg : ∀ a, f a ≤ g a) (hM : M ≤ M') :
    i2Psi2LintBound μ f M'

axiom i2Psi2LintBound.add_three {f g h : α → ℝ} {M N P : ℝ} (hf : Measurable f)
    (hg : Measurable g) (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a) (hh0 : ∀ a, 0 ≤ h a)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP : 0 ≤ P) (hfM : i2Psi2LintBound μ f M)
    (hgN : i2Psi2LintBound μ g N) (hhP : i2Psi2LintBound μ h P) :
    i2Psi2LintBound μ (fun a => f a + g a + h a) (M + N + P)
axiom i2Psi2LintBound.const_mul {f : α → ℝ} {M c : ℝ} (hc : 0 ≤ c)
    (h : i2Psi2LintBound μ f M) : i2Psi2LintBound μ (fun a => c * f a) (c * M)
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
/-- Tonelli, integrating first over the first variable. -/
axiom i2Psi2LintBound.of_prod_symm [SFinite μ] [SFinite ν] {F : α × β → ℝ}
    (hF : Measurable F) {G : β → ℝ} {M : ℝ}
    (h1 : ∀ᵐ b ∂ν, i2Psi2LintBound μ (fun a => F (a, b)) (G b))
    (h2 : i2Psi2LintBound ν G M) : i2Psi2LintBound (μ.prod ν) F M
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.RegularityStructures.Torus.KernelBoundsBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.Torus.KernelBoundsCovariance ====
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
# Parabolic volume and covariance bounds

The covariance estimate uses the homogeneous dimension five of space-time.
-/
@[expose] public noncomputable section
open MeasureTheory Set Metric
namespace RegularityStructures
namespace Phi43

axiom measurable_torusParabolicSize : Measurable torusParabolicSize

end Phi43
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.KernelCalculusBasic ====
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
# Pointwise inequalities for parabolic powers

The Young-type inequalities (10.37a)--(10.37b) of [Hai14] for the parabolic size
`s = torusParabolicSize` on space-time, together with the quasi-triangle inequalities used
throughout the kernel calculus (`s(u + h) ≤ 4 (s u + s h)`, `s(-w) ≤ 2 s w`) and
almost-everywhere positivity of `s`.

Source: [Hai14] = arXiv:1303.5113v4, (10.37), p. 168.
-/
public section
open MeasureTheory Set
namespace RegularityStructures

axiom ae_torusParabolicSize_sub_pos (z : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, 0 < torusParabolicSize (z - w)

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.TreeI2Psi2DiagramBounded ====
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
# Bounded integrals of products of singular weights over a time slab

All the variables of the diagram integrals of the tree `I(Ψ²) Ψ²` lie in a time slab
`|t - τ| ≤ 2` (the kernels `K` are supported in `|t| ≤ 1` and the base points are within
distance `1` of `τ`).  On the slab every parabolic distance to a point of the slab is at most `3`,
so a product of weights `s(pᵢ - w)^(-λᵢ)` with total exponent `λ₁ + λ₂ + λ₃ < 5` has a bounded
integral: `i2Psi2LintBound_slab_triple`, [Hai14, (10.37a), Lemma 10.14].
-/
@[expose] public noncomputable section
namespace RegularityStructures

end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures

axiom measurable_torusParabolicSize_sub_rpow (p : SpaceTime) (e : ℝ) :
    Measurable fun w : SpaceTime => torusParabolicSize (p - w) ^ e

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.TreeI2Psi2DiagramInner ====
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
# Integrals of the kernel increment against singular weights

With `A(w) = K(y - w) - K(x - w)` and `r = s(y - x)`:

* `i2Psi2LintBound_kernel_sub_two`: `∫ |A(w)| s(g - w)^(-2) dw ≲ B r^θ (s(y - g)^(-θ) + s(x - g)^(-θ))`
  for `θ ∈ (0, 1]`;
* `i2Psi2LintBound_kernel_sub_three`: `∫ |A(w)| s(g₁ - w)^(-1) s(g₂ - w)^(-κ) dw ≲
  B r^θ (s(y - g₂)^(-(θ+κ-1)) + s(x - g₂)^(-(θ+κ-1)) + 2 s(g₁ - g₂)^(-(θ+κ-1)))` for
  `θ ∈ [0, 1)` and `θ + κ > 1`;
* `i2Psi2LintBound_kernel_sub_slab`: `∫ |A(w)| s(g₁ - w)^(-λ₁) s(g₂ - w)^(-λ₂) dw ≲ B r^θ` when
  `3 + θ + λ₁ + λ₂ < 5` (no singular output), under the support hypotheses.

The constants depend only on the exponents.  [Hai14, Lemma 10.14, Lemma 10.18].
-/
public section
open MeasureTheory
namespace RegularityStructures

axiom i2Psi2LintBound_kernel_sub_slab {θ l₁ l₂ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hl₁ : 0 ≤ l₁)
    (hl₂ : 0 ≤ l₂) (he : 3 + θ + l₁ + l₂ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x y g₁ g₂ : SpaceTime, |y.1 - x.1| ≤ 1 → |g₁.1 - x.1| ≤ 2 → |g₂.1 - x.1| ≤ 2 →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          (torusParabolicSize (g₁ - w) ^ (-l₁) * torusParabolicSize (g₂ - w) ^ (-l₂)))
          (C * B * torusParabolicSize (y - x) ^ θ)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.TreeI2Psi2DiagramCov ====
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
# The kernel increment and the covariance weights

`i2Psi2Increment K x y w = K(y - w) - K(x - w)` is the kernel `δK_x(y, w)` of [Hai14, (10.39)].
A covariance `Q` with `|Q u| ≤ B s(u)^(-1)` satisfies the flipped bound
`|Q(w - g)| ≤ 2 B s(g - w)^(-1)` (`abs_cov_flip_le`), and its square
`Q(w - g)² ≤ 4 B² s(g - w)^(-2)` (`sq_cov_flip_le`), so that it can be paired with the weights
of `TreeI2Psi2DiagramInner`, which are written with `s(g - w)`.
-/
@[expose] public section
namespace RegularityStructures
/-- The kernel increment `δK_x(y, w) = K(y - w) - K(x - w)` of [Hai14, (10.39)]. -/
def i2Psi2Increment (K : SpaceTime → ℝ) (x y w : SpaceTime) : ℝ :=
  K (y - w) - K (x - w)
end RegularityStructures
end
public section
namespace RegularityStructures
axiom measurable_i2Psi2Increment {K : SpaceTime → ℝ} (hK : Measurable K) (x y : SpaceTime) :
    Measurable (i2Psi2Increment K x y)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.TreeI2Psi2DiagramMultiBasic ====
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
# The tree `I(Ψ²) Ψ²`: building blocks with general exponents

Generalisations of `i2Psi2LintBound_kernel_sub_two` and `i2Psi2LintBound_kernel_sub_three` to
arbitrary exponents of the singular weights, for the difference bound (10.3).  With
`A(w) = K(y - w) - K(x - w)`, `r = s(y - x)`, the Hölder gain `γ ∈ [0, 1]` and exponents `e`,
`e₁`, `e₂`:

* `i2Psi2LintBound_kernel_sub_single`:
  `∫ |A| s(g - w)^(-e) ≲ B r^γ (s(y - g)^(-(γ+e-2)) + s(x - g)^(-(γ+e-2)))`;
* `i2Psi2LintBound_kernel_sub_pair`:
  `∫ |A| s(g₁ - w)^(-e₁) s(g₂ - w)^(-e₂) ≲ B r^γ (s(y - g₂)^(-η) + s(x - g₂)^(-η) +
  2 s(g₁ - g₂)^(-η))`, `η = γ + e₁ + e₂ - 2`.

The kernel hypotheses are bundled in `i2Psi2KernelHyp`.  [Hai14, Lemma 10.14, Lemma 10.18].
-/
@[expose] public section
namespace RegularityStructures
/-- The hypotheses on the kernel `K` of the diagram estimates: `0 ≤ B`, measurable, supported in
`|t| ≤ 1`, `|K| ≤ B s^(-3)` and `|K(u + h) - K u| ≤ B s(h) s(u)^(-4)` for `s(h) ≤ s(u)/2`. -/
def i2Psi2KernelHyp (K : SpaceTime → ℝ) (B : ℝ) : Prop :=
  0 ≤ B ∧ Measurable K ∧ (∀ u : SpaceTime, 1 < |u.1| → K u = 0) ∧
    (∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) ∧
    (∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures

axiom i2Psi2LintBound_kernel_sub_pair {γ e₁ e₂ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (he₁ : 0 ≤ e₁) (he₂ : 0 < e₂) (h5 : 3 + γ + e₁ < 5) (he₂5 : e₂ < 5)
    (hsum : 2 < γ + e₁ + e₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y g₁ g₂ : SpaceTime, 0 < torusParabolicSize (y - g₂) →
        0 < torusParabolicSize (x - g₂) → 0 < torusParabolicSize (g₁ - g₂) →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          (torusParabolicSize (g₁ - w) ^ (-e₁) * torusParabolicSize (g₂ - w) ^ (-e₂)))
          (C * B * torusParabolicSize (y - x) ^ γ *
            (torusParabolicSize (y - g₂) ^ (-(γ + e₁ + e₂ - 2)) +
              torusParabolicSize (x - g₂) ^ (-(γ + e₁ + e₂ - 2)) +
              2 * torusParabolicSize (g₁ - g₂) ^ (-(γ + e₁ + e₂ - 2))))
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_b055cd0c6439cd8ad4a0_TreeI2Psi2DiagramMultiCross ====
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
# The cross pairing with general exponents

For `A(w) = K(y - w) - K(x - w)`, `A'(w') = K(y' - w') - K(x - w')`: three weights couple the
variables `w, w'`, namely `s(g₁ - w)^(-e₁)` (in `w` only), `s(w' - w)^(-e₂)` (both) and
`s(h - w')^(-e₃)` (in `w'` only).  If `3 + γ + e₁ < 5`, `2 < γ + e₁ + e₂` and
`3 + γ' + (γ + e₁ + e₂ - 2) + e₃ < 5`, then
`∫∫ |A| |A'| s(g₁ - w)^(-e₁) s(w' - w)^(-e₂) s(h - w')^(-e₃) ≲ B² r^γ r'^γ'`
(`i2Psi2LintBound_diag_cross`).  It generalises `i2Psi2LintBound_chaos4_cross`.
-/
public section
open MeasureTheory
namespace RegularityStructures
/-- **The cross pairing, general exponents.** -/
theorem i2Psi2LintBound_diag_cross {γ γ' e₁ e₂ e₃ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγ'0 : 0 ≤ γ') (hγ'1 : γ' ≤ 1) (he₁ : 0 ≤ e₁) (he₂ : 0 < e₂) (he₃ : 0 ≤ e₃)
    (h5 : 3 + γ + e₁ < 5) (he₂5 : e₂ < 5) (hs : 2 < γ + e₁ + e₂)
    (hslab : 3 + γ' + (γ + e₁ + e₂ - 2) + e₃ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' g₁ h : SpaceTime, |y.1 - x.1| ≤ 1 → |y'.1 - x.1| ≤ 1 → |g₁.1 - x.1| ≤ 2 →
        |h.1 - x.1| ≤ 2 →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          |i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
            (torusParabolicSize (g₁ - q.1) ^ (-e₁) * torusParabolicSize (q.2 - q.1) ^ (-e₂) *
              torusParabolicSize (h - q.2) ^ (-e₃)))
          (C * B ^ 2 * torusParabolicSize (y - x) ^ γ * torusParabolicSize (y' - x) ^ γ') := by
  obtain ⟨CI, hCI, hI⟩ := i2Psi2LintBound_kernel_sub_pair hγ0 hγ1 he₁ he₂ h5 he₂5 hs
  obtain ⟨CO, hCO, hO⟩ := i2Psi2LintBound_kernel_sub_slab (θ := γ') (l₁ := γ + e₁ + e₂ - 2)
    (l₂ := e₃) hγ'0 hγ'1 (by linarith) he₃ (by linarith)
  refine ⟨4 * CI * CO, by positivity, ?_⟩
  intro K B hK x y y' g₁ h hxy hxy' hg₁ hh
  obtain ⟨hB, hKm, hKs, hKb, hKi⟩ := id hK
  have mA := measurable_i2Psi2Increment hKm
  set r := torusParabolicSize (y - x) with hr
  set r' := torusParabolicSize (y' - x) with hr'
  set p := γ + e₁ + e₂ - 2 with hp
  have hr0 : 0 ≤ r ^ γ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hr0' : 0 ≤ r' ^ γ' := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nrpow : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  show i2Psi2LintBound (volume.prod volume) _ _
  refine i2Psi2LintBound.of_prod_symm
    (G := fun w' => |i2Psi2Increment K x y' w'| * torusParabolicSize (h - w') ^ (-e₃) *
      (CI * B * r ^ γ * (torusParabolicSize (y - w') ^ (-p) + torusParabolicSize (x - w') ^ (-p) +
        2 * torusParabolicSize (g₁ - w') ^ (-p)))) ?_ ?_ ?_
  · exact (((continuous_abs.measurable.comp (mA x y)).comp measurable_fst).mul
      ((continuous_abs.measurable.comp (mA x y')).comp measurable_snd)).mul
      ((((measurable_torusParabolicSize_sub_rpow g₁ _).comp measurable_fst).mul
        ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_fst)).pow_const
          _)).mul ((measurable_torusParabolicSize_sub_rpow h _).comp measurable_snd))
  · filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x,
      ae_torusParabolicSize_sub_pos g₁] with w' hy hx hg
    have hin := hI hK x y g₁ w' hy hx hg
    have hcst : 0 ≤ |i2Psi2Increment K x y' w'| * torusParabolicSize (h - w') ^ (-e₃) :=
      mul_nonneg (abs_nonneg _) (nrpow _ _)
    have hc := hin.const_mul (c := |i2Psi2Increment K x y' w'| *
      torusParabolicSize (h - w') ^ (-e₃)) hcst
    refine hc.mono (fun w => ?_) (le_of_eq (by ring))
    simp only [i2Psi2Increment]
    exact le_of_eq (by ring)
  · have bu : ∀ u : SpaceTime, |u.1 - x.1| ≤ 2 → i2Psi2LintBound volume (fun w' =>
        |i2Psi2Increment K x y' w'| * (torusParabolicSize (u - w') ^ (-p) *
          torusParabolicSize (h - w') ^ (-e₃))) (CO * B * r' ^ γ') := fun u hu =>
      hO hB hKs hKb hKi x y' u h hxy' hu hh
    have nn : ∀ (u : SpaceTime) w', 0 ≤ |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (u - w') ^ (-p) * torusParabolicSize (h - w') ^ (-e₃)) :=
      fun u w' => mul_nonneg (abs_nonneg _) (mul_nonneg (nrpow _ _) (nrpow _ _))
    have mm : ∀ u : SpaceTime, Measurable fun w' : SpaceTime => |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (u - w') ^ (-p) * torusParabolicSize (h - w') ^ (-e₃)) :=
      fun u => (continuous_abs.measurable.comp (mA x y')).mul
        ((measurable_torusParabolicSize_sub_rpow u _).mul
          (measurable_torusParabolicSize_sub_rpow h _))
    have hM : 0 ≤ CO * B * r' ^ γ' := mul_nonneg (mul_nonneg hCO hB) hr0'
    have hy2 : |y.1 - x.1| ≤ 2 := by linarith
    have hx2 : |x.1 - x.1| ≤ 2 := by simp
    have tg := (bu g₁ hg₁).const_mul (c := 2) (by norm_num)
    have s := i2Psi2LintBound.add_three (mm y) (mm x) (nn y) (nn x)
      (fun w' => mul_nonneg (by norm_num) (nn g₁ w')) hM hM (mul_nonneg (by norm_num) hM)
      (bu y hy2) (bu x hx2) tg
    have c := s.const_mul (c := CI * B * r ^ γ) (mul_nonneg (mul_nonneg hCI hB) hr0)
    refine c.mono (fun w' => ?_) (le_of_eq (by ring))
    exact le_of_eq (by ring)
end RegularityStructures
end
