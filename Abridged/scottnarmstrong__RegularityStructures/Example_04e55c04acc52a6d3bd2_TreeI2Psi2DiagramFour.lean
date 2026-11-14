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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v2873403e9bda.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v2873403e9bda.RegularityStructures.BPHZ.TreeI2Psi2DiagramLint ====
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
axiom i2Psi2LintBound.mono_ae {f g : α → ℝ} {M M' : ℝ}
    (h : i2Psi2LintBound μ g M) (hfg : ∀ᵐ a ∂μ, f a ≤ g a) (hM : M ≤ M') :
    i2Psi2LintBound μ f M'
axiom i2Psi2LintBound.mono {f g : α → ℝ} {M M' : ℝ}
    (h : i2Psi2LintBound μ g M) (hfg : ∀ a, f a ≤ g a) (hM : M ≤ M') :
    i2Psi2LintBound μ f M'

axiom i2Psi2LintBound.const_mul {f : α → ℝ} {M c : ℝ} (hc : 0 ≤ c)
    (h : i2Psi2LintBound μ f M) : i2Psi2LintBound μ (fun a => c * f a) (c * M)
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
axiom i2Psi2LintBound.prod_mul [SFinite μ] [SFinite ν] {f : α → ℝ} {g : β → ℝ} {M N : ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) (hf0 : ∀ a, 0 ≤ f a) (hM : 0 ≤ M)
    (hfM : i2Psi2LintBound μ f M) (hgN : i2Psi2LintBound ν g N) :
    i2Psi2LintBound (μ.prod ν) (fun q => f q.1 * g q.2) (M * N)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v2873403e9bda.RegularityStructures.Torus.KernelBoundsBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v2873403e9bda.Phi43.BPHZ.KernelCalculusBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v2873403e9bda.Phi43.BPHZ.TreeI2Psi2DiagramInner ====
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

/-- **Increment of `K` against `s(g - w)^(-2)`**, [Hai14, Lemma 10.14 and 10.18]. -/
axiom i2Psi2LintBound_kernel_sub_two {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x y g : SpaceTime, 0 < torusParabolicSize (y - g) → 0 < torusParabolicSize (x - g) →
        i2Psi2LintBound volume (fun w => |K (y - w) - K (x - w)| *
          torusParabolicSize (g - w) ^ (-(2 : ℝ)))
          (C * B * torusParabolicSize (y - x) ^ θ *
            (torusParabolicSize (y - g) ^ (-θ) + torusParabolicSize (x - g) ^ (-θ)))
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v2873403e9bda.Phi43.BPHZ.TreeI2Psi2DiagramCov ====
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
axiom torusParabolicSize_pos_of_sub_pos {a b : SpaceTime} (h : 0 < torusParabolicSize (a - b)) :
    0 < torusParabolicSize (b - a)

/-- The flipped square bound `Q(w - g)² ≤ 4 B² s(g - w)^(-2)`. -/
axiom sq_cov_flip_le {Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {g w : SpaceTime}
    (h : 0 < torusParabolicSize (g - w)) :
    Q (w - g) ^ 2 ≤ 4 * B ^ 2 * torusParabolicSize (g - w) ^ (-(2 : ℝ))
axiom measurable_i2Psi2Increment {K : SpaceTime → ℝ} (hK : Measurable K) (x y : SpaceTime) :
    Measurable (i2Psi2Increment K x y)
/-- The square bound `Q(u)² ≤ B² s(u)^(-2)`. -/
axiom sq_cov_le {Q : SpaceTime → ℝ} {B : ℝ}
    (hQ : ∀ u : SpaceTime, 0 < torusParabolicSize u →
      |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) {u : SpaceTime}
    (h : 0 < torusParabolicSize u) :
    Q u ^ 2 ≤ B ^ 2 * torusParabolicSize u ^ (-(2 : ℝ))
/-- `s(a - b)^(-e) ≤ 2 s(b - a)^(-e)` for `0 ≤ e ≤ 1`. -/
axiom torusParabolicSize_sub_rpow_neg_le {a b : SpaceTime} {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (h : 0 < torusParabolicSize (b - a)) :
    torusParabolicSize (a - b) ^ (-e) ≤ 2 * torusParabolicSize (b - a) ^ (-e)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_04e55c04acc52a6d3bd2_TreeI2Psi2DiagramFour ====
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
# The chaos-`4` monomials of the tree `I(Ψ²) Ψ²`: squared pairing

For `A(w) = K(y - w) - K(x - w)`, `A'(w') = K(y' - w') - K(x - w')` and a covariance `Q`
with `|Q| ≤ B s^(-1)`, the principal pairing
`∫∫ |A(w)| |A'(w')| Q(w - w')² dw dw' ≲ B⁴ s(y - x)^θ s(y' - x)^θ`, `θ = 1 - δ/2`
(`i2Psi2LintBound_chaos4_sq`): the inner integral is `≲ B³ r^θ (s(y - w')^(-θ) + s(x - w')^(-θ))`
(`i2Psi2LintBound_kernel_sub_two`, total order `5 + θ > 5`), and the outer one is bounded
(`i2Psi2LintBound_kernel_sub_slab`, total order `3 + θ + θ < 5`).  [Hai14, p. 169, after (10.39)].
-/
public section
open MeasureTheory
namespace RegularityStructures
private axiom alg_prod {CA B ra ra' d1 p q a2 b1 b2 : ℝ}
    (hra : 0 ≤ ra) (hra' : 0 ≤ ra') (hd1 : 0 ≤ d1) (hp : 0 ≤ p)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (h1 : a2 ≤ 2 * p) (h2 : b1 ≤ 2 * d1) (h3 : b2 ≤ 2 * q) :
    4 * B ^ 2 * (CA * B * ra * (d1 + a2)) * (B ^ 2 * (CA * B * ra' * (b1 + b2))) ≤
      16 * CA ^ 2 * B ^ 6 * ra * ra' * (d1 + p) * (d1 + q)
/-- **The product pairing of chaos `4`**: `(∫ |A| Q(w - y')²) (∫ |A'| Q'(y - w')²)`. -/
theorem i2Psi2LintBound_chaos4_prod {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q Q' : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K → Measurable Q →
      Measurable Q' → (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q' u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          (|i2Psi2Increment K x y q.1| * Q (q.1 - y') ^ 2) *
            (|i2Psi2Increment K x y' q.2| * Q' (y - q.2) ^ 2))
          (C * B ^ 6 * torusParabolicSize (y - x) ^ θ * torusParabolicSize (y' - x) ^ θ *
            (torusParabolicSize (y - y') ^ (-θ) + torusParabolicSize (y' - x) ^ (-θ)) *
            (torusParabolicSize (y - y') ^ (-θ) + torusParabolicSize (y - x) ^ (-θ))) := by
  obtain ⟨CA, hCA, hA⟩ := i2Psi2LintBound_kernel_sub_two hθ hθ1
  refine ⟨16 * CA ^ 2, by positivity, ?_⟩
  intro K Q Q' B hB hKm hQm hQm' hKs hKb hKi hQb hQb' x y y' hr hr' hd
  have mA := measurable_i2Psi2Increment hKm
  have hyx : 0 < torusParabolicSize (x - y) := torusParabolicSize_pos_of_sub_pos hr
  have hyx' : 0 < torusParabolicSize (x - y') := torusParabolicSize_pos_of_sub_pos hr'
  have hdd : 0 < torusParabolicSize (y' - y) := torusParabolicSize_pos_of_sub_pos hd
  have nrpow : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  -- the first factor
  have fa := (hA hB hKb hKi x y y' hd hyx').const_mul (c := 4 * B ^ 2) (by positivity)
  have fa' : i2Psi2LintBound volume (fun w => |i2Psi2Increment K x y w| * Q (w - y') ^ 2)
      (4 * B ^ 2 * (CA * B * torusParabolicSize (y - x) ^ θ *
        (torusParabolicSize (y - y') ^ (-θ) + torusParabolicSize (x - y') ^ (-θ)))) := by
    refine fa.mono_ae ?_ le_rfl
    filter_upwards [ae_torusParabolicSize_sub_pos y'] with w hw
    have hq := sq_cov_flip_le hB hQb hw
    calc |i2Psi2Increment K x y w| * Q (w - y') ^ 2
        ≤ |i2Psi2Increment K x y w| * (4 * B ^ 2 * torusParabolicSize (y' - w) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hq (abs_nonneg _)
      _ = _ := by simp only [i2Psi2Increment]; ring
  -- the second factor
  have fb := (hA hB hKb hKi x y' y hdd hyx).const_mul (c := B ^ 2) (by positivity)
  have fb' : i2Psi2LintBound volume (fun w => |i2Psi2Increment K x y' w| * Q' (y - w) ^ 2)
      (B ^ 2 * (CA * B * torusParabolicSize (y' - x) ^ θ *
        (torusParabolicSize (y' - y) ^ (-θ) + torusParabolicSize (x - y) ^ (-θ)))) := by
    refine fb.mono_ae ?_ le_rfl
    filter_upwards [ae_torusParabolicSize_sub_pos y] with w hw
    have hq := sq_cov_le hQb' hw
    calc |i2Psi2Increment K x y' w| * Q' (y - w) ^ 2
        ≤ |i2Psi2Increment K x y' w| * (B ^ 2 * torusParabolicSize (y - w) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hq (abs_nonneg _)
      _ = _ := by simp only [i2Psi2Increment]; ring
  have hMa : 0 ≤ 4 * B ^ 2 * (CA * B * torusParabolicSize (y - x) ^ θ *
        (torusParabolicSize (y - y') ^ (-θ) + torusParabolicSize (x - y') ^ (-θ))) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg hCA hB) (nrpow _ _))
      (add_nonneg (nrpow _ _) (nrpow _ _)))
  have hprod := i2Psi2LintBound.prod_mul (μ := volume) (ν := volume)
    (((continuous_abs.measurable.comp (mA x y)).mul ((hQm.comp
      (measurable_id.sub measurable_const)).pow_const 2)).aemeasurable)
    (((continuous_abs.measurable.comp (mA x y')).mul ((hQm'.comp
      (measurable_const.sub measurable_id)).pow_const 2)).aemeasurable)
    (fun w => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hMa fa' fb'
  refine hprod.mono (fun q => le_rfl) ?_
  have t1 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y') (e := θ) hθ.le hθ1 hr'
  have t2 := torusParabolicSize_sub_rpow_neg_le (a := y') (b := y) (e := θ) hθ.le hθ1 hd
  have t3 := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := θ) hθ.le hθ1 hr
  have := alg_prod (CA := CA) (B := B) (nrpow (y - x) θ) (nrpow (y' - x) θ) (nrpow (y - y') (-θ))
    (nrpow (y' - x) (-θ)) (nrpow (y' - y) (-θ)) (nrpow (x - y) (-θ)) t1 t2 t3
  calc _ ≤ _ := this
    _ = _ := by ring
end RegularityStructures
end
