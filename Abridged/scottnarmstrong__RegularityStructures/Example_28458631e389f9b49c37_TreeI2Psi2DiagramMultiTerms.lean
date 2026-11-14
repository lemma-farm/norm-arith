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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.RegularityStructures.BPHZ.TreeI2Psi2DiagramLint ====
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

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.i2Psi2LintBound.mono.{w_u_1} : ∀ {α : Type w_u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f g : α → ℝ}
  {M M' : ℝ},
  RegularityStructures.i2Psi2LintBound μ g M →
    (∀ (a : α), f a ≤ g a) → M ≤ M' → RegularityStructures.i2Psi2LintBound μ f M'

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.i2Psi2LintBound.const_mul.{w_u_1} : ∀ {α : Type w_u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → ℝ} {M c : ℝ},
  0 ≤ c →
    RegularityStructures.i2Psi2LintBound μ f M →
      RegularityStructures.i2Psi2LintBound μ (fun (a : α) ↦ c * f a) (c * M)
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.RegularityStructures.Torus.KernelBoundsBasic ====
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

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.Phi43.BPHZ.TreeI2Psi2DiagramCov ====
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

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.Phi43.BPHZ.TreeI2Psi2DiagramMultiBasic ====
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

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.Phi43.BPHZ.TreeI2Psi2DiagramMultiTriple ====
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
# Common notation for the difference bound of `I(Ψ²) Ψ²`

* `i2Psi2DiffF θ δ r r' d`: the target majorant
  `d^(-η) + d^(-2) (r^(2-η) + r'^(2-η)) + d^(-(2+2θ)) (r^(2-δ) + r'^(2-δ)) + r^(-η) + r'^(-η)`,
  `η = 2θ + δ`;
* `i2Psi2Triple K x y y' g₁ h a b c`: the integrand
  `|A(w)| |A'(w')| s(g₁ - w)^(-a) s(w' - w)^(-b) s(h - w')^(-c)`;
* `i2Psi2PointCfg x y y'`: `0 < r, r' ≤ 1`, `0 < d`, with `r = s(y - x)`, `r' = s(y' - x)`,
  `d = s(y - y')`;
* the relations `d ≤ 8 (r + r')`, `r' ≤ 16 (r + d)`, `r ≤ 16 (r' + d)`.
-/
@[expose] public section
namespace RegularityStructures
/-- The majorant of the difference bound: `η = 2θ + δ`,
`d^(-η) + d^(-2) (r^(2-η) + r'^(2-η)) + d^(-(2+2θ)) (r^(2-δ) + r'^(2-δ)) + (r^(-η) + r'^(-η))`. -/
noncomputable def i2Psi2DiffF (θ δ r r' d : ℝ) : ℝ :=
  d ^ (-(2 * θ + δ)) + d ^ (-(2 : ℝ)) * (r ^ (2 - (2 * θ + δ)) + r' ^ (2 - (2 * θ + δ))) +
    d ^ (-(2 + 2 * θ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) + (r ^ (-(2 * θ + δ)) + r' ^ (-(2 * θ + δ)))
/-- The integrand `|A(w)| |A'(w')| s(g₁ - w)^(-a) s(w' - w)^(-b) s(h - w')^(-c)`. -/
noncomputable def i2Psi2Triple (K : SpaceTime → ℝ) (x y y' g₁ h : SpaceTime) (a b c : ℝ)
    (q : SpaceTime × SpaceTime) : ℝ :=
  |i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
    (torusParabolicSize (g₁ - q.1) ^ (-a) * torusParabolicSize (q.2 - q.1) ^ (-b) *
      torusParabolicSize (h - q.2) ^ (-c))
def i2Psi2PointCfg (x y y' : SpaceTime) : Prop :=
  0 < torusParabolicSize (y - x) ∧ torusParabolicSize (y - x) ≤ 1 ∧
    0 < torusParabolicSize (y' - x) ∧ torusParabolicSize (y' - x) ≤ 1 ∧
    0 < torusParabolicSize (y - y')
end RegularityStructures
end
public section
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.i2Psi2PointCfg.time_le : ∀ {x y y' : RegularityStructures.SpaceTime},
  RegularityStructures.i2Psi2PointCfg x y y' → |y.1 - x.1| ≤ 1 ∧ |y'.1 - x.1| ≤ 1

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_28458631e389f9b49c37_TreeI2Psi2DiagramMultiTerms ====
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
# The monomials of the difference bound for `I(Ψ²) Ψ²`

Throughout `θ ∈ (0, 1/8]`, `δ ∈ (0, 1/4]`, `r = s(y - x)`, `r' = s(y' - x)`, `d = s(y - y')`,
`η = 2θ + δ`, and `F = i2Psi2DiffF θ δ r r' d`.  Each monomial of the second difference of the
chaos kernels is a product of four covariance weights, one of which has its exponent raised by `2θ`
(`TreeI2Psi2DifferencePointwise`).  Its diagram integral is bounded by `C B² F`:

* `i2Psi2LintBound_diff_sq_inner`, `_sq_outer`: `s(w' - w)^(-(2+2θ)) d^(-2)`, `s(w' - w)^(-2)
  d^(-(2+2θ))`;
* `i2Psi2LintBound_diff_prod_left`, `_prod_right`: the product pairings with a raised exponent;
* `i2Psi2LintBound_diff_cross_inner`: the cross pairing with a raised exponent among the three
  integrated weights, times `d^(-1)`;
* `i2Psi2LintBound_diff_cross_outer`: the cross pairing times `d^(-(1+2θ))`.
-/
public section
open MeasureTheory
namespace RegularityStructures

set_option linter.unusedVariables false in
theorem i2Psi2LintBound_diff_sq_outer {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) 
    (h_RegularityStructures_i2Psi2LintBound_diag_sq : ∀ {γ γ' e : ℝ},
      0 ≤ γ →
        γ ≤ 1 →
          0 ≤ γ' →
            γ' ≤ 1 →
              e < 5 →
                2 < γ + e →
                  3 + γ' + (γ + e - 2) < 5 →
                    ∃ (C : ℝ),
                      0 ≤ C ∧
                        ∀ {K : RegularityStructures.SpaceTime → ℝ} {B : ℝ},
                          RegularityStructures.i2Psi2KernelHyp K B →
                            ∀ (x y y' : RegularityStructures.SpaceTime),
                              |y.1 - x.1| ≤ 1 →
                                |y'.1 - x.1| ≤ 1 →
                                  RegularityStructures.i2Psi2LintBound MeasureTheory.MeasureSpace.volume
                                    (fun
                                        (q :
                                          RegularityStructures.SpaceTime ×
                                            RegularityStructures.SpaceTime) ↦
                                      |RegularityStructures.i2Psi2Increment K x y q.1| *
                                          |RegularityStructures.i2Psi2Increment K x y' q.2| *
                                        RegularityStructures.torusParabolicSize (q.2 - q.1) ^ (-e))
                                    (C * B ^ 2 * RegularityStructures.torusParabolicSize (y - x) ^ γ *
                                      RegularityStructures.torusParabolicSize (y' - x) ^ γ'))
    (h_RegularityStructures_rpow_mul_rpow_le_add_two : ∀ {r r' g : ℝ}, 0 < r → 0 < r' → r ^ g * r' ^ g ≤ r ^ (2 * g) + r' ^ (2 * g))
    (h_RegularityStructures_i2Psi2DiffF_ge_three : ∀ {θ δ r r' d : ℝ},
      0 < r →
        0 < r' →
          0 < d →
            d ^ (-(2 + 2 * θ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) ≤
              RegularityStructures.i2Psi2DiffF θ δ r r' d)
    (h_RegularityStructures_torusParabolicSize_nonneg : ∀ (z : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.torusParabolicSize z)
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' g₁ h : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (fun q => i2Psi2Triple K x y y' g₁ h 0 2 0 q *
          torusParabolicSize (y - y') ^ (-(2 + 2 * θ)))
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := h_RegularityStructures_i2Psi2LintBound_diag_sq (γ := 1 - δ / 2) (γ' := 1 - δ / 2)
    (e := 2) (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)
    (by linarith) (by linarith)
  refine ⟨C0, hC0, ?_⟩
  intro K B hK x y y' g₁ h hc
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hc
  obtain ⟨hxy, hxy'⟩ := hc.time_le
  have hB := hK.1
  have hb := (h0 hK x y y' hxy hxy').const_mul
    (c := torusParabolicSize (y - y') ^ (-(2 + 2 * θ)))
    (Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _)
  refine hb.mono (fun q => ?_) ?_
  · unfold i2Psi2Triple
    simp only [neg_zero, Real.rpow_zero, one_mul, mul_one]
    exact le_of_eq (by ring)
  · have amgm := h_RegularityStructures_rpow_mul_rpow_le_add_two hr hr' (g := 1 - δ / 2)
    have e2 : 2 * (1 - δ / 2) = 2 - δ := by ring
    rw [e2] at amgm
    have hF := h_RegularityStructures_i2Psi2DiffF_ge_three (θ := θ) (δ := δ) hr hr' hd
    have hCB : 0 ≤ C0 * B ^ 2 := by positivity
    have nd : 0 ≤ torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) := Real.rpow_nonneg hd.le _
    calc torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) * (C0 * B ^ 2 *
          torusParabolicSize (y - x) ^ (1 - δ / 2) * torusParabolicSize (y' - x) ^ (1 - δ / 2))
        = C0 * B ^ 2 * (torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) *
          (torusParabolicSize (y - x) ^ (1 - δ / 2) * torusParabolicSize (y' - x) ^ (1 - δ / 2))) :=
          by ring
      _ ≤ C0 * B ^ 2 * (torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) *
          (torusParabolicSize (y - x) ^ (2 - δ) + torusParabolicSize (y' - x) ^ (2 - δ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left amgm nd) hCB
      _ ≤ _ := mul_le_mul_of_nonneg_left hF hCB
end RegularityStructures
end
