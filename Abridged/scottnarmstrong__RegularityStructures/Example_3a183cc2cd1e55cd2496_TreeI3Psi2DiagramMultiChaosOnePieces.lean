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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.MeanInequalities

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.RegularityStructures.Torus.KernelBoundsBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.KernelCalculusBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3PsiPowers ====
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

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2ChaosOnePotPair ====
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
# Pairings of potentials `y ↦ ∫ h(w) |J(w - y)| dw`

Abstract Tonelli arguments: the integral of `u · Pot h` and of `Pot h₁ · Pot h₂` against `dy`
is bounded in terms of pointwise majorants which are certified by `SingularIntLe` statements.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
/-- The potential `y ↦ ∫ h(w) |J(w - y)| dw`. -/
def i3Psi2Pot (J h : SpaceTime → ℝ) (y : SpaceTime) : ℝ := ∫ w, h w * |J (w - y)|
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2ChaosOneCross ====
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
# Potential estimates for the regular part `B_z` of the chaos-`1` kernel

With `h_z(w) = |K(-w)| Q(w - z)²`, majorised by `B³ 3^δ s(w)^(-3) s(z - w)^(-(2+δ))` (on the slab
`|t| ≤ 1` carrying the support of `K(-·)`), we bound
`∫ s(z - y)^(-(3+δ')) Pot h_{z'}(y) dy` (the cross term with `Ā`) and
`∫ Pot h_z Pot h_{z'} dy` (the term `B_z B_{z'}`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The weight `h_z(w) = |K(-w)| Q(w - z)²`. -/
def i3Psi2Hz (K Q : SpaceTime → ℝ) (z w : SpaceTime) : ℝ := |K (-w)| * Q (w - z) ^ 2
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
axiom i3Psi2Hz_nonneg (K Q : SpaceTime → ℝ) (z w : SpaceTime) : 0 ≤ i3Psi2Hz K Q z w
axiom measurable_i3Psi2Hz {K Q : SpaceTime → ℝ} (hKm : Measurable K) (hQm : Measurable Q)
    (z : SpaceTime) : Measurable (i3Psi2Hz K Q z)
axiom i3Psi2Hz_le {K Q : SpaceTime → ℝ} {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQe : ∀ x, Q (-x) = Q x) {z : SpaceTime} (hz1 : torusParabolicSize z ≤ 1)
    {w : SpaceTime} (h0 : 0 < torusParabolicSize (0 - w)) (hzw : 0 < torusParabolicSize (z - w)) :
    i3Psi2Hz K Q z w ≤ (B ^ 3 * 3 ^ δ) * (singularPow 3 0 w * singularPow (2 + δ) z w)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePotBound ====
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
# Cross terms and pairings of potentials, general exponents

Generalisations of `chaosOne_cross_le` and `chaosOne_pp_le` to potentials of kernels of order
`3 + ε₂` against majorants `s(w)^(-3) s(z - w)^(-(2+ε₁))` of the weight `h`:

* `chaosOne_cross_gen`: `∫ s(z - y)^(-(3+ε₃)) Pot_J h (y) dy ≤ C (s(z')^(-η) + s(z)^(-η))`,
  `η = 1 + ε₁ + ε₂ + ε₃`;
* `chaosOne_pp_gen`: `∫ Pot_{J₁} h₁ Pot_{J₂} h₂ dy ≤ C (s(z)^(-η) s(z')^(-ε₁') + s(z')^(-(ε₁'+η)))`,
  `η = 1 + ε₁ + ε₂ + ε₂'`.
-/
public section
open MeasureTheory
namespace RegularityStructures
/-- The cross term `∫ s(z - y)^(-(3+ε₃)) Pot_J h(y) dy`. -/
axiom chaosOne_cross_gen {ε₁ ε₂ ε₃ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hε₃ : 0 ≤ ε₃)
    (hs : ε₁ + ε₂ + ε₃ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J h : SpaceTime → ℝ} {BJ Hc : ℝ}, 0 ≤ BJ → 0 ≤ Hc → Measurable J →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ BJ * torusParabolicSize x ^ (-(3 + ε₂))) →
      Measurable h → (∀ w, 0 ≤ h w) → ∀ z z' : SpaceTime, 0 < torusParabolicSize z →
        0 < torusParabolicSize z' →
        (∀ᵐ w : SpaceTime ∂volume,
          h w ≤ Hc * (singularPow 3 0 w * singularPow (2 + ε₁) z' w)) →
          Integrable (fun y => singularPow (3 + ε₃) z y * i3Psi2Pot J h y) ∧
            ∫ y, singularPow (3 + ε₃) z y * i3Psi2Pot J h y ≤
              C * Hc * BJ * (torusParabolicSize z' ^ (-(1 + ε₁ + ε₂ + ε₃)) +
                torusParabolicSize z ^ (-(1 + ε₁ + ε₂ + ε₃)))
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOneHz ====
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
# The regular part of the chaos-`1` kernel, difference

`B^a_z(y) = ∫ K(-w) Q_aa(w - z)² J_a(w - y) dw`.  We have
`B^a_z - B^b_z = ∫ K(-w) (Q_aa² - Q_bb²)(w - z) J_a(w - y) dw + ∫ K(-w) Q_bb(w - z)² ΔJ(w - y) dw`,
so `|B^a_z - B^b_z| ≤ Pot_{J_a}(h^Δ_z) + Pot_{ΔJ}(h^b_z)` with `h^Δ_z = |K(-·)| |Q_aa² - Q_bb²|(· - z)`
and `h^b_z = |K(-·)| Q_bb(· - z)²`.  The weight `h^Δ_z` is majorised by
`μ s(w)^(-3) s(z - w)^(-(2+θ+ν))`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The weight `h^Δ_z(w) = |K(-w)| |Q_a(w - z)² - Q_b(w - z)²|`. -/
def i3Psi2HzDelta (K Qa Qb : SpaceTime → ℝ) (z w : SpaceTime) : ℝ :=
  |K (-w)| * |Qa (w - z) ^ 2 - Qb (w - z) ^ 2|
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
axiom i3Psi2HzDelta_nonneg (K Qa Qb : SpaceTime → ℝ) (z w : SpaceTime) :
    0 ≤ i3Psi2HzDelta K Qa Qb z w
axiom measurable_i3Psi2HzDelta {K Qa Qb : SpaceTime → ℝ} (hKm : Measurable K)
    (hQa : Measurable Qa) (hQb : Measurable Qb) (z : SpaceTime) :
    Measurable (i3Psi2HzDelta K Qa Qb z)
axiom i3Psi2HzDelta_le {K Qa Qb : SpaceTime → ℝ} {B μ θ ν : ℝ} (hB : 0 ≤ B) (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQa : ∀ x, 0 < torusParabolicSize x → |Qa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQb : ∀ x, 0 < torusParabolicSize x → |Qb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hΔ : ∀ x, 0 < torusParabolicSize x →
      |Qa x - Qb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ)))
    (hQae : ∀ x, Qa (-x) = Qa x) (hQbe : ∀ x, Qb (-x) = Qb x) {z : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) {w : SpaceTime} (h0 : 0 < torusParabolicSize (0 - w))
    (hzw : 0 < torusParabolicSize (z - w)) :
    i3Psi2HzDelta K Qa Qb z w ≤
      (2 * B ^ 3 * μ * 3 ^ ν) * (singularPow 3 0 w * singularPow (2 + θ + ν) z w)
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_3a183cc2cd1e55cd2496_TreeI3Psi2DiagramMultiChaosOnePieces ====
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
# The potential parts of the chaos-`1` difference

For the potentials `P1_u = Pot_{J_a}(h^Δ_u)` and `P2_u = Pot_{ΔJ}(h^b_u)` (the two pieces of the
bound of `B^a_u - B^b_u`):

* `chaosOne_diff_cross_bound`: `∫ s(u - y)^(-(3 + δ/2 + θ)) (P1_{u'} + P2_{u'})(y) dy
  ≤ μ C (s(u')^(-E) + s(u)^(-E))`, `E = 1 + 2δ + 2θ`;
* `chaosOne_diff_pp_bound`: `∫ (P1_u + P2_u)(P1_{u'} + P2_{u'}) dy ≤ μ² C (s(u)^(-E) + 2 s(u')^(-E))`.
-/
public section
open MeasureTheory
namespace RegularityStructures
private axiom cross_le_E' {z z' : SpaceTime} {η E : ℝ} (hz : 0 < torusParabolicSize z)
    (hz' : 0 < torusParabolicSize z') (hz1 : torusParabolicSize z ≤ 1)
    (hz1' : torusParabolicSize z' ≤ 1) (h : η ≤ E) :
    torusParabolicSize z' ^ (-η) + torusParabolicSize z ^ (-η) ≤
      torusParabolicSize z' ^ (-E) + torusParabolicSize z ^ (-E)
theorem chaosOne_diff_cross_bound {B δ θ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Ja Jb Qaa Qbb : SpaceTime → ℝ} {μ : ℝ}, 0 ≤ μ →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Measurable K → Measurable Ja → Measurable Jb →
      Measurable Qaa → Measurable Qbb →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Qaa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Qbb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Qaa x - Qbb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ))) →
      (∀ x, 0 < torusParabolicSize x →
        |Ja x - Jb x| ≤ B * μ * torusParabolicSize x ^ (-(3 + θ))) →
      (∀ x, Qaa (-x) = Qaa x) → (∀ x, Qbb (-x) = Qbb x) →
      ∀ u u' : SpaceTime, 0 < torusParabolicSize u → 0 < torusParabolicSize u' →
        torusParabolicSize u ≤ 1 → torusParabolicSize u' ≤ 1 →
        Integrable (fun y => singularPow (3 + (δ / 2 + θ)) u y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y)) ∧
        ∫ y, singularPow (3 + (δ / 2 + θ)) u y *
          (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
            i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) ≤
          μ * C * (torusParabolicSize u' ^ (-(1 + 2 * δ + 2 * θ)) +
            torusParabolicSize u ^ (-(1 + 2 * δ + 2 * θ))) := by
  obtain ⟨Cx1, hCx1, hx1⟩ := chaosOne_cross_gen (ε₁ := θ + δ) (ε₂ := 0) (ε₃ := δ / 2 + θ)
    (by linarith) le_rfl (by linarith) (by linarith)
  obtain ⟨Cx2, hCx2, hx2⟩ := chaosOne_cross_gen (ε₁ := δ) (ε₂ := θ) (ε₃ := δ / 2 + θ)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  set Hd : ℝ := 2 * B ^ 3 * 3 ^ δ with hHd
  set Hb : ℝ := B ^ 3 * 3 ^ δ with hHb
  have hHd0 : 0 ≤ Hd := by rw [hHd]; positivity
  have hHb0 : 0 ≤ Hb := by rw [hHb]; positivity
  refine ⟨Cx1 * Hd * B + Cx2 * Hb * B, by positivity, ?_⟩
  intro K Ja Jb Qaa Qbb μ hμ hKs hKm hJam hJbm hQam hQbm hK hJa hQa hQb hΔQ hΔJ hQae hQbe u u'
    hu hu' hu1 hu1'
  have hMajΔ : ∀ᵐ w : SpaceTime ∂volume, i3Psi2HzDelta K Qaa Qbb u' w ≤
      (Hd * μ) * (singularPow 3 0 w * singularPow (2 + (θ + δ)) u' w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos u'] with w a b
    have := i3Psi2HzDelta_le (ν := δ) (θ := θ) hB hμ hδ.le hKs hK hQa hQb hΔQ hQae hQbe hu1' a b
    have e : 2 + θ + δ = 2 + (θ + δ) := by ring
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    rw [hHd]; ring
  have hMajB : ∀ᵐ w : SpaceTime ∂volume, i3Psi2Hz K Qbb u' w ≤
      Hb * (singularPow 3 0 w * singularPow (2 + δ) u' w) := by
    filter_upwards [ae_torusParabolicSize_sub_pos 0, ae_torusParabolicSize_sub_pos u'] with w a b
    exact (i3Psi2Hz_le hB hδ.le hKs hK hQb hQbe hu1' a b).trans (le_of_eq (by rw [hHb]))
  have hJa3 : ∀ x, 0 < torusParabolicSize x → |Ja x| ≤ B * torusParabolicSize x ^ (-(3 + 0 : ℝ)) :=
    fun x hx => by simpa using hJa x hx
  obtain ⟨j1, k1⟩ := hx1 hB (mul_nonneg hHd0 hμ) hJam hJa3
    (measurable_i3Psi2HzDelta hKm hQam hQbm u') (i3Psi2HzDelta_nonneg K Qaa Qbb u') u u' hu hu'
    hMajΔ
  have hΔJm : Measurable (fun x => Ja x - Jb x) := hJam.sub hJbm
  obtain ⟨j2, k2⟩ := hx2 (mul_nonneg hB hμ) hHb0 hΔJm hΔJ
    (measurable_i3Psi2Hz hKm hQbm u') (i3Psi2Hz_nonneg K Qbb u') u u' hu hu' hMajB
  have jj : Integrable (fun y => singularPow (3 + (δ / 2 + θ)) u y *
      i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y + singularPow (3 + (δ / 2 + θ)) u y *
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) := j1.add j2
  refine ⟨jj.congr (Filter.Eventually.of_forall fun y => by simp only; ring), ?_⟩
  have c1 := cross_le_E' hu hu' hu1 hu1' (η := 1 + (θ + δ) + 0 + (δ / 2 + θ))
    (E := 1 + 2 * δ + 2 * θ) (by linarith)
  have c2 := cross_le_E' hu hu' hu1 hu1' (η := 1 + δ + θ + (δ / 2 + θ))
    (E := 1 + 2 * δ + 2 * θ) (by linarith)
  have e : ∫ y, singularPow (3 + (δ / 2 + θ)) u y * (i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y +
      i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y) =
      (∫ y, singularPow (3 + (δ / 2 + θ)) u y * i3Psi2Pot Ja (i3Psi2HzDelta K Qaa Qbb u') y) +
      ∫ y, singularPow (3 + (δ / 2 + θ)) u y *
        i3Psi2Pot (fun x => Ja x - Jb x) (i3Psi2Hz K Qbb u') y := by
    rw [← integral_add j1 j2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)
  rw [e]
  have m1 := mul_le_mul_of_nonneg_left c1 (by positivity : 0 ≤ μ * (Cx1 * Hd * B))
  have m2 := mul_le_mul_of_nonneg_left c2 (by positivity : 0 ≤ μ * (Cx2 * Hb * B))
  linarith
end RegularityStructures
end
