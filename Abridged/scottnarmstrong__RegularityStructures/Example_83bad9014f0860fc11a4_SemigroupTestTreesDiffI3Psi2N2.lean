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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.RegularityStructures.Torus.KernelBoundsBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3PsiPowers ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3PsiLeaves ====
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
# Integrable majorants with an explicit integral bound

`SingularIntLe f X` records that `f` is integrable on space-time with `∫ f ≤ X`.  Using it we
package the integral estimates of products of centred parabolic powers that are needed for the
diagram bounds of the tree `I(Ψ³)Ψ`:

* two powers of total order `5 + η > 5` (from `integrable_and_integral_singularPow_mul_le`);
* three powers of total order `5 + η`, two of which have total order `< 5`;
* two powers of total order `< 5`, restricted to the time slab `|t| ≤ 2`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14 and (10.37a).
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- `f` is integrable on space-time with integral at most `X`. -/
def SingularIntLe (f : SpaceTime → ℝ) (X : ℝ) : Prop :=
  Integrable f ∧ ∫ w, f w ≤ X
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SingularIntLe.add : ∀ {f g : RegularityStructures.SpaceTime → ℝ} {X Y : ℝ},
  RegularityStructures.SingularIntLe f X →
    RegularityStructures.SingularIntLe g Y →
      RegularityStructures.SingularIntLe (fun (w : RegularityStructures.SpaceTime) ↦ f w + g w)
        (X + Y)
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SingularIntLe.const_mul : ∀ {f : RegularityStructures.SpaceTime → ℝ} {X c : ℝ},
  RegularityStructures.SingularIntLe f X →
    0 ≤ c →
      RegularityStructures.SingularIntLe (fun (w : RegularityStructures.SpaceTime) ↦ c * f w)
        (c * X)
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SingularIntLe.mono_right : ∀ {f : RegularityStructures.SpaceTime → ℝ} {X Y : ℝ},
  RegularityStructures.SingularIntLe f X → X ≤ Y → RegularityStructures.SingularIntLe f Y

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3PsiChain ====
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
# The diagrams with a `Q²`-link between the two integration variables

Let `δK(z, w) = K(z - w) - K(-w)`.  For `(u, u') = (z, z')` (the chaos-two pairing
`Q(w - z) Q(w - w̄)² Q(w̄ - z̄)`) and `(u, u') = (z', z)` (the secondary pairing
`Q(w - w̄)² Q(w - z̄) Q(w̄ - z)`), the double integral of
`δK(z, w) δK(z', w̄) Q(w - u) Q(w - w̄)² Q(w̄ - u')` is absolutely integrable and bounded by
`s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ)`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168 (secondary pairings: source gap, bounded by the
same lemmas).
-/
public section
open MeasureTheory Set
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SingularIntLe.congr_fun : ∀ {f g : RegularityStructures.SpaceTime → ℝ} {X : ℝ},
  (∀ (w : RegularityStructures.SpaceTime), f w = g w) →
    RegularityStructures.SingularIntLe f X → RegularityStructures.SingularIntLe g X
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3Psi2DiagramLeaves ====
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
# Leaves with symmetrised output for the diagrams of `I(Ψ³)Ψ²`

For the three points `z, z', 0` put `S_p(z, z') = s(z - z')^(-p) + s(z)^(-p) + s(z')^(-p)`.
Every ordered difference `s(a - b)^(-p)` of two of the points is at most `2^p S_p`.  Using this we
restate the two-power and three-power integral estimates with centres among `{z, z', 0}` in the
form `∫ ⋯ ≤ C S_η`, and prove that a product `S_a S_b` is at most a constant times `S_{a+b}`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- `S_p(z, z') = s(z - z')^(-p) + s(z - 0)^(-p) + s(z' - 0)^(-p)`. -/
def i3Psi2S (p : ℝ) (z z' : SpaceTime) : ℝ :=
  torusParabolicSize (z - z') ^ (-p) + torusParabolicSize (z - 0) ^ (-p) +
    torusParabolicSize (z' - 0) ^ (-p)
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3PsiDiagramMultiBasic ====
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
# Building blocks for the diagrams of `I(Ψ³)Ψ` with general exponents

* `TwoLevelLe G X`: a double-integral majorant `G` whose inner integrals are dominated by an
  integrable function of integral at most `X`; it yields integrability and a bound for every
  integrand dominated by `G`.
* the outer leaf and the inner integral of the chain diagram with the exponents
  `3`, `1 + α`, `1 + κ` (outer) and `4 + γ`, `2 + β` (inner), generalising the case
  `α = γ = 0`, `β = κ = δ` of `singularIntLe_outer_leaf` and `singularIntLe_inner`.

Source: [Hai14] = arXiv:1303.5113v4, (10.37a), Lemma 10.14, p. 167--168.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- A function `G` of two space-time variables is a **two-level majorant with bound `X`** if, for
almost every `w`, `G w` is integrable and its integral is at most `H w`, where `H` is integrable
with `∫ H ≤ X`. -/
def TwoLevelLe (G : SpaceTime → SpaceTime → ℝ) (X : ℝ) : Prop :=
  (∀ᵐ w : SpaceTime ∂volume, Integrable (G w)) ∧
    ∃ H : SpaceTime → ℝ, SingularIntLe H X ∧ ∀ᵐ w : SpaceTime ∂volume, ∫ v, G w v ≤ H w
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.TwoLevelLe.congr_fun : ∀ {G G' : RegularityStructures.SpaceTime → RegularityStructures.SpaceTime → ℝ} {X : ℝ},
  (∀ (w v : RegularityStructures.SpaceTime), G w v = G' w v) →
    RegularityStructures.TwoLevelLe G X → RegularityStructures.TwoLevelLe G' X
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3Psi2DiagramMultiN2 ====
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
# The weighted diagram `N₂` of `I(Ψ³)Ψ²` with general exponents

The diagram `N₂` (chaos `3`) is the double integral of `δK(z, w) δK(z', v)` against the weight
`s(w - z)^(-1) s(w - z')^(-1) s(w - v)^(-1) s(v - z')^(-1) s(z - v)^(-1)`.  Each of the five
exponents may be raised by a small `yᵢ ≥ 0` (the factor `μ s^(-θ)` of one covariance in the
difference of the fields), and the exponent of `s(w - z)` also carries the slab loss `δ`.  This file
contains the pointwise domination by the majorant `i3Psi2N2Majorant`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The majorant of the diagram `N₂`: exponents `1 + ν₁` at `(z, w)`, `1 + y₂` at `(z', w)`,
`1 + y₃` at `(w, v)`, `4 + y₄` at `(z', v)`, `(0, v)` and `1 + y₅` at `(z, v)`. -/
def i3Psi2N2Majorant (ν₁ y₂ y₃ y₄ y₅ : ℝ) (z z' w v : SpaceTime) : ℝ :=
  ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + ν₁) z w *
      singularPow (1 + y₂) z' w) *
    ((3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v) * singularPow (1 + y₅) z v *
      singularPow (1 + y₃) w v)
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_83bad9014f0860fc11a4_SemigroupTestTreesDiffI3Psi2N2 ====
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
# The weighted diagram `N₂` of the difference of `I(Ψ³)Ψ²`, for arbitrary `z, z'`

`i3Psi2N2Majorant_twoLevelLe`: the majorant `i3Psi2N2Majorant` is a two-level majorant with bound
`Λ C S_{1+δ+y₁+⋯+y₅}(z, z')`, independently of `K` and of any smallness of `z, z'`.
`i3Psi2N2Weighted_twoLevelLe_global`: the global weighted diagram.
-/
public section
open MeasureTheory
namespace RegularityStructures

set_option linter.unusedVariables false in
/-- **Two-level bound for the majorant of `N₂`**, independent of `K`. -/
theorem i3Psi2N2Majorant_twoLevelLe {δ y₁ y₂ y₃ y₄ y₅ : ℝ} (hδ : 0 < δ)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (hy₃ : 0 ≤ y₃) (hy₄ : 0 ≤ y₄) (hy₅ : 0 ≤ y₅)
    (hsum : δ + y₁ + y₂ + y₃ + y₄ + y₅ ≤ 1 / 2) 
    (h_RegularityStructures_torusParabolicSize_nonneg : ∀ (z : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.torusParabolicSize z)
    (h_RegularityStructures_torusParabolicSize_sub_pos_symm : ∀ {a b : RegularityStructures.SpaceTime},
      0 < RegularityStructures.torusParabolicSize (a - b) →
        0 < RegularityStructures.torusParabolicSize (b - a))
    (h_RegularityStructures_i3Psi2S_mul_le : ∀ {a b : ℝ},
      0 ≤ a →
        0 ≤ b →
          0 < a + b →
            ∀ {z z' : RegularityStructures.SpaceTime},
              0 < RegularityStructures.torusParabolicSize (z - z') →
                0 < RegularityStructures.torusParabolicSize (z - 0) →
                  0 < RegularityStructures.torusParabolicSize (z' - 0) →
                    RegularityStructures.i3Psi2S a z z' * RegularityStructures.i3Psi2S b z z' ≤
                      9 * 2 ^ (a + b) * RegularityStructures.i3Psi2S (a + b) z z')
    (h_RegularityStructures_outer_leaves_n2c : ∀ {ν₁ y₂ η : ℝ},
      0 < ν₁ →
        ν₁ < 1 →
          0 ≤ y₂ →
            0 < η →
              ν₁ + y₂ + η < 2 →
                ∃ (C : ℝ),
                  0 ≤ C ∧
                    ∀ {z z' : RegularityStructures.SpaceTime},
                      0 < RegularityStructures.torusParabolicSize (z - z') →
                        0 < RegularityStructures.torusParabolicSize (z - 0) →
                          0 < RegularityStructures.torusParabolicSize (z' - 0) →
                            RegularityStructures.SingularIntLe
                                (fun (w : RegularityStructures.SpaceTime) ↦
                                  RegularityStructures.singularPow 3 z w *
                                      RegularityStructures.singularPow (1 + ν₁) z w *
                                    RegularityStructures.singularPow (1 + y₂) z' w)
                                (C * RegularityStructures.i3Psi2S (ν₁ + y₂) z z') ∧
                              RegularityStructures.SingularIntLe
                                  (fun (w : RegularityStructures.SpaceTime) ↦
                                    RegularityStructures.singularPow 3 0 w *
                                        RegularityStructures.singularPow (1 + ν₁) z w *
                                      RegularityStructures.singularPow (1 + y₂) z' w)
                                  (C * RegularityStructures.i3Psi2S (ν₁ + y₂) z z') ∧
                                RegularityStructures.SingularIntLe
                                    (fun (w : RegularityStructures.SpaceTime) ↦
                                      RegularityStructures.singularPow 3 z w *
                                            RegularityStructures.singularPow (1 + ν₁) z w *
                                          RegularityStructures.singularPow (1 + y₂) z' w *
                                        RegularityStructures.singularPow η z' w)
                                    (C * RegularityStructures.i3Psi2S (ν₁ + y₂ + η) z z') ∧
                                  RegularityStructures.SingularIntLe
                                      (fun (w : RegularityStructures.SpaceTime) ↦
                                        RegularityStructures.singularPow 3 0 w *
                                              RegularityStructures.singularPow (1 + ν₁) z w *
                                            RegularityStructures.singularPow (1 + y₂) z' w *
                                          RegularityStructures.singularPow η z' w)
                                      (C * RegularityStructures.i3Psi2S (ν₁ + y₂ + η) z z') ∧
                                    RegularityStructures.SingularIntLe
                                        (fun (w : RegularityStructures.SpaceTime) ↦
                                          RegularityStructures.singularPow 3 z w *
                                                RegularityStructures.singularPow (1 + ν₁) z w *
                                              RegularityStructures.singularPow (1 + y₂) z' w *
                                            RegularityStructures.singularPow η 0 w)
                                        (C * RegularityStructures.i3Psi2S (ν₁ + y₂ + η) z z') ∧
                                      RegularityStructures.SingularIntLe
                                        (fun (w : RegularityStructures.SpaceTime) ↦
                                          RegularityStructures.singularPow 3 0 w *
                                                RegularityStructures.singularPow (1 + ν₁) z w *
                                              RegularityStructures.singularPow (1 + y₂) z' w *
                                            RegularityStructures.singularPow η 0 w)
                                        (C * RegularityStructures.i3Psi2S (ν₁ + y₂ + η) z z'))
    (h_RegularityStructures_i3Psi2S_nonneg : ∀ (p : ℝ) (z z' : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.i3Psi2S p z z')
    (h_RegularityStructures_singularIntLe_mul_three : ∀ {a b c η : ℝ},
      0 < a →
        0 < b →
          a + b < 5 →
            0 < c →
              c < 5 →
                0 < η →
                  a + b + c = 5 + η →
                    ∃ (C : ℝ),
                      0 ≤ C ∧
                        ∀ (p q r : RegularityStructures.SpaceTime),
                          0 < RegularityStructures.torusParabolicSize (p - r) →
                            0 < RegularityStructures.torusParabolicSize (q - r) →
                              RegularityStructures.SingularIntLe
                                (fun (w : RegularityStructures.SpaceTime) ↦
                                  RegularityStructures.singularPow a p w *
                                      RegularityStructures.singularPow b q w *
                                    RegularityStructures.singularPow c r w)
                                (C *
                                  (RegularityStructures.torusParabolicSize (p - r) ^ (-η) +
                                    RegularityStructures.torusParabolicSize (q - r) ^ (-η))))
    (h_RegularityStructures_rpow_neg_flip_singularPow : ∀ {p : ℝ},
      0 ≤ p →
        ∀ {c w : RegularityStructures.SpaceTime},
          0 < RegularityStructures.torusParabolicSize (c - w) →
            RegularityStructures.torusParabolicSize (w - c) ^ (-p) ≤
              2 ^ p * RegularityStructures.singularPow p c w)
    (h_RegularityStructures_ae_torusParabolicSize_sub_pos : ∀ (z : RegularityStructures.SpaceTime),
      ∀ᵐ (w : RegularityStructures.SpaceTime), 0 < RegularityStructures.torusParabolicSize (z - w))
    (h_RegularityStructures_twoLevelLe_of_inner : ∀ {m : RegularityStructures.SpaceTime → ℝ}
      {g : RegularityStructures.SpaceTime → RegularityStructures.SpaceTime → ℝ}
      {V : RegularityStructures.SpaceTime → ℝ} {X : ℝ},
      (∀ (w : RegularityStructures.SpaceTime), 0 ≤ m w) →
        (∀ᵐ (w : RegularityStructures.SpaceTime), RegularityStructures.SingularIntLe (g w) (V w)) →
          RegularityStructures.SingularIntLe (fun (w : RegularityStructures.SpaceTime) ↦ m w * V w) X →
            RegularityStructures.TwoLevelLe (fun (w v : RegularityStructures.SpaceTime) ↦ m w * g w v) X)
    (h_RegularityStructures_singularPow_nonneg : ∀ (a : ℝ) (c w : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.singularPow a c w)
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ z z' : SpaceTime, 0 < torusParabolicSize (z - z') →
      0 < torusParabolicSize z → 0 < torusParabolicSize z' →
        TwoLevelLe (fun w v => Λ * i3Psi2N2Majorant (y₁ + δ) y₂ y₃ y₄ y₅ z z' w v)
          (Λ * C * i3Psi2S (1 + δ + y₁ + y₂ + y₃ + y₄ + y₅) z z') := by
  have hη : 0 < 1 + y₃ + y₄ + y₅ := by linarith
  have hν1 : 0 < y₁ + δ := by linarith
  obtain ⟨Ci, hCi, hi⟩ := h_RegularityStructures_singularIntLe_mul_three (a := 1 + y₅) (b := 1 + y₃) (c := 4 + y₄)
    (η := 1 + y₃ + y₄ + y₅) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hη (by ring)
  obtain ⟨Co, hCo, ho⟩ := h_RegularityStructures_outer_leaves_n2c (ν₁ := y₁ + δ) (y₂ := y₂) (η := 1 + y₃ + y₄ + y₅)
    hν1 (by linarith) hy₂ hη (by linarith)
  have nP : (0 : ℝ) ≤ 2 ^ (1 + y₃ + y₄ + y₅) := Real.rpow_nonneg (by norm_num) _
  have nQ : (0 : ℝ) ≤ 2 ^ (1 + y₃ + y₄ + y₅ + (y₁ + δ + y₂)) := Real.rpow_nonneg (by norm_num) _
  refine ⟨Ci * Co * (54 * 2 ^ (1 + y₃ + y₄ + y₅ + (y₁ + δ + y₂)) + 8 * 2 ^ (1 + y₃ + y₄ + y₅)),
    mul_nonneg (mul_nonneg hCi hCo) (by positivity), ?_⟩
  intro Λ hΛ z z' hzz hz hz'
  have pz0 : 0 < torusParabolicSize (z - 0) := by rwa [sub_zero]
  have pz'0 : 0 < torusParabolicSize (z' - 0) := by rwa [sub_zero]
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := ho hzz pz0 pz'0
  set η : ℝ := 1 + y₃ + y₄ + y₅ with hηdef
  set ν : ℝ := y₁ + δ + y₂ with hνdef
  set P : ℝ := 2 ^ η with hPdef
  set x1 : ℝ := torusParabolicSize (z - z') ^ (-η) with hx1
  set u1 : ℝ := torusParabolicSize (z - 0) ^ (-η) with hu1
  have nx1 : 0 ≤ x1 := Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _
  have nu1 : 0 ≤ u1 := Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _
  have nc : 0 ≤ 3 * x1 + u1 := by positivity
  let V : SpaceTime → ℝ := fun w => Ci * (3 * x1 + u1 +
    P * (3 * singularPow η z' w + singularPow η 0 w))
  let m : SpaceTime → ℝ := fun w => Λ *
    ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + (y₁ + δ)) z w *
      singularPow (1 + y₂) z' w)
  have hm : ∀ w, 0 ≤ m w := fun w => mul_nonneg hΛ (mul_nonneg (mul_nonneg (add_nonneg
    (h_RegularityStructures_singularPow_nonneg _ _ _) (h_RegularityStructures_singularPow_nonneg _ _ _)) (h_RegularityStructures_singularPow_nonneg _ _ _))
    (h_RegularityStructures_singularPow_nonneg _ _ _))
  have hg : ∀ᵐ w : SpaceTime ∂volume, SingularIntLe (fun v => (3 * singularPow (4 + y₄) z' v +
      singularPow (4 + y₄) 0 v) * singularPow (1 + y₅) z v * singularPow (1 + y₃) w v) (V w) := by
    filter_upwards [h_RegularityStructures_ae_torusParabolicSize_sub_pos z', h_RegularityStructures_ae_torusParabolicSize_sub_pos 0] with w a b
    have f1 := h_RegularityStructures_rpow_neg_flip_singularPow (p := η) hη.le a
    have f2 := h_RegularityStructures_rpow_neg_flip_singularPow (p := η) hη.le b
    have t1 := hi z w z' hzz (h_RegularityStructures_torusParabolicSize_sub_pos_symm a)
    have t2 := hi z w 0 pz0 (h_RegularityStructures_torusParabolicSize_sub_pos_symm b)
    have := ((t1.const_mul (c := 3) (by norm_num)).add t2).congr_fun
      (g := fun v => (3 * singularPow (4 + y₄) z' v + singularPow (4 + y₄) 0 v) *
        singularPow (1 + y₅) z v * singularPow (1 + y₃) w v) (fun v => by ring)
    refine this.mono_right ?_
    simp only [V, sub_zero] at f2 ⊢
    have g1 : torusParabolicSize (w - z') ^ (-η) ≤ P * singularPow η z' w := f1
    have g2 : torusParabolicSize w ^ (-η) ≤ P * singularPow η 0 w := f2
    have := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left g1
      (by norm_num : (0 : ℝ) ≤ 3)) g2) hCi
    simp only [hx1, hu1, sub_zero] at *
    nlinarith
  have S0 := h_RegularityStructures_i3Psi2S_nonneg ν z z'
  have S1 := h_RegularityStructures_i3Psi2S_nonneg (ν + η) z z'
  have hν0 : 0 < ν := by rw [hνdef]; linarith
  have hSS := h_RegularityStructures_i3Psi2S_mul_le (a := η) (b := ν) hη.le hν0.le (by linarith) hzz pz0 pz'0
  rw [show η + ν = ν + η by ring] at hSS
  have hnc : 3 * x1 + u1 ≤ 3 * i3Psi2S η z z' := by
    have : 0 ≤ torusParabolicSize (z' - 0) ^ (-η) :=
      Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _
    simp only [i3Psi2S, hx1, hu1]
    linarith
  have hncS : (3 * x1 + u1) * i3Psi2S ν z z' ≤ 3 * (9 * 2 ^ (η + ν) * i3Psi2S (ν + η) z z') := by
    calc (3 * x1 + u1) * i3Psi2S ν z z' ≤ (3 * i3Psi2S η z z') * i3Psi2S ν z z' :=
          mul_le_mul_of_nonneg_right hnc S0
      _ = 3 * (i3Psi2S η z z' * i3Psi2S ν z z') := by ring
      _ ≤ 3 * (9 * 2 ^ (η + ν) * i3Psi2S (ν + η) z z') := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [show η + ν = ν + η by ring]; exact hSS
  have sA := (o1.add o2).const_mul nc
  have sB := (((o3.add o4).const_mul (c := 3) (by norm_num)).add (o5.add o6)).const_mul
    (c := P) (by positivity)
  have sT := (sA.add sB).const_mul (mul_nonneg hΛ hCi)
  have hH : SingularIntLe (fun w => m w * V w)
      (Λ * (Ci * Co * (54 * 2 ^ (η + ν) + 8 * 2 ^ η)) *
        i3Psi2S (1 + δ + y₁ + y₂ + y₃ + y₄ + y₅) z z') := by
    have e : 1 + δ + y₁ + y₂ + y₃ + y₄ + y₅ = ν + η := by rw [hνdef, hηdef]; ring
    rw [e]
    refine (sT.congr_fun (g := fun w => m w * V w) (fun w => by simp only [m, V]; ring)).mono_right
      ?_
    calc Λ * Ci * ((3 * x1 + u1) * (Co * i3Psi2S ν z z' + Co * i3Psi2S ν z z') +
          P * (3 * (Co * i3Psi2S (ν + η) z z' + Co * i3Psi2S (ν + η) z z') +
            (Co * i3Psi2S (ν + η) z z' + Co * i3Psi2S (ν + η) z z')))
        = (Λ * (Ci * Co)) * (2 * ((3 * x1 + u1) * i3Psi2S ν z z') +
            8 * P * i3Psi2S (ν + η) z z') := by ring
      _ ≤ (Λ * (Ci * Co)) * (2 * (3 * (9 * 2 ^ (η + ν) * i3Psi2S (ν + η) z z')) +
            8 * P * i3Psi2S (ν + η) z z') := by
          have hP : 0 ≤ Λ * (Ci * Co) := mul_nonneg hΛ (mul_nonneg hCi hCo)
          gcongr
      _ = _ := by rw [hPdef]; ring
  have hG := h_RegularityStructures_twoLevelLe_of_inner (m := m) (g := fun w v => (3 * singularPow (4 + y₄) z' v +
    singularPow (4 + y₄) 0 v) * singularPow (1 + y₅) z v * singularPow (1 + y₃) w v) (V := V)
    hm hg hH
  exact hG.congr_fun (fun w v => by simp only [m, i3Psi2N2Majorant]; ring)
end RegularityStructures
end
