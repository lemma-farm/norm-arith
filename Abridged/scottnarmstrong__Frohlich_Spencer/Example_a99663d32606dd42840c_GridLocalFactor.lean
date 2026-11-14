module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Tactic.Positivity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Group.Support
public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Notation
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Tactic.Common
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Push

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v4cb506007089.FroehlichSpencer.BKT.Generic.StripWeight ====
public section
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Strip weights (generic core, the shared weight interface)

The edge weight of FS81 §4 and §6–7 is an analytic interpolation `w` of a bond weight.

This module states them as three predicates; the instances
are theorems (Gaussian weight: `Generic/StripWeightScaling.lean`; Appendix B and C interpolations:
`Generic/Instances/*`).

* `IsStripWeight w W c`: `w` is real and positive on `ℝ`, analytic, even and conjugation-symmetric
  on the closed strip `|Im z| ≤ W`, satisfies the translation bound (4.10)(iii)/(c)
  `|w(t + iu)/w(t)| ≤ e^{c(u)}` for `|u| ≤ W`, and is bounded on the strip by a single integrable
  majorant `B(t)` that vanishes at infinity (the contour-end condition of FS81 Lemma 4.3).

The
  translation cost `c` is even with `c(0) = 0`.
* `HasLogDerivBounds w W M`: property (d) for `m = 1, 2`,
  `|(log w)^{(m)}(t + iu) − (log w)^{(m)}(t)| ≤ M(u)`.
* `HasCurvatureBound w κ`: the one-sided curvature bound of FS81 (6.28),
  `log w(t + s) ≥ log w(t) + (log w)'(t) s − κ s²` on the real axis.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT.Generic
open MeasureTheory Complex Filter Topology

/-- FS81 Appendix B/C property (d), `m = 1, 2`. -/
structure HasLogDerivBounds (w : ℂ → ℂ) (W : ℝ) (M : ℝ → ℝ) : Prop where
  logDeriv_sub_le : ∀ t u : ℝ, |u| ≤ W →
    ‖logDeriv w ((t : ℂ) + (u : ℂ) * I) - logDeriv w t‖ ≤ M u
  deriv_logDeriv_sub_le : ∀ t u : ℝ, |u| ≤ W →
    ‖deriv (logDeriv w) ((t : ℂ) + (u : ℂ) * I) - deriv (logDeriv w) t‖ ≤ M u

namespace IsStripWeight
variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

end IsStripWeight
end FroehlichSpencer.BKT.Generic
end

end
end

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v4cb506007089.FroehlichSpencer.BKT.Generic.LocalFactorBounds ====
public section
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Generic local-factor derivative bounds

Their first two derivatives are
controlled by `HasLogDerivBounds`; the strip-weight ratio estimate supplies the norm bound.

The
Bessel bridge identifies these definitions with the existing rotator factors and converts the
rotator logarithmic-derivative estimate to the generic interface.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT.Generic
open Complex
open scoped Real
variable {ι : Type*}
/-- One normalized edge factor, with the cost normalization from `Generic.LocalFactor`. -/
def normalizedEdgeFactor (w : ℂ → ℂ) (c : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℂ :=
  w ((x : ℂ) + (a : ℂ) * I) / w x * Complex.exp (-((c a : ℝ) : ℂ))
/-- The logarithmic-derivative difference for a translated edge factor. -/
def factorLogDeriv (w : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  logDeriv w (z + (a : ℂ) * I) - logDeriv w z
/-- The derivative of `factorLogDeriv`, again written without choosing a branch of `log w`. -/
def factorLogDeriv2 (w : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  deriv (logDeriv w) (z + (a : ℂ) * I) - deriv (logDeriv w) z
/-- The normalized product along a real line of edge variables. -/
def genericEdgeProduct (w : ℂ → ℂ) (c : ℝ → ℝ) (S : Finset ι)
    (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∏ e ∈ S, normalizedEdgeFactor w c (a e) (x e + μ * θ e)
/-- The logarithmic derivative of a finite edge product along its line. -/
def genericEdgeLogDeriv (w : ℂ → ℂ) (S : Finset ι)
    (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∑ e ∈ S, (θ e : ℂ) *
    factorLogDeriv w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)
/-- The derivative of `genericEdgeLogDeriv` along its line. -/
def genericEdgeLogDeriv2 (w : ℂ → ℂ) (S : Finset ι)
    (a x θ : ι → ℝ) (μ : ℝ) : ℂ :=
  ∑ e ∈ S, (θ e : ℂ) ^ 2 *
    factorLogDeriv2 w (a e) ((x e : ℂ) + (μ : ℂ) * θ e)

section Calculus
variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

end Calculus
section Bounds
variable {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ} [DecidableEq ι]

end Bounds
section LocalFunctionals
variable {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ} [DecidableEq ι]

end LocalFunctionals
section BesselBridge



end BesselBridge
end FroehlichSpencer.BKT.Generic
end

end
end

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_a99663d32606dd42840c_GridLocalFactor ====
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The per-factor Taylor step for a locally analytic weight

The generic T1.5 per-factor Taylor bound `one_add_mul_lineFactor_ge` (FS81 (6.30)–(6.37);
`Generic/Moment/Taylor.lean`, `Generic/LocalFactorBounds.lean`) is stated for `IsStripWeight`. Its
proof uses only the local strip clauses: analyticity on the strip, the ratio bound, the cost
normalization and nonvanishing on the real axis. The integrable real-line majorant of
`IsStripWeight` is never used. That majorant fails for the periodic clock weight
`exp(β cos(z/N))`.

This file packages the local clauses as `IsLocalStripWeight` and proves that the clock weight
satisfies them (`clockEdgeWeight_isLocalStripWeight`). It then repeats the generic derivative
bounds and the Taylor step verbatim under the weaker hypothesis (suffix `_loc`):
* `genericLocalF_bounds_loc`, `lineFactor_derivs_loc`;
* **`one_add_mul_lineFactor_ge_loc`**: `(1 + z f(0)) exp(z f'(0)/(1 + z f(0)) − err) ≤ 1 + z f(1)`.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT.Clock.Disorder
open Complex
open scoped Real
open FroehlichSpencer.BKT.Generic

variable {ι : Type*}
/-- The local clauses of a strip weight: those used by the T1.5 per-factor Taylor step. -/
structure IsLocalStripWeight (w : ℂ → ℂ) (W : ℝ) (c : ℝ → ℝ) : Prop where
  width_nonneg : 0 ≤ W
  ofReal_ne_zero : ∀ x : ℝ, w x ≠ 0
  analyticAt : ∀ z : ℂ, |z.im| ≤ W → AnalyticAt ℂ w z
  even : ∀ z : ℂ, |z.im| ≤ W → w (-z) = w z
  conj : ∀ z : ℂ, |z.im| ≤ W → (starRingEnd ℂ) (w z) = w ((starRingEnd ℂ) z)
  ratio_le : ∀ t u : ℝ, |u| ≤ W → ‖w ((t : ℂ) + (u : ℂ) * I) / w t‖ ≤ Real.exp (c u)
  cost_even : ∀ u, c (-u) = c u
  cost_zero : c 0 = 0

section Calculus
variable {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

end Calculus
section Bounds
variable {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ} [DecidableEq ι]


set_option linter.unusedVariables false in
/-- One generic finite product and its first two line derivatives. -/
theorem genericEdgeProduct_bounds_loc
    (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    (hlog : HasLogDerivBounds w W M)
    {S : Finset ι} (a x θ : ι → ℝ) (A T m μ : ℝ)
    (haA : ∀ e ∈ S, |a e| ≤ A) (hAW : A ≤ W)
    (hθT : ∀ e ∈ S, |θ e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) 
    (h_FroehlichSpencer_BKT_Clock_Disorder_hasDerivAt_deriv_genericEdgeProduct_loc : ∀ {ι : Type u_1} {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} [DecidableEq ι],
      FroehlichSpencer.BKT.Clock.Disorder.IsLocalStripWeight w W c →
        (∀ (z : ℂ), |z.im| ≤ W → w z ≠ 0) →
          ∀ {S : Finset ι} (a x θ : ι → ℝ),
            (∀ e ∈ S, |a e| ≤ W) →
              ∀ (μ₀ : ℝ),
                HasDerivAt (deriv (FroehlichSpencer.BKT.Generic.genericEdgeProduct w c S a x θ))
                  ((FroehlichSpencer.BKT.Generic.genericEdgeLogDeriv w S a x θ μ₀ ^ 2 +
                      FroehlichSpencer.BKT.Generic.genericEdgeLogDeriv2 w S a x θ μ₀) *
                    FroehlichSpencer.BKT.Generic.genericEdgeProduct w c S a x θ μ₀)
                  μ₀)
    (h_FroehlichSpencer_BKT_Generic_norm_genericEdgeLogDeriv_bounds : ∀ {ι : Type u_1} {w : ℂ → ℂ} {W : ℝ} {M : ℝ → ℝ},
      FroehlichSpencer.BKT.Generic.HasLogDerivBounds w W M →
        ∀ {S : Finset ι} (a x θ : ι → ℝ) (A T m μ : ℝ),
          (∀ e ∈ S, |a e| ≤ A) →
            A ≤ W →
              (∀ e ∈ S, |θ e| ≤ T) →
                (∀ (u : ℝ), |u| ≤ A → M u ≤ m) →
                  ‖FroehlichSpencer.BKT.Generic.genericEdgeLogDeriv w S a x θ μ‖ ≤
                      (↑S.card : ℝ) * m * T ∧
                    ‖FroehlichSpencer.BKT.Generic.genericEdgeLogDeriv2 w S a x θ μ‖ ≤
                      (↑S.card : ℝ) * m * T ^ 2)
    (h_FroehlichSpencer_BKT_Clock_Disorder_deriv_genericEdgeProduct_loc : ∀ {ι : Type u_1} {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} [DecidableEq ι],
      FroehlichSpencer.BKT.Clock.Disorder.IsLocalStripWeight w W c →
        (∀ (z : ℂ), |z.im| ≤ W → w z ≠ 0) →
          ∀ {S : Finset ι} (a x θ : ι → ℝ),
            (∀ e ∈ S, |a e| ≤ W) →
              deriv (FroehlichSpencer.BKT.Generic.genericEdgeProduct w c S a x θ) = fun (μ : ℝ) ↦
                FroehlichSpencer.BKT.Generic.genericEdgeLogDeriv w S a x θ μ *
                  FroehlichSpencer.BKT.Generic.genericEdgeProduct w c S a x θ μ)
    (h_FroehlichSpencer_BKT_Clock_Disorder_norm_genericEdgeProduct_le_one_loc : ∀ {ι : Type u_1} {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ},
      FroehlichSpencer.BKT.Clock.Disorder.IsLocalStripWeight w W c →
        ∀ {S : Finset ι} (a x θ : ι → ℝ) (μ : ℝ),
          (∀ e ∈ S, |a e| ≤ W) → ‖FroehlichSpencer.BKT.Generic.genericEdgeProduct w c S a x θ μ‖ ≤ 1)
    :
    ‖genericEdgeProduct w c S a x θ μ‖ ≤ 1 ∧
      ‖deriv (genericEdgeProduct w c S a x θ) μ‖ ≤ S.card * m * T ∧
      ‖deriv (deriv (genericEdgeProduct w c S a x θ)) μ‖ ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
  have haW : ∀ e ∈ S, |a e| ≤ W := fun e he => (haA e he).trans hAW
  have hP := h_FroehlichSpencer_BKT_Clock_Disorder_norm_genericEdgeProduct_le_one_loc hw a x θ μ haW
  have hQ := h_FroehlichSpencer_BKT_Generic_norm_genericEdgeLogDeriv_bounds hlog a x θ A T m μ haA hAW hθT hM
  have hderiv : ‖deriv (genericEdgeProduct w c S a x θ) μ‖ ≤ S.card * m * T := by
    rw [h_FroehlichSpencer_BKT_Clock_Disorder_deriv_genericEdgeProduct_loc hw hnzero a x θ haW, norm_mul]
    calc ‖genericEdgeLogDeriv w S a x θ μ‖ *
          ‖genericEdgeProduct w c S a x θ μ‖ ≤ (S.card * m * T) * 1 :=
        mul_le_mul hQ.1 hP (norm_nonneg _) ((norm_nonneg _).trans hQ.1)
      _ = S.card * m * T := mul_one _
  have hderiv2 :
      ‖deriv (deriv (genericEdgeProduct w c S a x θ)) μ‖ ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
    rw [(h_FroehlichSpencer_BKT_Clock_Disorder_hasDerivAt_deriv_genericEdgeProduct_loc hw hnzero a x θ haW μ).deriv, norm_mul]
    have hsq : ‖genericEdgeLogDeriv w S a x θ μ‖ ^ 2 ≤
        (S.card * m * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hQ.1 2
    have hNN : (S.card : ℝ) ≤ S.card ^ 2 := by
      rcases Nat.eq_zero_or_pos S.card with h0 | hpos
      · rw [h0]
        norm_num
      · have : (1 : ℝ) ≤ S.card := by exact_mod_cast hpos
        nlinarith
    have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
    have hM2 : m ^ 2 ≤ m := by nlinarith
    have hsum :
        ‖genericEdgeLogDeriv w S a x θ μ ^ 2 +
          genericEdgeLogDeriv2 w S a x θ μ‖ ≤
            (S.card * m * T) ^ 2 + S.card * m * T ^ 2 := by
      calc _ ≤ ‖genericEdgeLogDeriv w S a x θ μ‖ ^ 2 +
            ‖genericEdgeLogDeriv2 w S a x θ μ‖ := by
              refine (norm_add_le _ _).trans ?_
              rw [norm_pow]
        _ ≤ _ := add_le_add hsq hQ.2
    have hkey : (S.card * m * T) ^ 2 + S.card * m * T ^ 2 ≤
        2 * S.card ^ 2 * m * T ^ 2 := by
      have h1 : (S.card * m * T) ^ 2 = S.card ^ 2 * T ^ 2 * m ^ 2 := by ring
      have h2 : S.card ^ 2 * T ^ 2 * m ^ 2 ≤ S.card ^ 2 * T ^ 2 * m :=
        mul_le_mul_of_nonneg_left hM2 (by positivity)
      have h3 : S.card * m * T ^ 2 ≤ S.card ^ 2 * m * T ^ 2 := by
        have := mul_le_mul_of_nonneg_right hNN (mul_nonneg hm0 hT2)
        nlinarith [this]
      nlinarith
    calc
      ‖genericEdgeLogDeriv w S a x θ μ ^ 2 +
          genericEdgeLogDeriv2 w S a x θ μ‖ *
          ‖genericEdgeProduct w c S a x θ μ‖ ≤
        ((S.card * m * T) ^ 2 + S.card * m * T ^ 2) * 1 :=
          mul_le_mul hsum hP (norm_nonneg _) (by positivity)
      _ ≤ 2 * S.card ^ 2 * m * T ^ 2 := by rw [mul_one]; exact hkey
  exact ⟨hP, hderiv, hderiv2⟩
end Bounds
section LocalFunctionals
end LocalFunctionals
end FroehlichSpencer.BKT.Clock.Disorder
end
