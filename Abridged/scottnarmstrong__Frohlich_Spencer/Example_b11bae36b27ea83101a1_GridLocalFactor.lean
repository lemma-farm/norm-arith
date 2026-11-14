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

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v24369c863432.FroehlichSpencer.BKT.Generic.EdgeRatio ====
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
# The edge ratio of a complex translation (generic core)

`R_b(x) = ∏_e w(x_e + i b_e) / w(x_e)`,  with `x = ∇φ` and `b = ∇a`.

This module records the algebra of `R_b` that the generic translation step
(`Generic/ProductTranslation.lean`) needs: `R_0 = 1`, and `R` is multiplicative over shifts with
pairwise disjoint supports.

The second fact is FS81 (6.20) in the form used by KP §2.3.3: spin
waves of distinct densities have disjoint gradient supports, so the joint translation factors
into one ratio per density.

Both need only that `w` does not vanish at the real points `x_e`.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT.Generic
open Complex
variable {E : Type*} [Fintype E]
/-- FS81 (4.38)/(6.4): the edge ratio `R_b(x) = ∏_e w(x_e + i b_e) / w(x_e)`. -/
def edgeRatio (w : ℂ → ℂ) (b x : E → ℝ) : ℂ :=
  ∏ e, w ((x e : ℂ) + (b e : ℂ) * I) / w (x e)

end FroehlichSpencer.BKT.Generic
end

end
end

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v24369c863432.FroehlichSpencer.BKT.Generic.LocalFactor ====
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
# Normalized local factors and the translation energy (generic core)

Fix a translation cost `c : ℝ → ℝ`, the exponent of FS81 (4.10)(iii)
`|w(t + iu)/w(t)| ≤ e^{c(u)}`.

Normalizing every edge ratio by `e^{-c}` splits the translated factor
of `Generic/Translation.lean` into a scalar and a bounded function:

`e^{-⟨a, ϱ⟩} ½(e^{iθ} R_{Da} + e^{-iθ} R_{-Da}) = e^{-E_c(a, ϱ)} F`,

with the **translation energy** `E_c(a, ϱ) = ⟨a, ϱ⟩ - ∑_e c(D a(e))` (KP (2.12) when
`c(u) = βu²/2`; FS81 (4.41) when `c(u) = c(β)u²`) and the **local factor**
`F = ½(e^{iθ} P_{Da} + e^{-iθ} P_{-Da})`, `P_b = R_b e^{-∑ c(b)}` (FS81 (6.18)–(6.19);
`F = F₂ cos θ - F₁ sin θ` in FS81's notation, compare `Rotator.Contour.localF₁`, `localF₂`).

* `integral_prod_add_mul_cos_eq_localFactor`: the generic translation step in normalized form.
* `norm_localFactor_le_one`: `|F| ≤ 1` under the ratio bound (FS81 (6.21)).
* `localFactor_im_eq_zero`: `F` is real when `w` commutes with conjugation on the strip (FS81
  (4.11)).
* `localFactor_neg`: `F(-x, -θ) = F(x, θ)` when `w` is even on the strip (FS81 Theorem 6.1 (2)).
* `localFactor_zero`: without a wave, `F = cos θ`.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT.Generic
open MeasureTheory Complex
variable {V E : Type*} [Fintype V] [Fintype E]

/-- FS81 (6.19): the normalized edge ratio `P_b(x) = R_b(x) e^{-∑_e c(b_e)}`. -/
def normalizedEdgeRatio (w : ℂ → ℂ) (c : ℝ → ℝ) (b x : E → ℝ) : ℂ :=
  edgeRatio w b x * Complex.exp (-((∑ e, c (b e) : ℝ) : ℂ))
/-- FS81 (6.18): the local factor `F = ½(e^{iθ} P_b(x) + e^{-iθ} P_{-b}(x))`. -/
def localFactor (w : ℂ → ℂ) (c : ℝ → ℝ) (b x : E → ℝ) (θ : ℝ) : ℂ :=
  (Complex.exp (I * θ) * normalizedEdgeRatio w c b x +
    Complex.exp (-(I * θ)) * normalizedEdgeRatio w c (-b) x) / 2

end FroehlichSpencer.BKT.Generic
end

end
end

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v24369c863432.FroehlichSpencer.BKT.Generic.StripWeight ====
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

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v24369c863432.FroehlichSpencer.BKT.Generic.Moment.Taylor ====
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
# Second-order Taylor bound for one renormalized factor along the real shift (generic core)

Along the
real shift every renormalized factor `1 + z F` is followed on the line
`t ↦ (x + t y, ph + t s)`: edge gradients move by `t y` (the edge field `θ` of FS81 (6.10)–(6.13))
and the phase moves by `t s` (the reduced phase `[σ(ϱ)]_{2π}`).

This module proves

This is the second-order Taylor bound for `log(1 + z f)`, using `|f| ≤ 1` (so `1 + z f ≥ 7/8`),
  `|f'| ≤ 2(N m T + |s|)` and `|f''| ≤ 4 N² m T² + 4 |s| N m T + 2 s²`;
* `lineFactor_neg`, `deriv_lineFactor_neg`: the parity that makes the first-order term odd in the
  field (FS81 Theorem 6.1 (2));
* `localFactor_add_two_pi_mul`: the local factor only sees the phase modulo `2π`.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT.Generic
open Complex
/-! ## The real second-order Taylor bound -/
/-- **Second-order Taylor lower bound** on `[0, 1]`: `g(0) + g'(0) − M/2 ≤ g(1)` when
`|g''| ≤ M`. -/
axiom taylor_lower_bound {g g' g'' : ℝ → ℝ} {M : ℝ}
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g' (g'' t) t)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g'' t| ≤ M) : g 0 + g' 0 - M / 2 ≤ g 1
/-! ## The local factor along a line -/
variable {E : Type*} [Fintype E] {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ}
/-- The (real) local factor along the line `t ↦ (x + t y, ph + t s)`. -/
def lineFactor (w : ℂ → ℂ) (c : ℝ → ℝ) (b x y : E → ℝ) (ph s t : ℝ) : ℝ :=
  (localFactor w c b (x + t • y) (ph + t * s)).re

/-! ## The comparison of one factor -/

end FroehlichSpencer.BKT.Generic
end

end
end

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_b11bae36b27ea83101a1_GridLocalFactor ====
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

end Bounds
section LocalFunctionals
variable {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ} [DecidableEq ι]

end LocalFunctionals
variable {E : Type*} [Fintype E] {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ}
axiom lineFactor_derivs_loc (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) (hlog : HasLogDerivBounds w W M)
    (b x y : E → ℝ) (ph s A T m : ℝ) (hbA : ∀ e, |b e| ≤ A) (hAW : A ≤ W)
    (hyT : ∀ e, b e ≠ 0 → |y e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) :
    ∃ f' f'' : ℝ → ℝ,
      (∀ t, HasDerivAt (lineFactor w c b x y ph s) (f' t) t) ∧
      (∀ t, HasDerivAt f' (f'' t) t) ∧
      (∀ t, |lineFactor w c b x y ph s t| ≤ 1) ∧
      (∀ t, |f' t| ≤ 2 * ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) + 2 * |s|) ∧
      ∀ t, |f'' t| ≤ 4 * ((Finset.univ.filter fun e => b e ≠ 0).card ^ 2 * m * T ^ 2) +
        4 * |s| * ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) + 2 * s ^ 2
/-- **One factor along the real shift** (FS81 (6.35)–(6.37)): for `|z| ≤ 1/8`,
`(1 + z f(0)) exp(z f'(0)/(1 + z f(0)) − 8|z|(s² + (N m T)² + N² m T²)) ≤ 1 + z f(1)`, with
`f = lineFactor` and `N` the number of edges carrying the shift. -/
theorem one_add_mul_lineFactor_ge_loc (hw : IsLocalStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) (hlog : HasLogDerivBounds w W M)
    (b x y : E → ℝ) (ph s z A T m : ℝ) (hbA : ∀ e, |b e| ≤ A) (hAW : A ≤ W)
    (hyT : ∀ e, b e ≠ 0 → |y e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) (hz : |z| ≤ 1 / 8) :
    (1 + z * lineFactor w c b x y ph s 0) *
        Real.exp (z * deriv (lineFactor w c b x y ph s) 0 /
            (1 + z * lineFactor w c b x y ph s 0) -
          8 * |z| * (s ^ 2 + ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) ^ 2 +
            (Finset.univ.filter fun e => b e ≠ 0).card ^ 2 * m * T ^ 2)) ≤
      1 + z * lineFactor w c b x y ph s 1 := by
  obtain ⟨f', f'', hf, hf', hf0, hf'b, hf''b⟩ :=
    lineFactor_derivs_loc hw hnzero hlog b x y ph s A T m hbA hAW hyT hm0 hm1 hM
  set f := lineFactor w c b x y ph s with hfdef
  set N : ℝ := ((Finset.univ.filter fun e => b e ≠ 0).card : ℝ)
  set B := N * m * T with hBdef
  set Q := s ^ 2 + B ^ 2 + N ^ 2 * m * T ^ 2 with hQ
  have hQ2 : 0 ≤ N ^ 2 * m * T ^ 2 := by positivity
  have hz0 := abs_nonneg z
  have hD : ∀ t, 7 / 8 ≤ 1 + z * f t := by
    intro t
    have h1 : |z * f t| ≤ 1 / 8 := by
      rw [abs_mul]
      calc |z| * |f t| ≤ 1 / 8 * 1 := mul_le_mul hz (hf0 t) (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := mul_one _
    linarith [neg_abs_le (z * f t)]
  have hDpos : ∀ t, 0 < 1 + z * f t := fun t => by linarith [hD t]
  -- `g = log (1 + z f)` and its derivatives
  set g : ℝ → ℝ := fun t => Real.log (1 + z * f t) with hg
  set g' : ℝ → ℝ := fun t => z * f' t / (1 + z * f t) with hg'
  set g'' : ℝ → ℝ := fun t =>
    (z * f'' t * (1 + z * f t) - z * f' t * (z * f' t)) / (1 + z * f t) ^ 2 with hg''
  have hgd : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h := ((hf t).const_mul z).const_add 1
    exact ((Real.hasDerivAt_log (hDpos t).ne').comp t h).congr_deriv (by
      show (1 + z * f t)⁻¹ * (z * f' t) = z * f' t / (1 + z * f t)
      rw [div_eq_inv_mul])
  have hg'd : ∀ t, HasDerivAt g' (g'' t) t := by
    intro t
    have hn := (hf' t).const_mul z
    have hd := ((hf t).const_mul z).const_add 1
    have h := hn.div hd (hDpos t).ne'
    convert h using 1
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g'' t| ≤ 16 * |z| * Q := by
    intro t _
    have hDt := hD t
    have hDp := hDpos t
    have h1 := hf'b t
    have h2 := hf''b t
    have hs := abs_nonneg s
    have hsplit : g'' t = z * f'' t / (1 + z * f t) - (z * f' t) ^ 2 / (1 + z * f t) ^ 2 := by
      simp only [hg'']
      field_simp
    rw [hsplit]
    have a1 : |z * f'' t / (1 + z * f t)| ≤ 8 / 7 * (|z| * |f'' t|) := by
      rw [abs_div, abs_mul, abs_of_pos hDp, div_le_iff₀ hDp]
      nlinarith [mul_nonneg hz0 (abs_nonneg (f'' t))]
    have a2 : |(z * f' t) ^ 2 / (1 + z * f t) ^ 2| ≤ 64 / 49 * (z ^ 2 * f' t ^ 2) := by
      rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity),
        div_le_iff₀ (by positivity)]
      have hD2 : (7 / 8 : ℝ) ^ 2 ≤ (1 + z * f t) ^ 2 := by
        exact pow_le_pow_left₀ (by norm_num) hDt 2
      have : 0 ≤ z ^ 2 * f' t ^ 2 := by positivity
      nlinarith
    have hzz : z ^ 2 ≤ |z| / 8 := by
      rw [← sq_abs]
      nlinarith
    have hf'sq : f' t ^ 2 ≤ 8 * B ^ 2 + 8 * s ^ 2 := by
      have : |f' t| ^ 2 ≤ (2 * B + 2 * |s|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at this
      nlinarith [sq_abs s, sq_nonneg (B - |s|)]
    have hf''b' : |f'' t| ≤ 4 * (N ^ 2 * m * T ^ 2) + 2 * B ^ 2 + 4 * s ^ 2 := by
      nlinarith [sq_abs s, sq_nonneg (B - |s|)]
    calc |z * f'' t / (1 + z * f t) - (z * f' t) ^ 2 / (1 + z * f t) ^ 2|
        ≤ |z * f'' t / (1 + z * f t)| + |(z * f' t) ^ 2 / (1 + z * f t) ^ 2| :=
          abs_sub _ _
      _ ≤ 8 / 7 * (|z| * |f'' t|) + 64 / 49 * (z ^ 2 * f' t ^ 2) := add_le_add a1 a2
      _ ≤ 8 / 7 * (|z| * (4 * (N ^ 2 * m * T ^ 2) + 2 * B ^ 2 + 4 * s ^ 2)) +
          64 / 49 * (|z| / 8 * (8 * B ^ 2 + 8 * s ^ 2)) := by
          gcongr
      _ ≤ 16 * |z| * Q := by
          simp only [hQ]
          nlinarith [mul_nonneg hz0 hQ2, mul_nonneg hz0 (sq_nonneg B),
            mul_nonneg hz0 (sq_nonneg s)]
  have htay := taylor_lower_bound (fun t _ => hgd t) (fun t _ => hg'd t) hbound
  have hderiv : deriv f 0 = f' 0 := (hf 0).deriv
  rw [hderiv]
  have hexp1 : Real.exp (g 1) = 1 + z * f 1 := Real.exp_log (hDpos 1)
  have hexp0 : Real.exp (g 0) = 1 + z * f 0 := Real.exp_log (hDpos 0)
  calc (1 + z * f 0) * Real.exp (z * f' 0 / (1 + z * f 0) - 8 * |z| * Q)
      = Real.exp (g 0 + g' 0 - 16 * |z| * Q / 2) := by
        show _ = Real.exp (g 0 + z * f' 0 / (1 + z * f 0) - 16 * |z| * Q / 2)
        rw [show g 0 + z * f' 0 / (1 + z * f 0) - 16 * |z| * Q / 2 =
            g 0 + (z * f' 0 / (1 + z * f 0) - 8 * |z| * Q) by ring, Real.exp_add, hexp0]
    _ ≤ Real.exp (g 1) := Real.exp_le_exp.mpr htay
    _ = 1 + z * f 1 := hexp1
end FroehlichSpencer.BKT.Clock.Disorder
end
