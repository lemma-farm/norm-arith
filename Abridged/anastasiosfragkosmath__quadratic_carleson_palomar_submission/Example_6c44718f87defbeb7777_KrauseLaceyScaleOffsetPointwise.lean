import Mathlib
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.Rat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.Definitions ====
section
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Definitions from the quadratic Carleson endpoint paper

This file records foundational objects from Sections 2 and 3 of the paper.
-/
open Filter MeasureTheory Set
open scoped Topology
namespace QuadraticCarleson
/-- The paper's notation `e(s) = exp(2 π i s)`. -/
noncomputable def phase (s : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)

/-- The quadratic Hilbert-transform integral truncated at distance `ε` from
the singularity. -/
noncomputable def quadraticHilbertTrunc
    (modulation ε : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t in {t : ℝ | ε < |t|}, f (x - t) * phase (modulation * t ^ 2) / (t : ℂ)
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveDyadicKernel ====
section
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The dyadic kernels used in the positive estimate

This file records the elementary, exact part of the dyadic decomposition of
the quadratic Hilbert kernel.  The quotient defining a dyadic piece is given
the value zero at the origin; this is not an arbitrary extension, since the
numerator vanishes on a whole neighbourhood of the origin.
-/
open Function Set
open scoped ContDiff Topology
namespace QuadraticCarleson
/- The bump supplied by `ContDiffBump` is one on the inner closed ball and is
supported in the outer open ball.  With these radii those balls are exactly
the two intervals required in the paper. -/
noncomputable def dyadicCutoffData : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
noncomputable def dyadicCutoff : ℝ → ℝ := dyadicCutoffData

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.QuadraticCenteredMaximal ====
section
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# One-dimensional centered maximal estimates

The fixed-height quadratic `TT*` argument uses a one-dimensional centered
maximal estimate. The covering argument below proves the needed weak estimate
directly from Mathlib's Vitali theorem, with an explicit constant.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace QuadraticCarleson
noncomputable def centeredAverage (r : ℝ) (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in closedBall x r, f y) / ENNReal.ofReal (2 * r)
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.HardyLittlewoodMaximal ====
section
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The centered Hardy--Littlewood maximal operator on the real line

We use positive rational radii.  This makes the pointwise supremum measurably
countable while retaining arbitrarily small and arbitrarily large intervals.
The weak `(1,1)` estimate is obtained from the bounded-radius Vitali estimate
in `QuadraticCenteredMaximal` and continuity of measure from below.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace QuadraticCarleson
/-- Positive rational radii, used as a countable cofinal family. -/
abbrev PositiveRational := {q : ℚ // 0 < q}
noncomputable def centeredHardyLittlewoodMaximal (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : PositiveRational, centeredAverage (q : ℝ) f x
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.FiniteModulationKernelComparison ====
section
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The finite low-modulation block versus maximal truncations

This is the elementary pointwise reduction at the start of the proof of the
finite-modulation weak-type corollary in the accompanying article
([arXiv:2609.04101v1](https://arxiv.org/abs/2609.04101v1)). A
consecutive block of the paper's smooth dyadic kernels telescopes.  Replacing
its two smooth cutoffs by sharp cutoffs produces the difference of two
quadratic Hilbert truncations; the two transition annuli are controlled by
the centered Hardy--Littlewood maximal function.

The later sparse input in the paper is [Krause--Lacey, Theorem 1.1], namely a
uniform sparse `(1,p)` estimate for the maximally truncated quadratic Hilbert
transform.  Mathlib has no Carleson or oscillatory sparse-bound development,
and the project currently only defines the abstract sparse premise in
`FiniteSparseMaximal`.  Accordingly, this file proves the concrete pointwise
comparison without postulating that external theorem.
-/
open Function MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace QuadraticCarleson
set_option autoImplicit false
noncomputable def sharpQuadraticTailKernel (lam ε t : ℝ) : ℂ :=
  if ε < |t| then phase (lam * t ^ 2) / (t : ℂ) else 0

/-- The boundary error made when the smooth cutoff at radius `ρ` is replaced
by the sharp cutoff of the centered interval of radius `ρ`. -/
noncomputable def cutoffBoundaryKernel (lam ρ t : ℝ) : ℂ :=
  if t = 0 then 0 else
    (((dyadicCutoff (t / (4 * ρ)) - if |t| ≤ ρ then 1 else 0) / t : ℝ) : ℂ) *
      phase (lam * t ^ 2)

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceySharpSmoothAdapter ====
section
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# From sharp truncations to the smooth Krause--Lacey pieces

The Krause--Lacey stopping argument is naturally formulated for smooth dyadic
pieces, whereas the paper ultimately needs a maximum of sharp truncations.
This file proves the deterministic part of that passage.

Every positive radius is rounded upward to a dyadic radius lying between
`ε` and `2ε`.  The resulting annular error is bounded by eight copies of the
centered Hardy--Littlewood maximal function.  At the rounded radius, the
sharp tail is then decomposed exactly into a smooth high-pass cutoff and the
already-controlled cutoff boundary error.  Thus the complete loss in the
two deterministic replacements is sixteen copies of the maximal function.

What is *not* asserted here is the analytic Krause--Lacey sparse estimate for
the smooth high-pass maximum.  That is precisely the remaining oscillatory
input, rather than an assumption hidden in this adapter.
-/
open Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace QuadraticCarleson
namespace KrauseLaceySharpSmoothAdapter


set_option autoImplicit false
noncomputable section
def radiusRoundingBoundaryKernel (lam ε ρ t : ℝ) : ℂ :=
  sharpQuadraticTailKernel lam ε t - sharpQuadraticTailKernel lam ρ t

def smoothQuadraticHighPassKernel (lam ρ t : ℝ) : ℂ :=
  if t = 0 then 0 else
    ((((1 - dyadicCutoff (t / (4 * ρ))) / t : ℝ) : ℂ) *
      phase (lam * t ^ 2))

/-- Smooth high-pass convolution operator. -/
def smoothQuadraticHighPass
    (lam ρ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, smoothQuadraticHighPassKernel lam ρ (x - y) * f y

end
end KrauseLaceySharpSmoothAdapter
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Examples.Example_6c44718f87defbeb7777_KrauseLaceyScaleOffsetPointwise ====
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Arbitrary smooth radii versus adjacent dyadic radii

Rounding an arbitrary positive smooth radius upward to the next dyadic radius
costs at most `24` times the centered Hardy--Littlewood maximal function.  This
is a bound for the actual difference of the two smooth operators, obtained
from the two cutoff-boundary terms and the sharp annular rounding term.

The same single error bounds every finite maximum, with no cardinality loss.
The lower index of the comparison dyadic maximum is taken from the actual
radii, so a common real scale offset is not incorrectly treated as preserving
the original integer-dyadic lower index.  Pairing comparisons use `normInput`
on their right sides, avoiding cancellation of complex test functions.
-/
open Function MeasureTheory Set
open scoped ENNReal NNReal Topology ComplexConjugate
namespace QuadraticCarleson.KrauseLaceyScaleOffsetPointwise
open  KrauseLaceySharpSmoothAdapter



set_option autoImplicit false
noncomputable section
set_option linter.unusedVariables false in
/-- The actual difference between adjacent smooth cutoffs is one annular
error, uniformly dominated by the same maximal function. -/
theorem enorm_smoothHighPass_sub_le_maximal
    (lam : ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) (hρε : ρ ≤ 2 * ε)
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) 
    (h_QuadraticCarleson_KrauseLaceySharpSmoothAdapter_quadraticHilbertTrunc_eq_smoothHighPass_add_boundary : ∀ (lam : ℝ) {ρ : ℝ},
      0 < ρ →
        ∀ {f : ℝ → ℂ},
          MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume →
            ∀ (x : ℝ),
              QuadraticCarleson.quadraticHilbertTrunc lam ρ f x =
                QuadraticCarleson.KrauseLaceySharpSmoothAdapter.smoothQuadraticHighPass lam ρ f x +
                  ∫ (y : ℝ), QuadraticCarleson.cutoffBoundaryKernel lam ρ (x - y) * f y)
    (h_QuadraticCarleson_KrauseLaceySharpSmoothAdapter_radiusRoundingBoundaryOperator_enorm_le_maximal : ∀ (lam : ℝ) {ε ρ : ℝ},
      0 < ε →
        ε ≤ ρ →
          ρ ≤ 2 * ε →
            ∀ (f : ℝ → ℂ),
              Measurable f →
                ∀ (x : ℝ),
                  ‖∫ (y : ℝ),
                        QuadraticCarleson.KrauseLaceySharpSmoothAdapter.radiusRoundingBoundaryKernel lam
                            ε ρ (x - y) *
                          f y‖ₑ ≤
                    8 * QuadraticCarleson.centeredHardyLittlewoodMaximal (fun (y : ℝ) ↦ ‖f y‖ₑ) x)
    (h_QuadraticCarleson_cutoffBoundaryOperator_enorm_le_maximal : ∀ (lam : ℝ) {ρ : ℝ},
      0 < ρ →
        ∀ (f : ℝ → ℂ),
          Measurable f →
            ∀ (x : ℝ),
              ‖∫ (y : ℝ), QuadraticCarleson.cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ ≤
                8 * QuadraticCarleson.centeredHardyLittlewoodMaximal (fun (y : ℝ) ↦ ‖f y‖ₑ) x)
    (h_QuadraticCarleson_KrauseLaceySharpSmoothAdapter_quadraticHilbertTrunc_sub_rounded_eq_boundary : ∀ (lam : ℝ) {ε ρ : ℝ},
      0 < ε →
        0 < ρ →
          ∀ {f : ℝ → ℂ},
            MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume →
              ∀ (x : ℝ),
                QuadraticCarleson.quadraticHilbertTrunc lam ε f x -
                    QuadraticCarleson.quadraticHilbertTrunc lam ρ f x =
                  ∫ (y : ℝ),
                    QuadraticCarleson.KrauseLaceySharpSmoothAdapter.radiusRoundingBoundaryKernel lam ε ρ
                        (x - y) *
                      f y)
    :
    ‖smoothQuadraticHighPass lam ε f x - smoothQuadraticHighPass lam ρ f x‖ₑ ≤
      24 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  have hρ : 0 < ρ := hε.trans_le hερ
  have hεeq := h_QuadraticCarleson_KrauseLaceySharpSmoothAdapter_quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam hε hfi x
  have hρeq := h_QuadraticCarleson_KrauseLaceySharpSmoothAdapter_quadraticHilbertTrunc_eq_smoothHighPass_add_boundary lam hρ hfi x
  have hround := h_QuadraticCarleson_KrauseLaceySharpSmoothAdapter_quadraticHilbertTrunc_sub_rounded_eq_boundary lam hε hρ hfi x
  have heq : smoothQuadraticHighPass lam ε f x - smoothQuadraticHighPass lam ρ f x =
      ((∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y) -
        ∫ y, cutoffBoundaryKernel lam ε (x - y) * f y) +
          ∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y := by
    rw [← hround, hεeq, hρeq]
    ring
  rw [heq]
  calc
    _ ≤ (‖∫ y, radiusRoundingBoundaryKernel lam ε ρ (x - y) * f y‖ₑ +
        ‖∫ y, cutoffBoundaryKernel lam ε (x - y) * f y‖ₑ) +
          ‖∫ y, cutoffBoundaryKernel lam ρ (x - y) * f y‖ₑ :=
      (enorm_add_le _ _).trans (add_le_add enorm_sub_le le_rfl)
    _ ≤ (8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x +
        8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x) +
          8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x :=
      add_le_add (add_le_add
        (h_QuadraticCarleson_KrauseLaceySharpSmoothAdapter_radiusRoundingBoundaryOperator_enorm_le_maximal lam hε hερ hρε f hf x)
        (h_QuadraticCarleson_cutoffBoundaryOperator_enorm_le_maximal lam hε f hf x))
        (h_QuadraticCarleson_cutoffBoundaryOperator_enorm_le_maximal lam hρ f hf x)
    _ = _ := by ring
end
end QuadraticCarleson.KrauseLaceyScaleOffsetPointwise
