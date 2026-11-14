import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.Definitions ====
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

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.FiniteSparseMaximal ====
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
# Finite maxima of sparse operators

This file develops the sparse-family and finite-maximal ingredients of Lemma
`l:weak11sparse` in the paper.  In particular, it records measurability in the
definition of a sparse family, proves that a sparse family of nondegenerate
real intervals is countable, makes the infimum defining the sparse norm
usable, and verifies the two quantitative finite-dimensional steps in the
paper's proof: the Hölder estimate for the foliation by the linearizing index
and the logarithmic choice of exponents.
-/
open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
namespace L0Infinity

end L0Infinity
structure RealInterval where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
/-- The interval itself.  Endpoint choices do not affect any later measure. -/
def RealInterval.carrier (I : RealInterval) : Set ℝ := Ioc I.left I.right
/-- Lebesgue length of an interval. -/
def RealInterval.length (I : RealInterval) : ℝ := I.right - I.left
set_option linter.unusedVariables false in
axiom _root_.QuadraticCarleson.RealInterval.length_pos : ∀ (I : QuadraticCarleson.RealInterval), 0 < I.length

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.Bohr ====
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
# Elementary phase and Bohr-set lemmas

These are the first checked ingredients for Section 3 of the paper.
-/
open MeasureTheory Set
namespace QuadraticCarleson
set_option linter.unusedVariables false in
axiom _root_.QuadraticCarleson.norm_phase : ∀ (s : ℝ), ‖QuadraticCarleson.phase s‖ = 1
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.PositiveDyadicKernel ====
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

noncomputable def dyadicPsi (j : ℤ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else
    (dyadicCutoff (2⁻¹ ^ j * t) - dyadicCutoff (2⁻¹ ^ (j - 1) * t)) / t

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.QuadraticL2Operator ====
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
# Integral operators for the fixed-height quadratic argument

Finite linearizations of the annular quadratic operators have measurable,
bounded kernels with a finite spatial range. This file develops their actual
integral adjoints and `TT*` representation. The boundedness and finite-range
constants here may depend on the finite family; the oscillatory estimates in
`QuadraticTTStar` will be used to obtain constants independent of that family.
-/
open MeasureTheory Set
open scoped ComplexConjugate
namespace QuadraticCarleson
/-- The elementary kernel properties enjoyed by every finite linearization of
a family of bounded, compactly supported convolution kernels. -/
structure FiniteRangeKernel where
  toFun : ℝ → ℝ → ℂ
  measurable_toFun : Measurable (Function.uncurry toFun)
  radius : ℝ
  radius_pos : 0 < radius
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x t, ‖toFun x t‖ ≤ bound
  eq_zero : ∀ x t, radius < |x - t| → toFun x t = 0
instance : CoeFun FiniteRangeKernel (fun _ ↦ ℝ → ℝ → ℂ) := ⟨FiniteRangeKernel.toFun⟩
namespace FiniteRangeKernel

noncomputable def adjoint (K : FiniteRangeKernel) : FiniteRangeKernel where
  toFun x t := conj (K t x)
  measurable_toFun := Complex.continuous_conj.measurable.comp
    (K.measurable_toFun.comp measurable_swap)
  radius := K.radius
  radius_pos := K.radius_pos
  bound := K.bound
  bound_nonneg := K.bound_nonneg
  norm_le x t := by simpa only [RCLike.norm_conj] using K.norm_le t x
  eq_zero x t h := by
    rw [K.eq_zero t x (by simpa only [abs_sub_comm] using h), map_zero]
noncomputable def applyIntegral (K : FiniteRangeKernel) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, K x t * f t

end FiniteRangeKernel
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.QuadraticFixedHeightAveragingCorrelation ====
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
# Annular amplitude products in the fixed-height quadratic correlation

These lemmas instantiate the proved quadratic oscillatory estimate for the
actual product of two annular convolution amplitudes. Their uniform amplitude
and derivative bounds are kept explicit, to be supplied by the dyadic cutoff
lemmas rather than assumed in a headline theorem.
-/
open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate
namespace QuadraticCarleson
/-- Modulation of an annular amplitude by the paper's quadratic phase. -/
noncomputable def annularQuadraticKernel (a : ℝ → ℂ) (lam t : ℝ) : ℂ :=
  a t * phase (lam * t ^ 2)
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.QuadraticFixedHeightAveragingAmplitude ====
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
# Concrete one-sided dyadic amplitudes for fixed-height quadratic decay

The positive half of the paper's annular dyadic kernel is a dilation of one
fixed smooth compactly supported function. Uniform amplitude and derivative
constants are derived from that fixed function, not supplied as assumptions.
-/
open MeasureTheory Set
open scoped ENNReal NNReal ContDiff
namespace QuadraticCarleson

/-- The fixed positive half of the scale-zero dyadic amplitude. -/
noncomputable def positiveDyadicBase (t : ℝ) : ℂ :=
  if 0 < t then (dyadicPsi 0 t : ℂ) else 0

set_option linter.unusedVariables false in
axiom _root_.QuadraticCarleson.exists_positiveDyadicBase_bound : ∃ (D : ℝ),
  0 ≤ D ∧
    (∀ (t : ℝ), ‖QuadraticCarleson.positiveDyadicBase t‖ ≤ D) ∧
      ∀ (t : ℝ), ‖deriv QuadraticCarleson.positiveDyadicBase t‖ ≤ D
noncomputable def positiveDyadicAmplitudeBound : ℝ := Classical.choose exists_positiveDyadicBase_bound
set_option linter.unusedVariables false in
axiom _root_.QuadraticCarleson.positiveDyadicAmplitudeBound_nonneg : 0 ≤ QuadraticCarleson.positiveDyadicAmplitudeBound

noncomputable def positiveDyadicAmplitude (j : ℤ) (t : ℝ) : ℂ :=
  (((2⁻¹ : ℝ) ^ j : ℝ) : ℂ) * positiveDyadicBase ((2⁻¹ : ℝ) ^ j * t)
noncomputable def positiveDyadicAmplitudeDerivative (j : ℤ) (t : ℝ) : ℂ :=
  (((2⁻¹ : ℝ) ^ j : ℝ) : ℂ) ^ 2 * deriv positiveDyadicBase ((2⁻¹ : ℝ) ^ j * t)

set_option linter.unusedVariables false in
axiom _root_.QuadraticCarleson.hasDerivAt_positiveDyadicAmplitude : ∀ (j : ℤ) (t : ℝ),
  HasDerivAt (QuadraticCarleson.positiveDyadicAmplitude j)
    (QuadraticCarleson.positiveDyadicAmplitudeDerivative j t) t

set_option linter.unusedVariables false in
axiom _root_.QuadraticCarleson.positiveDyadicAmplitude_support_subset : ∀ (j : ℤ),
  Function.support (QuadraticCarleson.positiveDyadicAmplitude j) ⊆
    Set.Icc (2 ^ (j - 1) / 4) (2 ^ (j - 1))
set_option linter.unusedVariables false in
axiom _root_.QuadraticCarleson.norm_positiveDyadicAmplitude_le : ∀ (j : ℤ) (t : ℝ),
  ‖QuadraticCarleson.positiveDyadicAmplitude j t‖ ≤
    QuadraticCarleson.positiveDyadicAmplitudeBound / 2 ^ (j - 1)
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyDyadicLocalization ====
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
# Dyadic localization in the Krause--Lacey sparse recursion

This module formalizes the geometric localization at the start of Section 3
of Krause--Lacey, *Sparse bounds for maximal monomial oscillatory Hilbert
transforms* (arXiv:1609.01564).  In their display (3.2), an interval `I` of
length `2^(k+2)` is assigned a genuine dyadic kernel piece at scale `k`, and
the input is restricted to the central third `I'`.  The resulting piece is
supported in `I`.

The source first concentrates on the positive half-kernel `ρₖ⁺`, saying
explicitly that the complementary negative half is symmetric.  Accordingly,
our main localized piece uses the project's concrete `positiveDyadicAmplitude`;
a separate signed companion below uses the full `dyadicPsi` and connects this
localization to the genuine full dyadic Hilbert kernel.  Both have outer
support radius `2^(j-1)`, exactly one eighth of `2^(j+2)` in the project's
indexing.

The genuinely analytic input called Lemma 3.5 in that source is deliberately
not asserted here: it is the remaining local oscillatory `L¹ → L^q` estimate.
The results below prove its localization and stopping/packing framework, but
do not replace that estimate by an assumption.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
set_option autoImplicit false
/-- The interval `I'` in Krause--Lacey display (3.2): the central third of
`I`.  We retain the project's canonical half-open representative. -/
noncomputable def RealInterval.centralThird (I : RealInterval) : Set ℝ :=
  Ioc ((2 * I.left + I.right) / 3) ((I.left + 2 * I.right) / 3)

/-- The genuine localized quadratic dyadic piece corresponding to
Krause--Lacey (3.2), with the source input restriction to the central third.
The harmless phase parameter is left explicit. -/
noncomputable def krauseLaceyLocalizedPiece
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, positiveDyadicAmplitude j y * phase (lam * y ^ 2) *
    I.centralThird.indicator f (x - y)

noncomputable def intervalL1Average (f : ℝ → ℂ) (I : RealInterval) : ℝ :=
  I.length⁻¹ * ∫ x in I.carrier, ‖f x‖

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyStoppingExtraction ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual finite stopping extraction for the Krause--Lacey recursion

This is the finite version of the extraction following KL18 Lemma 3.5:
select the maximal intervals where either input average exceeds ten times
the parent average. The selected children, their packing, and the bounded
averages on the remaining collection are conclusions, not supplied stopping
or sparse hypotheses. The only structural input is laminarity of the finite
interval collection, as holds in each source dyadic grid.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyStoppingExtraction
set_option autoImplicit false

/-- The literal two-function threshold-ten test in the source recursion. -/
def IsBadDescendant (f g : ℝ → ℂ) (I J : RealInterval) : Prop :=
  J.carrier ⊆ I.carrier ∧
    (10 * intervalL1Average f I < intervalL1Average f J ∨
      10 * intervalL1Average g I < intervalL1Average g J)
noncomputable def badDescendants
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter (IsBadDescendant f g I)
/-- Inclusion-maximal bad intervals, constructed directly from the finite
candidate collection. -/
noncomputable def stoppingChildren
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact (badDescendants S f g I).filter fun J ↦
    ∀ K ∈ badDescendants S f g I, J.carrier ⊆ K.carrier → K = J

/-- The remaining collection on which the local oscillatory estimate must
be proved: discard every interval contained in a selected child. -/
noncomputable def goodCollection
    (S : Finset RealInterval) (f g : ℝ → ℂ) (I : RealInterval) : Finset RealInterval := by
  classical
  exact S.filter fun J ↦ ¬ ∃ K ∈ stoppingChildren S f g I, J.carrier ⊆ K.carrier
end KrauseLaceyStoppingExtraction
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyCrossScalePairing ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual cross pairings of the separated quadratic pieces

The mixed integral composition is justified on `L¹` inputs using the
bounded finite-range kernels. The resulting cross-pairing estimate keeps
the two actual central-third restricted input masses.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate
namespace QuadraticCarleson
set_option autoImplicit false
namespace FiniteRangeKernel
end FiniteRangeKernel
/-- The actual positive quadratic convolution as a bounded finite-range
kernel, with its proved cutoff constant and support radius. -/
noncomputable def krauseLaceyPositiveKernel (j : ℤ) : FiniteRangeKernel where
  toFun x t := annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t)
  measurable_toFun := by
    have ha : Continuous (positiveDyadicAmplitude j) :=
      continuous_iff_continuousAt.mpr
        (fun t ↦ (hasDerivAt_positiveDyadicAmplitude j t).continuousAt)
    unfold annularQuadraticKernel phase
    fun_prop
  radius := (2 : ℝ) ^ (j - 1)
  radius_pos := by positivity
  bound := positiveDyadicAmplitudeBound / (2 : ℝ) ^ (j - 1)
  bound_nonneg := div_nonneg positiveDyadicAmplitudeBound_nonneg (by positivity)
  norm_le x t := by
    simp only [annularQuadraticKernel, norm_mul, norm_phase, mul_one]
    exact norm_positiveDyadicAmplitude_le j (x - t)
  eq_zero x t ht := by
    have hz : positiveDyadicAmplitude j (x - t) = 0 := by
      by_contra hn
      have hs := positiveDyadicAmplitude_support_subset j hn
      have hnonneg : 0 ≤ x - t := (by positivity : 0 ≤ (2 : ℝ) ^ (j - 1) / 4).trans hs.1
      rw [abs_of_nonneg hnonneg] at ht
      exact (not_lt_of_ge hs.2) ht
    simp [annularQuadraticKernel, hz]

end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyBadScaleInputs ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual bad-scale inputs in the local Krause--Lacey argument

The bad intervals are the actual maximal threshold-ten children for `f`
(the second stopping input is zero). The grouping uses the source's exact
condition `max (2^k₀) |J| = 2^ℓ`, including every smaller child at the base
scale. No cancellation is subtracted from these bad inputs.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
open scoped Classical
/-- The actual source family `B(ℓ)`. -/
noncomputable def badScaleCells (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) : Finset RealInterval :=
  (stoppingChildren S f 0 I₀).filter fun J ↦ max ((2 : ℝ) ^ k₀) J.length = (2 : ℝ) ^ ℓ
/-- The uncancelled bad input `B_ℓ = ∑_{J∈B(ℓ)} f 1_J`. -/
noncomputable def badScaleInput (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) (x : ℝ) : ℂ :=
  ∑ J ∈ badScaleCells S f I₀ k₀ ℓ, J.carrier.indicator f x

end KrauseLaceyBadScale
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyNonstandardEnergy ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual nonstandard intervals and their diagonal energy

The nonstandard test is the source's adjoint-composition test, rather than
the desired `L²` estimate. Its right side is the actual unit-window
convolution of the restricted bad input. The diagonal estimate below is
derived from this test and the proved stopping-cell local-mass bound.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate Classical
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
/-- The near-diagonal positive convolution in the source nonstandard test. -/
noncomputable def localUnitMass (I : RealInterval) (b : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∫ t in Icc (x - 1 / 2) (x + 1 / 2), ‖I.centralThird.indicator b t‖
/-- Literal source nonstandard condition, with the concrete near-diagonal
constant multiplied by `100`. We use the equivalent a.e. form. -/
def IsNonstandard (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) : Prop :=
  ∀ᵐ x ∂volume, x ∈ I.centralThird →
    ‖(krauseLaceyPositiveKernel k).adjoint.applyIntegral
      (krauseLaceyLocalizedPiece 1 k I b) x‖ ≤
      (1600 * positiveDyadicAmplitudeBound ^ 2 / I.length) * localUnitMass I b x
noncomputable def nonstandardIntervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : Finset RealInterval :=
  (goodCollection S f 0 I₀).filter fun I ↦
    I.length = (2 : ℝ) ^ (scale I + 2) ∧ k₀ ≤ scale I + 2 - s ∧
      IsNonstandard (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s))

end KrauseLaceyBadScale
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyNonstandardCrossRows ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Summable cross rows for the actual nonstandard bad pieces

The small intervals in a cross row need not be disjoint: their actual
restricted bad-scale inputs have no multiplicity. This removes a potential
generation-count loss from the two-scale correlation estimate.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
noncomputable def intervalBadMass
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (I : RealInterval) : ℝ :=
  ∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖

end KrauseLaceyBadScale
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyPrunedPhysicalMaximal ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The genuine pruned physical-truncation maximal operator

Physical length tails are compared to the regenerated prefixes of the
same pruned family. The factor two comes from subtracting two prefixes.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyBadScale

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
noncomputable def badLengthTailAction
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (ell : ℤ) (x : ℝ) : ℂ :=
  ∑ I ∈ N, if (2 : ℝ) ^ ell ≤ I.length then krauseLaceyLocalizedPiece 1 (scale I) I
    (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0
noncomputable def badLengthTailMaximal
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval) (x : ℝ) : ℝ :=
  ⨆ ell : ℤ, ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖

end KrauseLaceyBadScale
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Examples.Example_65575b6f124925a37842_KrauseLaceyNonstandardPairing ====
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The actual nonstandard local pairing bound (KL18 Proposition 4.7)

The amplitude estimate gives the exact interval-average majorant for
every physical truncation. Integration and the proved no-loss bad-input
mass packing yield the source pairing bound, independently of the scale
gap. No linearization or sparse estimate is assumed.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open  KrauseLaceyStoppingExtraction
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

set_option linter.unusedVariables false in
theorem badLengthTailMaximal_le_massMajorant
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) (x : ℝ) 
    (h_QuadraticCarleson_krauseLaceyLocalizedPiece_eq_zero_of_notMem : ∀ (lam : ℝ) (j : ℤ) (I : QuadraticCarleson.RealInterval) (f : ℝ → ℂ),
      I.length = 2 ^ (j + 2) →
        ∀ {x : ℝ}, x ∉ I.carrier → QuadraticCarleson.krauseLaceyLocalizedPiece lam j I f x = 0)
    (h_QuadraticCarleson_KrauseLaceyBadScale_intervalBadMass_nonneg : ∀ (S : Finset QuadraticCarleson.RealInterval) (f : ℝ → ℂ) (I₀ : QuadraticCarleson.RealInterval)
      (k₀ s : ℤ) (scale : QuadraticCarleson.RealInterval → ℤ) (I : QuadraticCarleson.RealInterval),
      0 ≤ QuadraticCarleson.KrauseLaceyBadScale.intervalBadMass S f I₀ k₀ s scale I)
    (h_QuadraticCarleson_KrauseLaceyBadScale_norm_localizedBadPiece_le_mass : ∀ {S : Finset QuadraticCarleson.RealInterval} {f : ℝ → ℂ},
      MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume →
        ∀ (I₀ : QuadraticCarleson.RealInterval) (k₀ s : ℤ) (scale : QuadraticCarleson.RealInterval → ℤ)
          {I : QuadraticCarleson.RealInterval},
          I ∈ QuadraticCarleson.KrauseLaceyBadScale.nonstandardIntervals S f I₀ k₀ s scale →
            ∀ (x : ℝ),
              ‖QuadraticCarleson.krauseLaceyLocalizedPiece 1 (scale I) I
                    (QuadraticCarleson.KrauseLaceyBadScale.badScaleInput S f I₀ k₀ (scale I + 2 - s))
                    x‖ ≤
                8 * QuadraticCarleson.positiveDyadicAmplitudeBound / I.length *
                  QuadraticCarleson.KrauseLaceyBadScale.intervalBadMass S f I₀ k₀ s scale I)
    :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      ∑ I ∈ N, I.carrier.indicator (fun _ ↦
        (8 * positiveDyadicAmplitudeBound / I.length) * intervalBadMass S f I₀ k₀ s scale I) x := by
  apply ciSup_le
  intro ell
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  by_cases hx : x ∈ I.carrier
  · rw [Set.indicator_of_mem hx]
    split_ifs
    · exact h_QuadraticCarleson_KrauseLaceyBadScale_norm_localizedBadPiece_le_mass hf I₀ k₀ s scale (hN hI) x
    · rw [norm_zero]
      exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
        positiveDyadicAmplitudeBound_nonneg) I.length_pos.le)
        (h_QuadraticCarleson_KrauseLaceyBadScale_intervalBadMass_nonneg S f I₀ k₀ s scale I)
  · rw [Set.indicator_of_notMem hx, h_QuadraticCarleson_krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
      (Finset.mem_filter.mp (hN hI)).2.1 hx]
    simp

end KrauseLaceyBadScale
end QuadraticCarleson
