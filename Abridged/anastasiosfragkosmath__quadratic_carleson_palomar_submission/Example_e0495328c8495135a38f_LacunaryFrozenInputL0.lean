import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Instances.Rat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Convolution
import Mathlib.Topology.Order.IsLUB

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CalderonZygmundBadPart ====
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
# The cancellative Calderón--Zygmund bad-part estimate in one dimension

This file formalizes the one-dimensional Lipschitz-kernel specialization of
Lemma 6.12 on printed page 114 of the harmonic-analysis notes supplied by the
author.  It is the form needed for the low oscillatory part of the positive
theorem: an atom supported on an interval has mean zero, so subtracting the
kernel at the interval center converts cancellation into spatial decay.
-/
open MeasureTheory Set
namespace QuadraticCarleson
set_option autoImplicit false
/-- The one-dimensional cube of side length `R` centered at `z`, represented
half-open so disjoint interval families remain literally disjoint. -/
noncomputable def centeredInterval (z R : ℝ) : Set ℝ :=
  Ico (z - R / 2) (z + R / 2)
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveEndpointOptimization ====
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
# Scalar optimization in the positive endpoint argument

This file isolates the numerical part of the high--low decomposition in the
positive endpoint proof of arXiv:2609.04101v1.  In particular it records the
two choices of magnitude thresholds and scale cutoffs made at the end of the
proof and turns membership in a magnitude level into the corresponding Orlicz
weight.

We use exponential notation for real powers of two.  Thus
`lacunaryScale k = 2^(2^k)` and
`lacunaryAmplitude k = 2^(2^(2^k))`, exactly the paper's lacunary choice.
-/
open Filter Set
open scoped Topology
namespace QuadraticCarleson
namespace PositiveEndpointOptimization
set_option autoImplicit false
/-- Membership in the `k`th magnitude band.  This is the scalar content of
the paper's set `F_k`, applied to `t = |f x|`. -/
def InMagnitudeLevel (A : ℕ → ℝ) (k : ℕ) (t : ℝ) : Prop :=
  if k = 0 then 0 ≤ t ∧ t ≤ A 0
  else A (k - 1) < t ∧ t ≤ A k
end PositiveEndpointOptimization
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveLevelIntegration ====
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
# Measurable magnitude levels and endpoint-weight integration

This module supplies the measure-theoretic bridge from the scalar estimates
in `PositiveEndpointOptimization` to the sums over the paper's magnitude sets
`F_k`.  Extended nonnegative integrals are used throughout, so no integrability
or finiteness hypothesis is needed.
-/
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace QuadraticCarleson
namespace PositiveLevelIntegration
open PositiveEndpointOptimization
set_option autoImplicit false
/-- The paper's magnitude set `F_k`, for an arbitrary threshold sequence. -/
def magnitudeLevelSet {α : Type*} (A : ℕ → ℝ) (f : α → ℂ) (k : ℕ) : Set α :=
  {x | InMagnitudeLevel A k ‖f x‖}

end PositiveLevelIntegration
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CalderonZygmundLevelAtoms ====
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
# Calderón--Zygmund atoms on magnitude levels

This file isolates the algebraic and measure-theoretic facts about the atoms

`1_I (f 1_{F_k} - average_I (f 1_{F_k}))`

used in the positive-endpoint argument.  It does not assert the existence of
a Calderón--Zygmund decomposition: the interval (or a disjoint family of
intervals) is supplied explicitly.
-/
open MeasureTheory Set
open scoped ENNReal BigOperators Function
namespace QuadraticCarleson
namespace CalderonZygmundLevelAtoms
open PositiveEndpointOptimization PositiveLevelIntegration
set_option autoImplicit false
noncomputable section
/-- The part of `f` lying in the magnitude band `F_k`. -/
def levelRestricted (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  (magnitudeLevelSet A f k).indicator f
/-- The average of the level-restricted function over the centered interval. -/
def levelAverage (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℂ :=
  ⨍ x in centeredInterval z R, levelRestricted A f k x
/-- The level atom attached to a centered interval. -/
def levelAtom (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℝ → ℂ :=
  (centeredInterval z R).indicator
    (fun x ↦ levelRestricted A f k x - levelAverage A f k z R)

axiom norm_levelAtom_le_two_mul {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) (x : ℝ) :
    ‖levelAtom A f k z R x‖ ≤ 2 * A k

end
end CalderonZygmundLevelAtoms
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CalderonZygmundDyadicStopping ====
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
# Dyadic stopping intervals for the Calderón--Zygmund decomposition

This module supplies an explicit global dyadic grid and proves the quantitative
parent/child facts behind the height-one stopping rule.  In particular, a
child of a good parent has `‖f‖`-average at most two.
-/
open Filter MeasureTheory Set
open scoped ENNReal BigOperators Function Topology
namespace QuadraticCarleson
namespace CalderonZygmundDyadicStopping
set_option autoImplicit false
noncomputable section
/-- Length of a depth-`n` cell in the dyadic grid with root length `L`. -/
def dyadicLength (L : ℝ) (n : ℕ) : ℝ := L / (2 : ℝ) ^ n
/-- The half-open dyadic cell with depth `n` and integer address `q`. -/
def dyadicInterval (L : ℝ) (n : ℕ) (q : ℤ) : Set ℝ :=
  Ico ((q : ℝ) * dyadicLength L n) (((q : ℝ) + 1) * dyadicLength L n)

/-- The data-dependent root length.  It is strictly larger than the global
`L¹` mass, so every depth-zero cell has average at most one. -/
def rootLength (f : ℝ → ℂ) : ℝ :=
  (∫ x, ‖f x‖) + 1

/-- The scalar `‖f‖` average on a dyadic cell. -/
def dyadicNormAverage (f : ℝ → ℂ) (L : ℝ) (n : ℕ) (q : ℤ) : ℝ :=
  ⨍ x in dyadicInterval L n q, ‖f x‖

structure DyadicCell where
  depth : ℕ
  index : ℤ
  deriving DecidableEq, Encodable
def DyadicCell.interval (L : ℝ) (c : DyadicCell) : Set ℝ :=
  dyadicInterval L c.depth c.index
def DyadicCell.normAverage (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : ℝ :=
  dyadicNormAverage f L c.depth c.index
/-- Every strictly coarser dyadic cell containing `c` is good. -/
def cellAncestorsGood (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : Prop :=
  ∀ (m : ℕ) (r : ℤ), m < c.depth →
    c.interval L ⊆ dyadicInterval L m r → dyadicNormAverage f L m r ≤ 1
def IsStoppingCell (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : Prop :=
  cellAncestorsGood f L c ∧ 1 < c.normAverage f L
/-- The canonical countable family of first-crossing cells. -/
def stoppingCell (f : ℝ → ℂ) :=
  {c : DyadicCell // IsStoppingCell f (rootLength f) c}

def stoppingBadUnion (f : ℝ → ℂ) : Set ℝ :=
  ⋃ c : stoppingCell f, c.1.interval (rootLength f)
end
end CalderonZygmundDyadicStopping
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CalderonZygmundStoppingIntervals ====
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
# Converting canonical dyadic stopping cells to centered intervals

The analytic atom estimates use a center and a length, while the canonical
stopping construction uses half-open dyadic cells.  The project's centered
interval convention is also half-open, so this file supplies an exact set
identity and transfers literal pairwise disjointness without a boundary loss.
-/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace QuadraticCarleson
namespace CalderonZygmundStoppingIntervals
open CalderonZygmundDyadicStopping
set_option autoImplicit false
noncomputable section
/-- Center of the canonical half-open stopping interval. -/
def stoppingCenter {f : ℝ → ℂ} (c : stoppingCell f) : ℝ :=
  ((c.1.index : ℝ) + 1 / 2) * dyadicLength (rootLength f) c.1.depth
/-- Length of the canonical half-open stopping interval. -/
def stoppingLength {f : ℝ → ℂ} (c : stoppingCell f) : ℝ :=
  dyadicLength (rootLength f) c.1.depth
axiom stoppingLength_pos {f : ℝ → ℂ} (c : stoppingCell f) :
    0 < stoppingLength c

end
end CalderonZygmundStoppingIntervals
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveHighHeightEstimate ====
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
# Genuine high-height estimate: disjoint level-atom inputs

The paper's high part uses the strict height range `r > B_k` and the input
`b_k = ∑ I, b_{I,k}`. This file constructs that countable disjoint atom sum,
proves its L² input bound from the actual atom estimates, and invokes the
proved real-parameter fixed-height quadratic maximal theorem.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace PositiveHighHeightEstimate
open CalderonZygmundLevelAtoms PositiveLevelIntegration
noncomputable def disjointLevelAtomSum {ι : Type*}
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ι → ℝ) (x : ℝ) : ℂ :=
  ∑' i, levelAtom A f k (z i) (R i) x

end PositiveHighHeightEstimate
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CanonicalScaleAtoms ====
section
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Canonical stopping atoms sliced by their exact dyadic lengths

The scale class is exactly `2^j ≤ length < 2^(j+1)`. The construction is
generic in the magnitude amplitudes and therefore covers both the full and
lacunary partitions. No interval family is supplied as an assumption.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace CanonicalScaleAtoms
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms 
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate

noncomputable def canonicalLevelBadPart (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  disjointLevelAtomSum A f k (stoppingCenter (f := f)) stoppingLength
axiom canonicalLevelBadPart_eq_atom_of_mem (A : ℕ → ℝ) {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) (k : ℕ) :
    canonicalLevelBadPart A f k x =
      levelAtom A f k (stoppingCenter c) (stoppingLength c) x
axiom canonicalLevelBadPart_eq_zero_of_notMem (A : ℕ → ℝ) {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) (k : ℕ) : canonicalLevelBadPart A f k x = 0
end CanonicalScaleAtoms
end QuadraticCarleson

end

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Examples.Example_e0495328c8495135a38f_LacunaryFrozenInputL0 ====
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The genuine frozen block input belongs to the paper's test domain

Every stopping cell meets the support of the original input and has length
at most the data-dependent root length. Thus all stopping cells lie in one
bounded enlargement of a compact set supporting the original input. Exact
disjointness also gives a pointwise `2 A_k` bound for any frozen scale block,
with no factor depending on its number of scales.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryFrozenInputL0
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CanonicalScaleAtoms
open PositiveEndpointOptimization  
set_option autoImplicit false
theorem norm_canonicalLevelBadPart_le_two_mul
    {A : ℕ → ℝ} (f : ℝ → ℂ) {k : ℕ} (hAk : 0 ≤ A k) (x : ℝ) :
    ‖canonicalLevelBadPart A f k x‖ ≤ 2 * A k := by
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    rw [canonicalLevelBadPart_eq_atom_of_mem A c hc]
    exact norm_levelAtom_le_two_mul hAk (stoppingLength_pos c) x
  · rw [canonicalLevelBadPart_eq_zero_of_notMem A hx, norm_zero]
    positivity
end LacunaryFrozenInputL0
end QuadraticCarleson
