module

public import Mathlib
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Image
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.Regular
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.PSeries
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.Statement ====
public section
set_option autoImplicit false
/-!
# The geometric objects of Theorem 1.1

`Plane` carries the Euclidean norm. `gaugeMeasure` is Mathlib's arbitrary-gauge
Hausdorff measure, and `distanceSet` is the ordinary unpinned distance set.
-/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace FalconerThetaGauge
noncomputable section
/-- The real Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

end
end FalconerThetaGauge

end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RadialProjectionDefinitions ====
public section
set_option autoImplicit false
/-!
# Actual radial directions, arc length, and projection kernels

The target circle is the Euclidean unit sphere. The radial projection from `x`
points toward `y`, as in Theorem 5.4. On the diagonal it is assigned the unit
direction of angle zero. Arc length is the pushforward of Lebesgue measure on
the single-turn interval `(-π, π]`, so its total mass is `2π`.

The complex coordinate and kernel construction are adapted from
`FalconerPacking.PolarFourierEnergy` and `FalconerPacking.RadialProjectionKernel`
(original source credits Yongxi Lin, Apache 2.0), at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/tree/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking
-/
@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace FalconerThetaGauge
/-- The actual Euclidean unit circle. -/
abbrev UnitCircle := Metric.sphere (0 : Plane) 1
/-- The unit vector of angle `θ` in the standard Euclidean orientation. -/
def angularDirection (θ : ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr (Real.cos θ + Real.sin θ * Complex.I)
@[simp]
axiom norm_angularDirection (θ : ℝ) : ‖angularDirection θ‖ = 1

/-- The unit-circle point of angle `θ`. -/
def unitCircleOfAngle (θ : ℝ) : UnitCircle :=
  ⟨angularDirection θ, by simp⟩

/-- Lebesgue angular measure over one full turn, without probability normalization. -/
def radialAngularMeasure : Measure ℝ := volume.restrict (Ioc (-Real.pi) Real.pi)

/-- Actual circle arc length, with total mass `2π`. -/
def circleArcLength : Measure UnitCircle := radialAngularMeasure.map unitCircleOfAngle

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeFrostmanDyadic ====
public section
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
set_option autoImplicit false
/-!
# Dyadic cubes in the plane

Adapted from `FalconerPacking.Dyadic` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Dyadic.lean
This is the geometric cube hierarchy used in the finite gauge Frostman construction.  A dyadic square of generation `n` is a product of
half-open coordinate intervals of side `2⁻ⁿ`, indexed by integers.

* `mem_dyadicCube_iff` — membership is exactly the statement that the index is the floor index,
  so the generation-`n` cubes partition the plane;
* `dyadicCube_disjoint` — distinct cubes of one generation are disjoint;
* `dyadicCube_succ_subset` — each cube is contained in its parent, whose index is `k / 2`;
* `dist_le_of_mem_dyadicCube` — a generation-`n` cube has diameter at most `√2 / 2ⁿ`;
* `measurableSet_dyadicCube` — cubes are Borel.

This is the geometric hierarchy, not `Data.Dyadic`, which is an arithmetic number type.
-/
@[expose] public section
noncomputable section
open Set
namespace FalconerThetaGauge.GaugeFrostman
/-- The dyadic square of generation `n` with integer index `k`, half-open in each coordinate. -/
def dyadicCube (n : ℕ) (k : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, (k i : ℝ) ≤ 2 ^ n * x i ∧ 2 ^ n * x i < (k i : ℝ) + 1}

axiom measurableSet_dyadicCube (n : ℕ) (k : Fin 2 → ℤ) :
    MeasurableSet (dyadicCube n k)
section Counting
end Counting
section Ancestors
/-- The index of the generation-`n` ancestor, `m` levels up. -/
def ancestor (m : ℕ) (k : Fin 2 → ℤ) : Fin 2 → ℤ := fun i ↦ k i / 2 ^ m

end Ancestors
end FalconerThetaGauge.GaugeFrostman

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeFrostman ====
public section
set_option autoImplicit false
/-!
# Gauge content and the finite ingredients of Frostman's lemma

These are ingredients of Lemma 5.1 of the manuscript. In particular, positive
gauge Hausdorff measure gives positive unrestricted Hausdorff content. The
probability measure and its ball bound are not yet constructed in this file.

The content-to-measure argument is adapted from `FalconerPacking.Content`
(original source credits Yongxi Lin, Apache 2.0), replacing powers by the manuscript's actual gauge.
Source: `CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Content.lean
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
namespace GaugeFrostman
/-- Side length of a dyadic square of generation `j`. -/
def dyadicRadius (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℝ))
end GaugeFrostman
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeSeparatedMeasuresGeometry ====
public section
set_option autoImplicit false
/-!
# The fixed geometric normalization in Proposition 5.6

An explicit positive similarity places the centers one quarter apart around the
center of the unit square. The selected compact pieces lie in discs of radius
one four-hundredth, and their pair distances lie between `0.24` and `0.26`.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace FalconerThetaGauge
namespace GaugeSeparatedMeasures
/-- The half-open unit square, with its coordinate description. -/
def unitSquare : Set Plane := {x | ∀ i : Fin 2, x i ∈ Ico (0 : ℝ) 1}
end GaugeSeparatedMeasures
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularDecompositionCells ====
public section
set_option autoImplicit false
/-!
# Actual terminal cells and their original measure weights

The half-open unit square has precisely `4^N` generation-`N` cells. Their
original measure weights partition its mass; this connects finite bottom-up
types to the planar measure in Lemma 5.8.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped Classical ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
/-- The finite coordinate indices of the terminal cells in the unit square. -/
def unitCellIndices (N : ℕ) : Finset (Fin 2 → ℤ) :=
  Finset.univ.image (fun k : Fin 2 → Fin (2 ^ N) ↦ fun i ↦ (k i : ℤ))

/-- The terminal weights are the original measure masses, with no reweighting. -/
def unitCellWeight (μ : Measure Plane) (N : ℕ) (k : Fin 2 → ℤ) : ℝ :=
  μ.real (dyadicCube N k)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularMeasureExcessCount ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-!
# Actual excess properties and occupied-cell counts of retained parts

The normalized retained carriers satisfy Lemma 5.10, and their occupied
descendants satisfy the counting estimate (5.2).
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures

def occupiedCellDescendants (ρ : Measure Plane) (g p : ℕ) (q : Fin 2 → ℤ) :
    Finset (Fin 2 → ℤ) :=
  (unitCellIndices p).filter
    (fun k ↦ ancestor (p - g) k = q ∧ 0 < unitCellWeight ρ p k)
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DirectionalTestsTube ====
public section
set_option autoImplicit false
/-! # The actual finite occupied-cell tube count in Definition 6.2 -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman
/-- The true center of the manuscript's half-open generation-`p` dyadic cell. -/
def dyadicCellCenter (p : ℕ) (k : Fin 2 → ℤ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i ↦ ((k i : ℝ) + 1 / 2) / (2 : ℝ) ^ p)
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBumpBox ====
public section
set_option autoImplicit false
/-!
# Genuine box smoothing and its explicit derivative cost

The normalized average over a width-`2a` interval is the convolution with the
uniform box probability. The fundamental theorem of calculus identifies its
derivative with the signed endpoint difference. Each such difference costs at
most `a⁻¹` in the actual first norm, uniformly in the smooth input function.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace FalconerThetaGauge
/-- The literal normalized uniform-box convolution, expressed as an interval integral. -/
def boxAverage (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 * a)⁻¹ * ∫ t in (x - a)..(x + a), f t

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBumpWidths ====
public section
set_option autoImplicit false
/-!
# The explicit box widths and their exact factorial product

The finite-order smoothing construction uses the manuscript's widths
`6/(π² j²)`. Every finite partial sum leaves a positive radius for the smooth
tail, while the first `k` signed differences cost exactly `(π²/6)^k (k!)²`.
-/
@[expose] public section
noncomputable section
open Finset
namespace FalconerThetaGauge
def explicitBoxWidth (j : ℕ) : ℝ := 6 / (Real.pi ^ 2 * (j + 1 : ℝ) ^ 2)

/-- Every finite box convolution leaves genuine room for an arbitrary smooth tail. -/
def explicitBumpTailRadius (K : ℕ) : ℝ := 1 - ∑ j ∈ range K, explicitBoxWidth j
axiom explicitBumpTailRadius_pos (K : ℕ) : 0 < explicitBumpTailRadius K
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBumpStack ====
public section
set_option autoImplicit false
/-!
# Finite stacks of genuine box convolutions

Each derivative may be assigned to the next box, leaving a probability density
behind it. The resulting first-norm estimate depends only on the differentiated
widths, not on the arbitrary smooth tail or the total number of boxes.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge

def explicitBoxStack (j : ℕ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | K + 1, f => boxAverage (explicitBoxWidth j) (explicitBoxStack (j + 1) K f)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBump ====
public section
set_option autoImplicit false
/-!
# Explicit smooth even probability kernels at every finite required order

For any prescribed order `K`, convolve the first `K` uniform boxes of widths
`6/(π²j²)` with an arbitrary normalized smooth even tail in the remaining
support radius. This gives all quantitative derivative estimates through `K`
with exactly the manuscript's constants, without needing an infinite Fourier
product. The source argument uses only finitely many derivatives at each scale.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge

/-- A genuine smooth tail placed in the unused finite support radius. -/
def explicitBumpTail (K : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := explicitBumpTailRadius K / 2
  rOut := explicitBumpTailRadius K
  rIn_pos := by linarith [explicitBumpTailRadius_pos K]
  rIn_lt_rOut := by linarith [explicitBumpTailRadius_pos K]
/-- The actual order-`K` compact smooth probability kernel. -/
def explicitBump (K : ℕ) : ℝ → ℝ :=
  explicitBoxStack 0 K ((explicitBumpTail K).normed volume)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBumpScale ====
public section
set_option autoImplicit false
/-! # Rescaled quantitative finite-order smooth kernels -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge
/-- The order-`K` probability kernel at the actual positive spatial scale `δ`. -/
def scaledExplicitBump (K : ℕ) (δ : ℝ) (x : ℝ) : ℝ :=
  δ⁻¹ * explicitBump K (δ⁻¹ * x)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBumpCutoff ====
public section
set_option autoImplicit false
/-! # Actual smooth masks from closed neighborhoods of arbitrary passing sets -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff Convolution
namespace FalconerThetaGauge

/-- A true real-line convolution mask, including masks of periodic sets. -/
def smoothIndicator (K : ℕ) (δ : ℝ) (S : Set ℝ) : ℝ → ℝ :=
  S.indicator (fun _ ↦ 1) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] scaledExplicitBump K δ

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingNearCells ====
public section
set_option autoImplicit false
/-! # Exact near-row lattice count in source Estimate 7.8 -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
def spaceSplittingNear (p : ℕ) (R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : Prop :=
  dist (dyadicCellCenter p R.1) (dyadicCellCenter p S.1) ≤ 4 * dyadicRadius p ∧
    dist (dyadicCellCenter p R.2) (dyadicCellCenter p S.2) ≤ 4 * dyadicRadius p
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.MaskedFourierEnergy ====
public section
set_option autoImplicit false
/-!
# The actual masked Fourier amplitude and circular spectrum

These are the literal angular-frequency quantities `U_X` and `σ_X` in
Definition 7.1, for an actual carrier and a jointly Borel bounded symbol.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
/-- The literal masked Fourier amplitude of the actual carrier restriction. -/
def maskedFourierAmplitude (ρ : Measure Plane) (X : Set Plane)
    (b : Plane → UnitCircle → ℝ) (r : ℝ) (w : UnitCircle) : ℂ :=
  ∫ x in X, Complex.exp (-((r * inner ℝ x (w : Plane) : ℝ) : ℂ) * Complex.I) * (b x w : ℂ) ∂ρ

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.MaskedFourierEnergyCutoff ====
public section
set_option autoImplicit false
/-! # The genuine smooth dyadic-frequency cutoff of the source -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped ContDiff Convolution
namespace FalconerThetaGauge
/-- The actual source cutoff `1_[3/8,3] * ω_(1/8)`. -/
def maskedFrequencyCutoff (K : ℕ) : ℝ → ℝ :=
  smoothIndicator K (1 / 8) (Icc (3 / 8) 3)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingDistanceCover ====
public section
set_option autoImplicit false
/-! # Genuine almost-everywhere finite coverage of the far comparable spatial terms -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
def spaceSplittingRootFourMeasure (ρ : Measure Plane) (a : ℕ) (X Y : Fin 2 → ℤ) :
    Measure ((Plane × Plane) × (Plane × Plane)) :=
  ((ρ.restrict (dyadicCube a X)).prod (ρ.restrict (dyadicCube a X))).prod
    ((ρ.restrict (dyadicCube a Y)).prod (ρ.restrict (dyadicCube a Y)))
set_option linter.unusedVariables false in
axiom _root_.FalconerThetaGauge.instIsFiniteMeasureProdPlaneSpaceSplittingRootFourMeasure : ∀ (ρ : MeasureTheory.Measure FalconerThetaGauge.Plane) [MeasureTheory.IsFiniteMeasure ρ] (a : ℕ)
  (X Y : Fin 2 → ℤ),
  MeasureTheory.IsFiniteMeasure (FalconerThetaGauge.spaceSplittingRootFourMeasure ρ a X Y)
attribute [instance] _root_.FalconerThetaGauge.instIsFiniteMeasureProdPlaneSpaceSplittingRootFourMeasure
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.FourierSeparationKernel ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # Genuine spatial Fourier factorization and angular Fubini -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped RealInnerProductSpace
namespace FalconerThetaGauge
def maskedFourierPairKernel (b₁ b₂ : Plane → UnitCircle → ℝ) (r : ℝ)
    (w : UnitCircle) (p : Plane × Plane) : ℂ :=
  Complex.exp (-((r * inner ℝ (p.1 - p.2) (w : Plane) : ℝ) : ℂ) * Complex.I) *
    (b₁ p.1 w : ℂ) * (b₂ p.2 w : ℂ)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingCircle ====
public section
set_option autoImplicit false
/-! # Actual circular pair kernels and their genuine stationary-phase expansion -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff ComplexConjugate RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman
/-- The actual angular integral `I_x(r)` in the far terms of source Estimate 7.8. -/
def spaceSplittingCircleIntegral (b : Plane → UnitCircle → ℝ) (r : ℝ)
    (x x' : Plane) : ℂ :=
  ∫ w, maskedFourierPairKernel b b r w (x, x') ∂circleArcLength

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.MaskedFourierRadialMeasure ====
public section
set_option autoImplicit false
/-! # The genuine finite radial measure for the dyadic Fourier energy -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
namespace FalconerThetaGauge
/-- The nonnegative radial density appearing in the literal joint square energy. -/
def maskedFourierRadialWeight (K v : ℕ) (r : ℝ) : ℝ :=
  ((2 : ℝ) ^ v)⁻¹ * maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * r ^ 2

/-- This measure is finite because its literal compactly supported density is integrable. -/
def maskedFourierRadialMeasure (K v : ℕ) : Measure ℝ :=
  volume.withDensity (fun r ↦ ENNReal.ofReal (maskedFourierRadialWeight K v r))

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.MaskedFourierArcPair ====
public section
set_option autoImplicit false
/-! # Actual square-root arc amplitudes in the finite joint Fourier measure -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
namespace FalconerThetaGauge
/-- The actual radial and two-circle product measure, with no hypothetical energy input. -/
def maskedFourierJointMeasure (K v : ℕ) : Measure (ℝ × UnitCircle × UnitCircle) :=
  (maskedFourierRadialMeasure K v).prod (circleArcLength.prod circleArcLength)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingNearSchur ====
public section
set_option autoImplicit false
/-! # Literal occupied-cell expansion and the `81²` near-row Schur bound -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
def spaceSplittingJointAmplitude (ρ₁ ρ₂ : Measure Plane) (X Y : Set Plane)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (z : ℝ × UnitCircle × UnitCircle) : ℂ :=
  maskedFourierAmplitude ρ₁ X b₁ z.1 z.2.1 * maskedFourierAmplitude ρ₂ Y b₂ z.1 z.2.2

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrthogonalityKernelCrossBound ====
public section
set_option autoImplicit false
/-! # Actual unlinked Fourier cross integrals retain all four true cell masses -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
namespace FalconerThetaGauge
open GaugeFrostman
axiom ae_mem_four_carriers (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁]
    [IsFiniteMeasure ρ₂] {X X' Y Y' : Set Plane} (hX : MeasurableSet X)
    (hX' : MeasurableSet X') (hY : MeasurableSet Y) (hY' : MeasurableSet Y') :
    ∀ᵐ p : (Plane × Plane) × (Plane × Plane)
      ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod ((ρ₂.restrict Y).prod (ρ₂.restrict Y')),
      p ∈ (X ×ˢ X') ×ˢ (Y ×ˢ Y')

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingSpatialKernel ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # The literal four-point averaged circular kernel for space splitting -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped RealInnerProductSpace
namespace FalconerThetaGauge
/-- The actual averaged product of the two masked circular integrals. -/
def spaceSplittingAveragedCircleKernel (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ)
    (x x' y y' : Plane) : ℂ :=
  (((2 : ℝ) ^ v : ℝ) : ℂ)⁻¹ * ∫ r in Ioi 0,
    ((maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * r ^ 2 : ℝ) : ℂ) *
      spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y'

axiom integrable_spaceSplittingAveragedCircleKernel
    (μ : Measure ((Plane × Plane) × (Plane × Plane))) [IsFiniteMeasure μ]
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (uncurry b₁))
    (hb₂ : Measurable (uncurry b₂)) (hbound₁ : ∀ x w, |b₁ x w| ≤ 1)
    (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) (K v : ℕ) :
    Integrable (fun p ↦ spaceSplittingAveragedCircleKernel b₁ b₂ K v
      p.1.1 p.1.2 p.2.1 p.2.2) μ
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingSpatialKernelBounds ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # Actual absolute-integral bounds for the four-point space-splitting kernel -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped RealInnerProductSpace
namespace FalconerThetaGauge
axiom abs_integral_spaceSplittingJointAmplitude_inner_le_integral_norm
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (X X' Y Y' : Set Plane) (K v : ℕ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    |∫ z, inner ℝ (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z)
      (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z)
      ∂maskedFourierJointMeasure K v| ≤
      ∫ p : (Plane × Plane) × (Plane × Plane),
        ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v p.1.1 p.1.2 p.2.1 p.2.2‖
        ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
          ((ρ₂.restrict Y).prod (ρ₂.restrict Y'))
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingFarSumMeasures ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # The genuine fine four-point measures sum exactly to the root four-point measure -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
def spaceSplittingFineFourMeasure (ρ : Measure Plane) (p : ℕ)
    (P Q : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    Measure ((Plane × Plane) × (Plane × Plane)) :=
  ((ρ.restrict (dyadicCube p P.1)).prod (ρ.restrict (dyadicCube p Q.1))).prod
    ((ρ.restrict (dyadicCube p P.2)).prod (ρ.restrict (dyadicCube p Q.2)))
set_option linter.unusedVariables false in
axiom _root_.FalconerThetaGauge.instIsFiniteMeasureProdPlaneSpaceSplittingFineFourMeasure : ∀ (ρ : MeasureTheory.Measure FalconerThetaGauge.Plane) [MeasureTheory.IsFiniteMeasure ρ] (p : ℕ)
  (P Q : (Fin 2 → ℤ) × (Fin 2 → ℤ)),
  MeasureTheory.IsFiniteMeasure (FalconerThetaGauge.spaceSplittingFineFourMeasure ρ p P Q)
attribute [instance] _root_.FalconerThetaGauge.instIsFiniteMeasureProdPlaneSpaceSplittingFineFourMeasure
def spaceSplittingFinePairs (ρ : Measure Plane) (a p : ℕ) (X Y : Fin 2 → ℤ) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (occupiedCellDescendants ρ a p X).product (occupiedCellDescendants ρ a p Y)
axiom sum_spaceSplittingFineFourMeasure (ρ : Measure Plane) [IsProbabilityMeasure ρ]
    (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p) (X Y : Fin 2 → ℤ) :
    (∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y, spaceSplittingFineFourMeasure ρ p P Q) =
      spaceSplittingRootFourMeasure ρ a X Y
axiom integrable_spaceSplittingFineFourMeasure (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {f : (Plane × Plane) × (Plane × Plane) → ℝ}
    (hf : Integrable f (spaceSplittingRootFourMeasure ρ a X Y))
    {P Q : (Fin 2 → ℤ) × (Fin 2 → ℤ)}
    (hP : P ∈ spaceSplittingFinePairs ρ a p X Y)
    (hQ : Q ∈ spaceSplittingFinePairs ρ a p X Y) :
    Integrable f (spaceSplittingFineFourMeasure ρ p P Q)
axiom sum_integral_spaceSplittingFineFourMeasure (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {f : (Plane × Plane) × (Plane × Plane) → ℝ}
    (hf : Integrable f (spaceSplittingRootFourMeasure ρ a X Y)) :
    (∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y,
        ∫ z, f z ∂spaceSplittingFineFourMeasure ρ p P Q) =
      ∫ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingFarSum ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # Genuine far cross-term summation retains the root four-point measure -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
def spaceSplittingFarCrossSum (ρ : Measure Plane) (a p : ℕ) (X Y : Fin 2 → ℤ)
    (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ) : ℝ :=
  ∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
    ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y,
      if spaceSplittingNear p P Q then 0 else
        |∫ z, inner ℝ
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ z)
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p Q.1) (dyadicCube p Q.2) b₁ b₂ z)
          ∂maskedFourierJointMeasure K v|
axiom spaceSplittingRootFourMeasure_real_univ (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (a : ℕ) (X Y : Fin 2 → ℤ) :
    (spaceSplittingRootFourMeasure ρ a X Y).real univ =
      (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Examples.Example_73838a607487d227e2b4_SpaceSplittingFarSumENNBound ====
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # True ENNReal pointwise far bounds integrate without pointwise finiteness assumptions -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
theorem spaceSplittingFarCrossSum_le_of_ofReal_majorant (ρ : Measure Plane)
    [IsProbabilityMeasure ρ] (hρ : ρ unitSquare = 1) {a p : ℕ} (hap : a ≤ p)
    (X Y : Fin 2 → ℤ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    {f : (Plane × Plane) × (Plane × Plane) → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y) ≠ ⊤)
    (hmajor : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y, ¬spaceSplittingNear p P Q →
        ∀ x ∈ dyadicCube p P.1, ∀ x' ∈ dyadicCube p Q.1,
          ∀ y ∈ dyadicCube p P.2, ∀ y' ∈ dyadicCube p Q.2,
            ENNReal.ofReal ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y'‖ ≤
              ENNReal.ofReal δ + f ((x, x'), (y, y'))) :
    spaceSplittingFarCrossSum ρ a p X Y b₁ b₂ K v ≤
      δ * (ρ.real (dyadicCube a X) * ρ.real (dyadicCube a Y)) ^ 2 +
        (∫⁻ z, f z ∂spaceSplittingRootFourMeasure ρ a X Y).toReal := by
  have hfi := integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfin
  have hi := (integrable_const δ).add hfi
  have hfin' : ∀ P ∈ spaceSplittingFinePairs ρ a p X Y,
      ∀ Q ∈ spaceSplittingFinePairs ρ a p X Y,
        (∫⁻ z, f z ∂spaceSplittingFineFourMeasure ρ p P Q) ≠ ⊤ := by
    rw [← sum_spaceSplittingFineFourMeasure ρ hρ hap X Y,
      lintegral_finsetSum_measure] at hfin
    intro P hP
    have hPfin := ENNReal.sum_ne_top.1 hfin P hP
    rw [lintegral_finsetSum_measure] at hPfin
    exact ENNReal.sum_ne_top.1 hPfin
  have hterm (P : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hP : P ∈ spaceSplittingFinePairs ρ a p X Y)
      (Q : (Fin 2 → ℤ) × (Fin 2 → ℤ))
      (hQ : Q ∈ spaceSplittingFinePairs ρ a p X Y) :
      (if spaceSplittingNear p P Q then 0 else
        |∫ z, inner ℝ
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p P.1) (dyadicCube p P.2) b₁ b₂ z)
          (spaceSplittingJointAmplitude ρ ρ (dyadicCube p Q.1) (dyadicCube p Q.2) b₁ b₂ z)
          ∂maskedFourierJointMeasure K v|) ≤
      ∫ z, δ + (f z).toReal ∂spaceSplittingFineFourMeasure ρ p P Q := by
    by_cases hn : spaceSplittingNear p P Q
    · rw [ite_eq_left hn]
      exact integral_nonneg (fun _ ↦ add_nonneg hδ ENNReal.toReal_nonneg)
    · rw [ite_eq_right hn]
      apply (abs_integral_spaceSplittingJointAmplitude_inner_le_integral_norm ρ ρ
        (dyadicCube p P.1) (dyadicCube p Q.1) (dyadicCube p P.2) (dyadicCube p Q.2)
        K v hb₁ hb₂ hbound₁ hbound₂).trans
      apply integral_mono_ae
        (integrable_spaceSplittingAveragedCircleKernel (spaceSplittingFineFourMeasure ρ p P Q)
          hb₁ hb₂ hbound₁ hbound₂ K v).norm
        (integrable_spaceSplittingFineFourMeasure ρ hρ hap X Y hi hP hQ)
      have hae := ae_mem_four_carriers ρ ρ (measurableSet_dyadicCube p P.1)
        (measurableSet_dyadicCube p Q.1) (measurableSet_dyadicCube p P.2)
        (measurableSet_dyadicCube p Q.2)
      have haeF := ae_lt_top hf (hfin' P hP Q hQ)
      filter_upwards [hae, haeF] with z hz hzf
      have hb := hmajor P hP Q hQ hn z.1.1 hz.1.1 z.1.2 hz.1.2
        z.2.1 hz.2.1 z.2.2 hz.2.2
      have hreal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hzf.ne⟩) hb
      simpa only [ENNReal.toReal_add ENNReal.ofReal_ne_top hzf.ne,
        ENNReal.toReal_ofReal hδ, ENNReal.toReal_ofReal (norm_nonneg _),
        Pi.add_apply] using hreal
  calc
    _ ≤ ∑ P ∈ spaceSplittingFinePairs ρ a p X Y,
        ∑ Q ∈ spaceSplittingFinePairs ρ a p X Y,
          ∫ z, δ + (f z).toReal ∂spaceSplittingFineFourMeasure ρ p P Q := by
      exact sum_le_sum (fun P hP ↦ sum_le_sum (fun Q hQ ↦ hterm P hP Q hQ))
    _ = ∫ z, δ + (f z).toReal ∂spaceSplittingRootFourMeasure ρ a X Y :=
      sum_integral_spaceSplittingFineFourMeasure ρ hρ hap X Y hi
    _ = _ := by
      rw [integral_add (integrable_const δ) hfi, integral_const,
        spaceSplittingRootFourMeasure_real_univ, smul_eq_mul, mul_comm,
        integral_toReal hf.aemeasurable (ae_lt_top hf hfin)]
end FalconerThetaGauge
