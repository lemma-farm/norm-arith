module

public import Mathlib
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
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
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.Statement ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RadialProjectionDefinitions ====
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

/-- The angle from the pin `x` toward the source point `y`; its diagonal value is zero. -/
def radialAngle (x y : Plane) : ℝ :=
  Complex.arg (Complex.orthonormalBasisOneI.repr.symm (y - x))

/-- Lebesgue angular measure over one full turn, without probability normalization. -/
def radialAngularMeasure : Measure ℝ := volume.restrict (Ioc (-Real.pi) Real.pi)

/-- Actual circle arc length, with total mass `2π`. -/
def circleArcLength : Measure UnitCircle := radialAngularMeasure.map unitCircleOfAngle

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.ExplicitBumpBox ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.ExplicitBumpWidths ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.ExplicitBumpStack ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.ExplicitBump ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.ExplicitBumpScale ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.ExplicitBumpCutoff ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.MaskedFourierEnergyCutoff ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.FourierSeparationKernel ====
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

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.StationaryMorseAngle ====
public section
set_option autoImplicit false
/-!
# The literal Morse coordinate for circular stationary phase
-/
@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace FalconerThetaGauge
def stationaryMorseAngle (s : ℝ) : ℝ := 2 * Real.arcsin (s / 2)
def stationaryMorseJacobian (s : ℝ) : ℝ := (Real.sqrt (1 - s ^ 2 / 4))⁻¹

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.StationaryPhaseOperators ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-!
# Exact constant coefficients for the circular Morse coordinate

The coefficients are finite sums of the actual derivatives of the literal Morse angle and
Jacobian. Ordered finite partitions supply the composition coefficients; Leibniz supplies
the Jacobian factor. They are independent of the amplitude and the stationary point.
-/
@[expose] public section
noncomputable section
open Finset Set
open scoped ContDiff Topology
namespace FalconerThetaGauge
/-- The coefficient of the `k`th derivative in the `m`th derivative of a composition. -/
def stationaryCompositionCoefficient (m k : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition m,
    if c.length = k then ∏ r, iteratedDeriv (c.partSize r) stationaryMorseAngle 0 else 0
/-- Universal real coefficients for the amplitude times the Morse Jacobian. -/
def stationaryDerivativeCoefficient (n k : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1),
    (n.choose i : ℝ) * iteratedDeriv i stationaryMorseJacobian 0 *
      stationaryCompositionCoefficient (n - i) k

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.StationaryPhaseOperatorsComplex ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-!
# The two constant-coefficient stationary-phase operators
-/
@[expose] public section
noncomputable section
open Finset
open scoped ContDiff
namespace FalconerThetaGauge
/-- The source's positive-sign operator coefficient. -/
def stationaryPhaseCoefficient (j k : ℕ) : ℂ :=
  (Complex.I / 2) ^ j / (j.factorial : ℂ) * (stationaryDerivativeCoefficient (2 * j) k : ℂ)
/-- The operator at the opposite stationary point has conjugate coefficients. -/
def stationaryPhaseConjugateCoefficient (j k : ℕ) : ℂ :=
  star (stationaryPhaseCoefficient j k)
def stationaryPhaseOperator (j : ℕ) (G : ℝ → ℂ) (φ : ℝ) : ℂ :=
  ∑ k ∈ range (2 * j + 1), stationaryPhaseCoefficient j k * iteratedDeriv k G φ
def stationaryPhaseConjugateOperator (j : ℕ) (G : ℝ → ℂ) (φ : ℝ) : ℂ :=
  ∑ k ∈ range (2 * j + 1), stationaryPhaseConjugateCoefficient j k * iteratedDeriv k G φ

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.MaskedMattilaSymbolRegularity ====
public section
set_option autoImplicit false
/-! # Genuine built-symbol amplitudes for the pointwise masked Mattila inversion -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge
def builtSymbolAngularAmplitude (b : Plane → UnitCircle → ℝ) (x : Plane) : ℝ → ℂ :=
  fun θ ↦ (b x (unitCircleOfAngle θ) : ℂ)
def builtSymbolPairAngularAmplitude (b₁ b₂ : Plane → UnitCircle → ℝ)
    (x y : Plane) : ℝ → ℂ := builtSymbolAngularAmplitude b₁ x * builtSymbolAngularAmplitude b₂ y
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.SpaceSplittingCircle ====
public section
set_option autoImplicit false
/-! # Actual circular pair kernels and their genuine stationary-phase expansion -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff ComplexConjugate RealInnerProductSpace
namespace FalconerThetaGauge

/-- The actual angular integral `I_x(r)` in the far terms of source Estimate 7.8. -/
def spaceSplittingCircleIntegral (b : Plane → UnitCircle → ℝ) (r : ℝ)
    (x x' : Plane) : ℂ :=
  ∫ w, maskedFourierPairKernel b b r w (x, x') ∂circleArcLength
axiom norm_spaceSplittingCircleIntegral_le {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (hbound : ∀ x w, |b x w| ≤ 1)
    (r : ℝ) (x x' : Plane) : ‖spaceSplittingCircleIntegral b r x x'‖ ≤ 2 * Real.pi
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.OrthogonalityRadialAmplitude ====
public section
set_option autoImplicit false
/-! # The literal source radial amplitude and its compact dyadic support -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace FalconerThetaGauge
/-- The actual radial weight `2⁻ᵛ Ψ(r/2ᵛ) r²` in Estimate 7.6. -/
def orthogonalityRadialAmplitude (K v : ℕ) (r : ℝ) : ℂ :=
  (((2 : ℝ) ^ v)⁻¹ : ℂ) * (maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) : ℂ) * (r : ℂ) ^ 2
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.MaskedFourierRadialMeasure ====
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
set_option linter.unusedVariables false in
axiom _root_.FalconerThetaGauge.isFiniteMeasure_maskedFourierRadialMeasure : ∀ (K v : ℕ), MeasureTheory.IsFiniteMeasure (FalconerThetaGauge.maskedFourierRadialMeasure K v)
attribute [instance] _root_.FalconerThetaGauge.isFiniteMeasure_maskedFourierRadialMeasure
axiom integral_maskedFourierRadialMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K v : ℕ) (f : ℝ → E) :
    (∫ r, f r ∂maskedFourierRadialMeasure K v) =
      ∫ r, maskedFourierRadialWeight K v r • f r
axiom orthogonalityRadialAmplitude_eq_real_weight (K v : ℕ) (r : ℝ) :
    orthogonalityRadialAmplitude K v r = (maskedFourierRadialWeight K v r : ℂ)
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.SpaceSplittingSpatialKernel ====
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
axiom spaceSplittingAveragedCircleKernel_eq_radial (b₁ b₂ : Plane → UnitCircle → ℝ)
    (K v : ℕ) (x x' y y' : Plane) :
    spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y' =
      ∫ r, spaceSplittingCircleIntegral b₁ r x x' *
        spaceSplittingCircleIntegral b₂ r y y' ∂maskedFourierRadialMeasure K v

@[fun_prop]
axiom measurable_spaceSplittingCircleIntegral_joint {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) :
    Measurable (fun q : (Plane × Plane) × ℝ ↦
      spaceSplittingCircleIntegral b q.2 q.1.1 q.1.2)
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.SpaceSplittingCircleRemainder ====
public section
set_option autoImplicit false
/-! # The actual far circular integral has a uniformly small stationary remainder -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace FalconerThetaGauge
/-- Both genuine stationary contributions to the actual built-symbol circular integral. -/
def spaceSplittingStationaryMain (T : ℕ) (b : Plane → UnitCircle → ℝ)
    (r : ℝ) (x x' : Plane) : ℂ :=
  (Real.sqrt (2 * Real.pi / (r * dist x x')) : ℂ) *
    (Complex.exp (-((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
      ∑ j ∈ Finset.range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
        stationaryPhaseOperator j (builtSymbolPairAngularAmplitude b b x x')
          (radialAngle 0 (x - x')) +
    Complex.exp (((r * dist x x' - Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
      ∑ j ∈ Finset.range T, ((r * dist x x' : ℝ) : ℂ)⁻¹ ^ j *
        stationaryPhaseConjugateOperator j (builtSymbolPairAngularAmplitude b b x x')
          (radialAngle 0 (x - x') + Real.pi))
end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Examples.Example_f16d7dda1d4bc6e4eac6_SpaceSplittingCircleProductRemainder ====
set_option autoImplicit false
/-! # The true averaged product of the circular stationary remainders is negligible -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
@[fun_prop]
axiom measurable_spaceSplittingStationaryMain (T : ℕ) (b : Plane → UnitCircle → ℝ)
    (x x' : Plane) : Measurable (fun r ↦ spaceSplittingStationaryMain T b r x x')
axiom norm_circle_product_sub_stationary_product_le {Ix Iy Mx My : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hx : ‖Ix‖ ≤ 2 * Real.pi) (hy : ‖Iy‖ ≤ 2 * Real.pi)
    (hex : ‖Ix - Mx‖ ≤ δ) (hey : ‖Iy - My‖ ≤ δ) :
    ‖Ix * Iy - Mx * My‖ ≤ (4 * Real.pi + δ) * δ
set_option maxHeartbeats 800000 in
theorem norm_averaged_circle_product_sub_stationary_product_le
    {b₁ b₂ : Plane → UnitCircle → ℝ} (hb₁ : Measurable (Function.uncurry b₁))
    (hb₂ : Measurable (Function.uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1)
    (K v T : ℕ) (x x' y y' : Plane) {δ : ℝ} (hδ : 0 ≤ δ)
    (hex : ∀ᵐ r ∂maskedFourierRadialMeasure K v,
      ‖spaceSplittingCircleIntegral b₁ r x x' -
        spaceSplittingStationaryMain T b₁ r x x'‖ ≤ δ)
    (hey : ∀ᵐ r ∂maskedFourierRadialMeasure K v,
      ‖spaceSplittingCircleIntegral b₂ r y y' -
        spaceSplittingStationaryMain T b₂ r y y'‖ ≤ δ) :
    ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y' -
      ∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        spaceSplittingStationaryMain T b₁ r x x' *
          spaceSplittingStationaryMain T b₂ r y y'‖ ≤
      (maskedFourierRadialMeasure K v).real univ * (4 * Real.pi + δ) * δ := by
  let μ := maskedFourierRadialMeasure K v
  have hm₁ := measurable_spaceSplittingStationaryMain T b₁ x x'
  have hm₂ := measurable_spaceSplittingStationaryMain T b₂ y y'
  have hc₁ : Measurable (fun r ↦ spaceSplittingCircleIntegral b₁ r x x') :=
    Measurable.of_uncurry_left
      (f := fun (q : Plane × Plane) (r : ℝ) ↦ spaceSplittingCircleIntegral b₁ r q.1 q.2)
      (x := (x, x')) (measurable_spaceSplittingCircleIntegral_joint hb₁)
  have hc₂ : Measurable (fun r ↦ spaceSplittingCircleIntegral b₂ r y y') :=
    Measurable.of_uncurry_left
      (f := fun (q : Plane × Plane) (r : ℝ) ↦ spaceSplittingCircleIntegral b₂ r q.1 q.2)
      (x := (y, y')) (measurable_spaceSplittingCircleIntegral_joint hb₂)
  have hiC : Integrable (fun r ↦ spaceSplittingCircleIntegral b₁ r x x' *
      spaceSplittingCircleIntegral b₂ r y y') μ := by
    apply (integrable_const ((2 * Real.pi) ^ 2 : ℝ)).mono (hc₁.mul hc₂).aestronglyMeasurable
    filter_upwards [] with r
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul (norm_spaceSplittingCircleIntegral_le hb₁ hbound₁ r x x')
      (norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y') (norm_nonneg _) (by positivity)
  have hiM : Integrable (fun r ↦ spaceSplittingStationaryMain T b₁ r x x' *
      spaceSplittingStationaryMain T b₂ r y y') μ := by
    apply (integrable_const ((2 * Real.pi + δ) ^ 2 : ℝ)).mono
      (hm₁.mul hm₂).aestronglyMeasurable
    filter_upwards [hex, hey] with r hex hey
    have h₁ := norm_add_le (spaceSplittingStationaryMain T b₁ r x x' -
      spaceSplittingCircleIntegral b₁ r x x') (spaceSplittingCircleIntegral b₁ r x x')
    have h₂ := norm_add_le (spaceSplittingStationaryMain T b₂ r y y' -
      spaceSplittingCircleIntegral b₂ r y y') (spaceSplittingCircleIntegral b₂ r y y')
    rw [sub_add_cancel, norm_sub_rev] at h₁ h₂
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul (by linarith [norm_spaceSplittingCircleIntegral_le hb₁ hbound₁ r x x'])
      (by linarith [norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y'])
      (norm_nonneg _) (by positivity)
  have heq : (∫ r : ℝ, orthogonalityRadialAmplitude K v r *
        spaceSplittingStationaryMain T b₁ r x x' *
          spaceSplittingStationaryMain T b₂ r y y') =
      ∫ r, spaceSplittingStationaryMain T b₁ r x x' *
        spaceSplittingStationaryMain T b₂ r y y' ∂μ := by
    rw [integral_maskedFourierRadialMeasure]
    simp only [Complex.real_smul, ← orthogonalityRadialAmplitude_eq_real_weight, mul_assoc]
  rw [spaceSplittingAveragedCircleKernel_eq_radial, heq, ← integral_sub hiC hiM]
  have hb : ∀ᵐ r ∂μ, ‖spaceSplittingCircleIntegral b₁ r x x' *
      spaceSplittingCircleIntegral b₂ r y y' -
      spaceSplittingStationaryMain T b₁ r x x' *
        spaceSplittingStationaryMain T b₂ r y y'‖ ≤ (4 * Real.pi + δ) * δ := by
    filter_upwards [hex, hey] with r hex hey
    exact norm_circle_product_sub_stationary_product_le hδ
      (norm_spaceSplittingCircleIntegral_le hb₁ hbound₁ r x x')
      (norm_spaceSplittingCircleIntegral_le hb₂ hbound₂ r y y') hex hey
  simpa only [μ, mul_assoc, mul_comm, mul_left_comm] using
    (norm_integral_le_of_norm_le_const hb)
end FalconerThetaGauge
