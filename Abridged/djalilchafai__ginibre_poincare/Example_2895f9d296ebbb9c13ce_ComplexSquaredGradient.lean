module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Tactic.Positivity
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Concrete.Configuration ====
public section
@[expose] public section
/-!
# Configuration space and particle permutations

The configuration space of `n` planar particles is `Fin n → ℂ`.  This file
defines particle relabelling, symmetric and alternating observables, and the
collision locus.  It contains no measure-theoretic or analytic input.
-/
namespace GinibrePoincare
/-- The configuration space of `n` labelled particles in the complex plane. -/
abbrev Configuration (n : ℕ) := Fin n → ℂ

end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Concrete.Wirtinger ====
public section
@[expose] public section
/-!
# Concrete Wirtinger derivatives and Gaussian holomorphic distance

The coordinate operators
`∂̄_k = (∂_{x_k} + i ∂_{y_k}) / 2` are defined directly from the real
Fréchet derivative on `Configuration n`.
-/
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
/-- A vector supported in one complex coordinate. -/
def coordinateDirection {n : ℕ} (k : Fin n) (w : ℂ) :
    Configuration n :=
  fun j => if j = k then w else 0
/-- Unit direction in the real part of coordinate `k`. -/
def realCoordinateDirection {n : ℕ} (k : Fin n) :
    Configuration n :=
  coordinateDirection k 1
/-- Unit direction in the imaginary part of coordinate `k`. -/
def imaginaryCoordinateDirection {n : ℕ} (k : Fin n) :
    Configuration n :=
  coordinateDirection k Complex.I
end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Analysis.RadialSobolevClosure ====
public section
@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
/-- The actual real Euclidean gradient, as a vector with `2n` coordinates. -/
def ginibreEuclideanGradient {n : ℕ} (f : Configuration n → ℝ) (z : Configuration n) :
    EuclideanSpace ℝ (Fin n × Fin 2) :=
  WithLp.toLp 2 (fun k => if k.2 = 0 then fderiv ℝ f z (realCoordinateDirection k.1)
    else fderiv ℝ f z (imaginaryCoordinateDirection k.1))
end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Analysis.GinibreWeakGradient ====
public section
@[expose] public section
/-! # Weak gradients and closability for the Ginibre radial completion

Write `ρ` for the concrete, unnormalised real Lebesgue density. Testing with
`ρ ψ` avoids division by the density at collisions. The adjoint test is
`ρ ∂ψ + 2 (∂ρ) ψ`. These identities describe the distributional derivative of
`ρ² u`, and determine the gradient uniquely because `ρ > 0` almost everywhere
for the Ginibre measure. They do not assert the reverse approximation theorem
from an independently defined weak Sobolev space to the radial core.
-/
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
def ginibreCoordinateDirection {n : ℕ} (k : Fin n × Fin 2) : Configuration n :=
  if k.2 = 0 then realCoordinateDirection k.1 else imaginaryCoordinateDirection k.1
axiom ginibreEuclideanGradient_coordinate {n : ℕ} (f : Configuration n → ℝ)
    (z : Configuration n) (k : Fin n × Fin 2) :
    ginibreEuclideanGradient f z k = fderiv ℝ f z (ginibreCoordinateDirection k)
end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Examples.Example_2895f9d296ebbb9c13ce_ComplexSquaredGradient ====
@[expose] public section
/-! # Actual gradient bound for squared complex observables -/
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 500000
def complexDirectionalEnergy {n : ℕ} (F : Configuration n → ℂ) (z : Configuration n) : ℝ :=
  ∑ k : Fin n × Fin 2, Complex.normSq (fderiv ℝ F z (ginibreCoordinateDirection k))
axiom fderiv_complex_normSq {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ ∞ F) (z v : Configuration n) :
    fderiv ℝ (fun w => Complex.normSq (F w)) z v =
      2 * (F z).re * (fderiv ℝ F z v).re + 2 * (F z).im * (fderiv ℝ F z v).im
/-- Cauchy–Schwarz controls the actual squared-real gradient by the complex
directional energy times the squared complex value. -/
theorem ginibreEuclideanGradient_complex_normSq_bound {n : ℕ} (F : Configuration n → ℂ)
    (hF : ContDiff ℝ ∞ F) (z : Configuration n) :
    ‖ginibreEuclideanGradient (fun w => Complex.normSq (F w)) z‖ ^ 2 ≤
      4 * Complex.normSq (F z) * complexDirectionalEnergy F z := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs,sq_abs]
  unfold complexDirectionalEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [ginibreEuclideanGradient_coordinate,fderiv_complex_normSq F hF]
  simp only [Complex.normSq_apply]
  nlinarith [sq_nonneg ((F z).re * (fderiv ℝ F z (ginibreCoordinateDirection k)).im -
    (F z).im * (fderiv ℝ F z (ginibreCoordinateDirection k)).re)]
end
end GinibrePoincare
