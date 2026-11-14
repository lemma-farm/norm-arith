import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Thickening

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Parabolic.Basic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic space-time geometry

The spatial geometry uses the Euclidean norm on `Fin 3 → ℝ`, defined from the
finite sum of squares.  This is deliberate: the ambient function space's
default norm can be the sup norm, whereas the cylinders here are Euclidean.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
abbrev Vec3 := Fin 3 → ℝ

def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Ambient.Basic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Ambient coordinate carriers

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps only the coordinate carrier needed by the
weak-derivative API and uses the `CKN` namespace.
-/
namespace CKN
/-- The native coordinate model of a finite-dimensional real vector space. -/
abbrev Vec (d : ℕ) := Fin d → ℝ
end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Ambient.Basis ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Coordinate basis for native vectors

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port retains the coordinate basis and reconstruction facts
needed to state coordinate weak derivatives, under the `CKN` namespace.
-/
namespace CKN
/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Pressure.LeibnizLaplacian ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# The Leibniz rule for the spatial Laplacian, in weak form

The paper's identity `eq:leibniz-lap`,
`Δ(η T) = η Δ T + 2 ∂_j η ∂_j T + T Δ η`,
is stated there for a scalar distribution `T` and a smooth `η`.  This file
proves the underlying pointwise second-order product rule for smooth functions
on `Vec3 := Fin 3 → ℝ`, and then integrates it against a locally integrable
weight to obtain the weak (test-function) form used in the paper.

Spatial partial derivatives are ordinary partial derivatives, expressed as the
Fréchet derivative applied to a coordinate basis vector, matching the
convention of `CKN.spatialPartial`.
-/
open MeasureTheory Set
open CKN.Foundation.Parabolic
namespace CKN
noncomputable section
/-! ## Spatial partial derivatives and their product rules -/
/-- The `i`th spatial partial derivative `∂_i f`, as the Fréchet derivative applied
to the `i`th coordinate basis vector. -/
def spatialDeriv (f : Vec3 → ℝ) (i : Fin 3) : Vec3 → ℝ :=
  fun x => (fderiv ℝ f x) (basisVec i)

end
end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Harmonic.NewtonianRepresentation ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology Interval
open MeasureTheory MeasureTheory.Measure Set Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
open CKN.Foundation.Parabolic
/-! The Newtonian kernel representation obtained from the heat semigroup. -/
/-- The positive three-dimensional Newtonian kernel. -/
def newtonianKernel (z : Vec3) : ℝ :=
  1 / (4 * Real.pi * vec3EuclideanNorm z)
end CKN.Foundation.Heat

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Cutoff.Basic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Quantitative smooth cutoff data

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps the cutoff bundle and the explicit Euclidean
gradient API in the independent `CKN` namespace.

## Main definitions

* `CKN.vecEuclideanNorm`: the Euclidean norm on native coordinate vectors.
* `CKN.classicalGradient`: the coordinate gradient of a scalar function.
* `CKN.QuantitativeSmoothCutoff`: quantitative smooth cutoff data.

## Main results

* `QuantitativeSmoothCutoff.sq`: squaring a cutoff doubles its gradient bound.
* `QuantitativeSmoothCutoff.sq_toFun` and `QuantitativeSmoothCutoff.sq_apply`:
  the square operation has the expected pointwise form.
* `QuantitativeSmoothCutoff.mem_Icc`: every cutoff value lies in `[0, 1]`.
-/
open scoped BigOperators
namespace CKN
/-- The Euclidean dot product on native coordinate vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i
/-- The square of the Euclidean norm on native coordinate vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x
/-- The Euclidean norm on native coordinate vectors. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

/-- The coordinate gradient of a scalar function in the native vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

namespace QuantitativeSmoothCutoff
variable {d : ℕ}
variable {inner outer : Set (Vec d)}
variable {K : ℝ}

end QuantitativeSmoothCutoff
end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Cutoff.Ball ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Quantitative smooth cutoffs for round balls

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent port uses the native `Fin d → ℝ` carrier and an
explicit Euclidean squared distance.

## Main definitions

* `euclideanBall` and `euclideanClosedBall`: round balls for the explicit
  Euclidean norm.
* `canonicalBallCutoff`: a smooth cutoff with a midpoint support collar.

## Main results

* `canonicalBallCutoff_smooth`, `canonicalBallCutoff_eq_one_on_inner`, and
  `canonicalBallCutoff_tsupport_subset_outer` give the qualitative cutoff
  properties.
* `canonicalBallCutoff_gradient_bound` gives the explicit bound
  `32 / (R - r)`.
-/
open Set
noncomputable section
namespace CKN
/-- Euclidean squared distance on native vectors. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)
/-- The explicit round Euclidean open ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}
/-- The explicit round Euclidean closed ball. -/
def euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}

end CKN

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Mollify.Basic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# ContDiffBump mollification

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The custom convex-approximation chain was not used here: Mathlib
v4.34 already provides normalized `ContDiffBump` kernels, convolution
regularity, and approximate-identity convergence. This direct port keeps the
kernel and convolution API independent of the sibling geometry layer.
-/
open scoped Convolution Topology
namespace CKN
/-- A smooth bump centered at zero with outer radius `ε`. -/
noncomputable def standardMollifier {d : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ContDiffBump (0 : Vec d) :=
  { rIn := ε / 2
    rOut := ε
    rIn_pos := half_pos hε
    rIn_lt_rOut := half_lt_self hε }
/-- The normalized scalar kernel associated with `standardMollifier`. -/
noncomputable def mollifier {d : ℕ} (ε : ℝ) (hε : 0 < ε) : Vec d → ℝ :=
  (standardMollifier ε hε).normed MeasureTheory.volume

noncomputable def mollify {d : ℕ} (u : Vec d → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Vec d → ℝ :=
  MeasureTheory.convolution (mollifier (d := d) ε hε) u
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Pressure.Cutoff ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# A smooth ball cut-off with two derivative bounds

The native carrier is `Fin 3 → ℝ`.  The cut-off below is obtained by
convolving the indicator of the `7ρ/10` ball with a normalized smooth bump.
The bump is chosen with a slightly smaller inherited-metric radius so that
its Euclidean support has a strict collar in the native carrier.  This keeps
the stated Euclidean radii literal while avoiding an implicit change of norm.
-/
open Set MeasureTheory Metric
open scoped Convolution
set_option autoImplicit false
noncomputable section
namespace CKN

private def ballIndicator (x₀ : Vec 3) (R : ℝ) : Vec 3 → ℝ :=
  (euclideanBall x₀ R).indicator (fun _ => 1)

private def unitBallCutoff : Vec 3 → ℝ :=
  mollify (ballIndicator 0 (7 / 10)) (1 / 100) (by norm_num)

/-- The convolution cut-off at center `x₀` and radius `ρ`. -/
def mollifiedBallCutoff (x₀ : Vec 3) {ρ : ℝ} (_hρ : 0 < ρ) : Vec 3 → ℝ :=
  fun x => unitBallCutoff (ρ⁻¹ • (x - x₀))

/-- The absolute unit-scale gradient constant of the convolution cut-off. -/
noncomputable def cutoffGradientConstant : ℝ :=
  sSup (Set.range (fun x : Vec 3 =>
    vecEuclideanNorm (classicalGradient unitBallCutoff x)))
/-- The absolute unit-scale second-derivative constant of the convolution
cut-off. -/
noncomputable def cutoffSecondDerivativeConstant : ℝ :=
  sSup (Set.range (fun x : Vec 3 =>
    ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖))

end CKN

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Harmonic.InteriorBasic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
/-!
# Harmonic interior estimates from the Newtonian representation

Kernel and integration-by-parts infrastructure for the representation route.
-/
noncomputable section
namespace CKN.Foundation.Heat

def eta (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) : Vec3 → ℝ :=
  mollifiedBallCutoff x₀ hρ
/-- The Newtonian kernel times one cutoff derivative. -/
def kernelCutoffDerivative (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (i : Fin 3) (y : Vec3) : ℝ :=
  newtonianKernel (x - y) * spatialDeriv (eta x₀ hρ) i y

end CKN.Foundation.Heat

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Harmonic.InteriorEstimatesBasic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat

def cutoffAnnulus (x₀ : Vec3) (ρ : ℝ) : Set Vec3 :=
  euclideanBall x₀ (3 * ρ / 4) \ euclideanClosedBall x₀ (13 * ρ / 20)
noncomputable def harmonicInteriorGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 900 * (3 / 4) * cutoffGradientConstant +
    (4 * Real.pi)⁻¹ * 30 * (9 / 16) * cutoffSecondDerivativeConstant
end CKN.Foundation.Heat

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_deff641b9e5f36b10441_InteriorSupSmoothBoundSupport ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat

set_option linter.unusedVariables false in
/-- Bounds the differentiated cutoff kernel at the three-quarter scale. -/
lemma kernel_cutoff_derivative_bound_scaled_three_quarters
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) (i j : Fin 3) 
    (h_CKN_Foundation_Heat_newtonianKernel_spatialDeriv_size_bound : ∀ {z : CKN.Foundation.Parabolic.Vec3},
      z ≠ 0 →
        ∀ (i : Fin 3),
          |CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i z| ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹)
    (h_CKN_Foundation_Heat_newtonianKernel_size_bound : ∀ {z : CKN.Foundation.Parabolic.Vec3},
      z ≠ 0 → |CKN.Foundation.Heat.newtonianKernel z| ≤ (4 * Real.pi)⁻¹ * ‖z‖⁻¹)
    (h_CKN_Foundation_Heat_eta_spatialDeriv_bound_global : ∀ (x₀ : CKN.Foundation.Parabolic.Vec3) {ρ : ℝ} (hρ : 0 < ρ) (y : CKN.Foundation.Parabolic.Vec3)
      (i : Fin 3),
      |CKN.spatialDeriv (CKN.Foundation.Heat.eta x₀ hρ) i y| ≤ CKN.cutoffGradientConstant / ρ)
    (h_CKN_Foundation_Heat_eta_spatialSecond_bound_global : ∀ (x₀ : CKN.Foundation.Parabolic.Vec3) {ρ : ℝ} (hρ : 0 < ρ) (y : CKN.Foundation.Parabolic.Vec3)
      (i j : Fin 3),
      |CKN.spatialDeriv (CKN.spatialDeriv (CKN.Foundation.Heat.eta x₀ hρ) i) j y| ≤
        CKN.cutoffSecondDerivativeConstant / ρ ^ 2)
    (h_CKN_Foundation_Heat_cutoff_annulus_norm_distance_for_three_quarters : ∀ {x x₀ : CKN.Foundation.Parabolic.Vec3} {ρ : ℝ},
      0 < ρ →
        x ∈ CKN.euclideanBall x₀ (3 * ρ / 4) →
          ∀ {y : CKN.Foundation.Parabolic.Vec3},
            y ∈ CKN.Foundation.Heat.cutoffAnnulus x₀ (4 * ρ / 3) → ρ / 30 < ‖x - y‖)
    (h_CKN_Foundation_Heat_spatialDeriv_kernelCutoffDerivative_of_ne : ∀ {x x₀ y : CKN.Foundation.Parabolic.Vec3} {ρ : ℝ} (hρ : 0 < ρ),
      x - y ≠ 0 →
        ∀ (i j : Fin 3),
          CKN.spatialDeriv (CKN.Foundation.Heat.kernelCutoffDerivative x x₀ hρ i) j y =
            CKN.spatialDeriv
                  (fun (z : CKN.Foundation.Parabolic.Vec3) ↦
                    CKN.Foundation.Heat.newtonianKernel (x - z))
                  j y *
                CKN.spatialDeriv (CKN.Foundation.Heat.eta x₀ hρ) i y +
              CKN.Foundation.Heat.newtonianKernel (x - y) *
                CKN.spatialDeriv (CKN.spatialDeriv (CKN.Foundation.Heat.eta x₀ hρ) i) j y)
    (h_CKN_Foundation_Heat_spatialDeriv_newtonianKernel_shift_eq_neg : ∀ {x y : CKN.Foundation.Parabolic.Vec3},
      x - y ≠ 0 →
        ∀ (i : Fin 3),
          CKN.spatialDeriv
              (fun (z : CKN.Foundation.Parabolic.Vec3) ↦ CKN.Foundation.Heat.newtonianKernel (x - z)) i
              y =
            -CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y))
    :
    |CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
        x x₀ (by positivity) i) j y| ≤
      harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ := by
  have hdist := h_CKN_Foundation_Heat_cutoff_annulus_norm_distance_for_three_quarters hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hdist
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hdist)
  rw [h_CKN_Foundation_Heat_spatialDeriv_kernelCutoffDerivative_of_ne (by positivity) hxy]
  calc
    |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y *
          CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
        newtonianKernel (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) j y| ≤
        |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y| *
          |CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y| +
        |newtonianKernel (x - y)| *
          |CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) j y| := by
      calc
        |_ + _| ≤ |_| + |_| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ *
          (cutoffGradientConstant / (4 * ρ / 3)) +
        (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ *
          (cutoffSecondDerivativeConstant / (4 * ρ / 3) ^ 2) := by
      have hderiv := h_CKN_Foundation_Heat_newtonianKernel_spatialDeriv_size_bound hxy j
      have hinv : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 30) ^ 2)⁻¹ := by gcongr
      have heta := h_CKN_Foundation_Heat_eta_spatialDeriv_bound_global x₀
        (ρ := 4 * ρ / 3) (by positivity) y i
      have hsecond := h_CKN_Foundation_Heat_eta_spatialSecond_bound_global x₀
        (ρ := 4 * ρ / 3) (by positivity) y i j
      have hkernel := h_CKN_Foundation_Heat_newtonianKernel_size_bound hxy
      have hdistinv : ‖x - y‖⁻¹ ≤ (ρ / 30)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).2 hdist.le
      have hderiv' : |CKN.spatialDeriv newtonianKernel j (x - y)| ≤
          (4 * Real.pi)⁻¹ * ((ρ / 30) ^ 2)⁻¹ :=
        hderiv.trans (mul_le_mul_of_nonneg_left hinv (by positivity))
      have hkernel' : |newtonianKernel (x - y)| ≤
          (4 * Real.pi)⁻¹ * (ρ / 30)⁻¹ :=
        hkernel.trans (mul_le_mul_of_nonneg_left hdistinv (by positivity))
      rw [show |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) j y| =
          |CKN.spatialDeriv newtonianKernel j (x - y)| by
            rw [h_CKN_Foundation_Heat_spatialDeriv_newtonianKernel_shift_eq_neg hxy, abs_neg]]
      gcongr
    _ = harmonicInteriorGradientConstant * (ρ ^ 3)⁻¹ := by
      dsimp [harmonicInteriorGradientConstant]
      field_simp [hρ.ne']
      ring
end CKN.Foundation.Heat
