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

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Parabolic.Basic ====
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

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Sobolev.Ambient.Basic ====
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

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Ambient.Euclidean ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Euclidean functions on the native ambient carrier

`Space` is a reducible abbreviation of the existing `CKN.Vec 3` carrier, so
all native-space statements use the same type as the Sobolev interfaces. The
body of `spaceEuclideanNorm` is kept definitionally identical to the
finite-sum expression used by the parabolic spatial norm.
-/
namespace CKN
/-- The native three-dimensional carrier, definitionally equal to `Vec 3`. -/
abbrev Space := Vec 3
/-- The Euclidean length given by the finite sum of coordinate squares. -/
noncomputable def spaceEuclideanNorm (x : Space) : ℝ := Real.sqrt (∑ k, x k ^ 2)

end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Sobolev.Cutoff.Basic ====
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

namespace QuantitativeSmoothCutoff
variable {d : ℕ}
variable {inner outer : Set (Vec d)}
variable {K : ℝ}

end QuantitativeSmoothCutoff
end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Sobolev.Cutoff.Ball ====
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

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vd20c8d1f409f.CKN.Foundation.Harmonic.InteriorEstimatesBasic ====
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
end CKN.Foundation.Heat

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_f6497eda5a4ed2ba8160_InteriorSupSmoothBoundSupport ====
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
/-- Bounds the cutoff annulus away from the three-quarter ball. -/
lemma cutoff_annulus_norm_distance_for_three_quarters
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (3 * ρ / 4))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ (4 * ρ / 3)) 
    (h_CKN_Foundation_Parabolic_vec3EuclideanNorm_eq_l2 : ∀ (v : CKN.Foundation.Parabolic.Vec3),
      CKN.Foundation.Parabolic.vec3EuclideanNorm v = ‖WithLp.toLp 2 v‖)
    (h_CKN_mem_euclideanBall_iff_vecEuclideanNorm_lt : ∀ {d : ℕ} {x₀ x : CKN.Vec d} {R : ℝ},
      0 < R → (x ∈ CKN.euclideanBall x₀ R ↔ CKN.vecEuclideanNorm (x - x₀) < R))
    (h_CKN_mem_euclideanClosedBall_iff_vecEuclideanNorm_le : ∀ {d : ℕ} {x₀ x : CKN.Vec d} {R : ℝ},
      0 ≤ R → (x ∈ CKN.euclideanClosedBall x₀ R ↔ CKN.vecEuclideanNorm (x - x₀) ≤ R))
    (h_CKN_euclideanNorm_le_three_mul_space_norm : ∀ (x : CKN.Space), CKN.spaceEuclideanNorm x ≤ 3 * ‖x‖)
    :
    ρ / 30 < ‖x - y‖ := by
  have hx' : vec3EuclideanNorm (x - x₀) < 3 * ρ / 4 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (h_CKN_mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have hy' : 13 * (4 * ρ / 3) / 20 < vec3EuclideanNorm (y - x₀) := by
    have hnot : y ∉ euclideanClosedBall x₀ (13 * (4 * ρ / 3) / 20) := hy.2
    by_contra hle
    apply hnot
    apply (h_CKN_mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact le_of_not_gt (by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
        using hle)
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (x - y) + vec3EuclideanNorm (x - x₀) := by
    rw [h_CKN_Foundation_Parabolic_vec3EuclideanNorm_eq_l2, h_CKN_Foundation_Parabolic_vec3EuclideanNorm_eq_l2,
      h_CKN_Foundation_Parabolic_vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (y - x₀)‖ =
          ‖WithLp.toLp 2 ((y - x) + (x - x₀))‖ := by
            congr 1
            ext i
            simp
      _ ≤ ‖WithLp.toLp 2 (y - x)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := norm_add_le _ _
      _ = _ := by
        rw [show y - x = -(x - y) by ext i; simp,
          WithLp.toLp_neg, norm_neg]
  have hEuclideanGap : 7 * ρ / 60 < vec3EuclideanNorm (x - y) := by
    rw [show 13 * (4 * ρ / 3) / 20 = 13 * ρ / 15 by ring] at hy'
    nlinarith only [hx', hy', htri]
  have hthree := h_CKN_euclideanNorm_le_three_mul_space_norm (x - y)
  have hthree' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  nlinarith only [hEuclideanGap, hthree', hρ]
end CKN.Foundation.Heat
