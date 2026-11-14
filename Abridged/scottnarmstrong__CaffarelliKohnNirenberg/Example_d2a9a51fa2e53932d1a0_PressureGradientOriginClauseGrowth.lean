import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.FunProp
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
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Basic ====
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

def ParabolicPoint := Vec3 × ℝ

def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)
instance : MeasurableSpace ParabolicPoint := inferInstanceAs (MeasurableSpace (Vec3 × ℝ))

def vec3Ball (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) < r}

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_d2a9a51fa2e53932d1a0_PressureGradientOriginClauseGrowth ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Pressure oscillation on clipped origin windows

The pressure contribution to the slice bound is controlled by its spatial
`3/2` power mass and Hölder in time. The required mass exponent is
`13/2 - 15/(2κ)`, which yields the gradient mass exponent `5 - 6/κ`.
The separate large-radius estimate is supplied by
`pressure_gradient_origin_cylinder_large_cell_le` in `PressureGradientLargeCells`.
No estimate for the complete slice majorant is asserted here.
-/
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic  
noncomputable section
namespace CKN.Core.Step4
set_option linter.unusedVariables false in
/-- Hölder in a clipped time window for the pressure part of the doubled
slice estimate, retaining its spatial power mass on that same window. -/
theorem originClause_pressure_clipped_holder
    {P : ParabolicPoint → ℝ} {x : Vec3} {t r R : ℝ} (hr : 0 < r)
    (hm : AEStronglyMeasurable P
      ((volume.restrict (vec3Ball x (2*r))).prod
        (volume.restrict (Ioc (t-r^2) t ∩ Ioc (-R^2) 0)))) 
    (h_CKN_Core_Step4_lintegral_rpow_le_rpow_lintegral_mul_measure : ∀ {α : Type} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {J : α → ENNReal},
      AEMeasurable J μ →
        ∀ {θ : ℝ},
          0 < θ →
            θ < 1 →
              ∫⁻ (s : α), J s ^ θ ∂μ ≤
                (∫⁻ (s : α), J s ∂μ) ^ θ * (μ : Set α → ENNReal) Set.univ ^ (1 - θ))
    :
    (∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-R^2) 0,
      (ENNReal.ofReal ((2*r) ^ (-1/2 : ℝ)) *
        eLpNorm (fun y => P (y,s)) (ENNReal.ofReal (3/2 : ℝ))
          (volume.restrict (vec3Ball x (2*r)))) ^ (6/5 : ℝ)) ≤
    ENNReal.ofReal ((2*r) ^ (-3/5 : ℝ)) *
      ((∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-R^2) 0,
        ∫⁻ y in vec3Ball x (2*r), ‖P (y,s)‖ₑ ^ (3/2 : ℝ)) ^ (4/5 : ℝ) *
        ENNReal.ofReal (r^2) ^ (1/5 : ℝ)) := by
  let W := Ioc (t-r^2) t ∩ Ioc (-R^2) 0
  let J := fun s => ∫⁻ y in vec3Ball x (2*r), ‖P (y,s)‖ₑ ^ (3/2 : ℝ)
  have hJ : AEMeasurable J (volume.restrict W) :=
    (hm.aemeasurable.enorm.pow_const (3/2 : ℝ)).lintegral_prod_left'
  have h2r : 0 < 2*r := by positivity
  have heq : ∀ᵐ s ∂volume.restrict W,
      (ENNReal.ofReal ((2*r) ^ (-1/2 : ℝ)) *
        eLpNorm (fun y => P (y,s)) (ENNReal.ofReal (3/2 : ℝ))
          (volume.restrict (vec3Ball x (2*r)))) ^ (6/5 : ℝ) =
      ENNReal.ofReal ((2*r) ^ (-3/5 : ℝ)) * J s ^ (4/5 : ℝ) := by
    filter_upwards [hm.prodMk_right] with s hs
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top hs]
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3/2),
      show (1 / (3/2) : ℝ) = 2/3 by norm_num]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6/5),
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos h2r _),
      ← Real.rpow_mul h2r.le, ← ENNReal.rpow_mul]
    norm_num only [show (-1/2 : ℝ)*(6/5) = -3/5 by norm_num,
      show (2/3 : ℝ)*(6/5) = 4/5 by norm_num]
    rfl
  have hv : volume W ≤ ENNReal.ofReal (r^2) := by
    calc volume W ≤ volume (Ioc (t-r^2) t) := measure_mono inter_subset_left
         _ = _ := by rw [Real.volume_Ioc]; congr 1; ring_nf
  rw [lintegral_congr_ae heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply mul_le_mul' le_rfl
  have hh := h_CKN_Core_Step4_lintegral_rpow_le_rpow_lintegral_mul_measure hJ
    (by norm_num : (0 : ℝ) < 4/5) (by norm_num : (4/5 : ℝ) < 1)
  simp only [Measure.restrict_apply_univ, show (1-4/5 : ℝ) = 1/5 by norm_num] at hh
  exact hh.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hv (by norm_num)))
end CKN.Core.Step4
