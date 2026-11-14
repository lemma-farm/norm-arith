import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Basic ====
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

def parabolicDist (p q : ParabolicPoint) : ℝ :=
  max (vec3EuclideanNorm (p.1 - q.1)) (Real.sqrt |p.2 - q.2|)

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Holder ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Hölder bounds for the parabolic metric

This module names the seminorm used by the space-time regularity statements.
The measure-theoretic representative predicate records agreement on a set.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory Set
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
def ParabolicHolderSeminormLE
    (U : Set ParabolicPoint) (g : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |g x - g y| ≤ K * parabolicDist x y ^ α
namespace ParabolicHolderSeminormLE
end ParabolicHolderSeminormLE
end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Campanato ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Campanato oscillations on parabolic cylinders

The `L^p` oscillation of a function on a parabolic cylinder, the Campanato
bound it satisfies on a region, the tail constant of the dyadic geometric
series, and the comparison of the average of `|f|` on a subset with the
average on the ambient set.  The oscillations use genuine space-time averages.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
def parabolicCampanatoTailConstant (α : ℝ) : ℝ :=
  1 / (1 - (2 : ℝ) ^ (-α))
end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.CampanatoHolder ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
def parabolicCampanatoHolderConstant (α p : ℝ) : ℝ :=
  (2 * parabolicCampanatoTailConstant α + 1) *
    (2 : ℝ) ^ (5 / p) * (8 : ℝ) ^ α
end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_1e11aef6ccb2d8467a6d_HeatHolderComplex ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Parabolic
theorem heat_holder_complex_components_bound
    {gRe gIm : ParabolicPoint → ℝ} {α K p : ℝ}
    (hRe : ParabolicHolderSeminormLE Set.univ gRe α
      (parabolicCampanatoHolderConstant α p * K))
    (hIm : ParabolicHolderSeminormLE Set.univ gIm α
      (parabolicCampanatoHolderConstant α p * K)) :
    ∀ z z' : ParabolicPoint,
      ‖((gRe z : ℂ) + Complex.I * (gIm z : ℂ)) -
          ((gRe z' : ℂ) + Complex.I * (gIm z' : ℂ))‖ ≤
        2 * (parabolicCampanatoHolderConstant α p * K) *
          parabolicDist z z' ^ α := by
  intro z z'
  have hRe' := hRe z (Set.mem_univ z) z' (Set.mem_univ z')
  have hIm' := hIm z (Set.mem_univ z) z' (Set.mem_univ z')
  calc
    ‖((gRe z : ℂ) + Complex.I * (gIm z : ℂ)) -
        ((gRe z' : ℂ) + Complex.I * (gIm z' : ℂ))‖ =
        ‖((gRe z - gRe z' : ℝ) : ℂ) +
          Complex.I * ((gIm z - gIm z' : ℝ) : ℂ)‖ := by
            congr 1
            push_cast
            ring
    _ ≤ ‖((gRe z - gRe z' : ℝ) : ℂ)‖ +
          ‖Complex.I * ((gIm z - gIm z' : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |gRe z - gRe z'| + |gIm z - gIm z'| := by
      simp only [Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
        Real.norm_eq_abs]
    _ ≤ (parabolicCampanatoHolderConstant α p * K) *
          parabolicDist z z' ^ α +
        (parabolicCampanatoHolderConstant α p * K) *
          parabolicDist z z' ^ α := add_le_add hRe' hIm'
    _ = 2 * (parabolicCampanatoHolderConstant α p * K) *
          parabolicDist z z' ^ α := by ring
end CKN.Core.HeatPotential
