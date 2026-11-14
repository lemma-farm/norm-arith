import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
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
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Basic ====
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
abbrev L2Vec3 := PiLp 2 (fun _ : Fin 3 => ℝ)
def ParabolicPoint := Vec3 × ℝ
axiom half_pos : 0 < (1 / 2 : ℝ)
axiom half_le_one : (1 / 2 : ℝ) ≤ 1
abbrev SnowTime := Metric.Snowflaking ℝ (1 / 2 : ℝ) half_pos half_le_one
def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)
instance : MeasurableSpace ParabolicPoint := inferInstanceAs (MeasurableSpace (Vec3 × ℝ))
instance : MeasurableSpace SnowTime := borel SnowTime
set_option linter.unusedVariables false in
axiom _root_.CKN.Foundation.Parabolic.instBorelSpaceSnowTime : BorelSpace CKN.Foundation.Parabolic.SnowTime
attribute [instance] _root_.CKN.Foundation.Parabolic.instBorelSpaceSnowTime
def parabolicMeasurableEquiv : ParabolicPoint ≃ᵐ L2Vec3 × SnowTime :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 Vec3) {
    toEquiv := Metric.Snowflaking.toSnowflaking
    measurable_toFun := Metric.Snowflaking.continuous_toSnowflaking.measurable
    measurable_invFun := Metric.Snowflaking.homeomorph.continuous.measurable }
def parabolicMap (p : ParabolicPoint) :
    L2Vec3 × SnowTime := parabolicMeasurableEquiv p
axiom parabolicMap_injective : Function.Injective parabolicMap
noncomputable instance parabolicMetricSpace : MetricSpace ParabolicPoint :=
  MetricSpace.induced parabolicMap parabolicMap_injective inferInstance
abbrev parabolicPseudoMetricSpace : PseudoMetricSpace ParabolicPoint :=
  MetricSpace.toPseudoMetricSpace (self := parabolicMetricSpace)

def parabolicDist (p q : ParabolicPoint) : ℝ :=
  max (vec3EuclideanNorm (p.1 - q.1)) (Real.sqrt |p.2 - q.2|)
axiom dist_eq_parabolicDist (p q : ParabolicPoint) :
    dist p q = parabolicDist p q

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Vec3Norm ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic

/-- The Euclidean norm on `Vec3` is invariant under negation. -/
axiom vec3EuclideanNorm_neg (v : Vec3) :
    vec3EuclideanNorm (-v) = vec3EuclideanNorm v

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Core.HeatPotential.Far ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open  CKN.Foundation.Parabolic

axiom vec3EuclideanNorm_add_le (x y : Vec3) :
    vec3EuclideanNorm (x + y) ≤ vec3EuclideanNorm x + vec3EuclideanNorm y
end CKN.Core.HeatPotential

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplitData ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology Distributions
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open   CKN.Foundation.Parabolic

open CKN.Core.HeatPotential
/- The smooth symbol class used by the split node. -/
def multiplierHeatShellSet (z : ParabolicPoint) (r : ℝ) (j : ℕ) : Set ParabolicPoint :=
  Metric.ball z ((2 : ℝ) ^ (j + 1) * r) \
    Metric.ball z ((2 : ℝ) ^ j * r)
end CKN.Core.HeatPotential

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_1fca705397899d1b7ed6_HeatFarAssemblyGeometry ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Geometry of a far shell and the mass of its source

Fix a base point `z`, a radius `r > 0` and a shell index `j ≥ 6`, and write
`R = 2 ^ j r` for the inner radius of the shell
`multiplierHeatShellSet z r j`.  Two facts about that shell are used by every
far estimate.

* **Separation.**  An observation point `q` in the closed ball of radius `r`
  around `z` is separated from every shell point `v` whose time lies below
  `q.2`: the parabolic gauge
  `max ‖q.1 - v.1‖ √(q.2 - v.2)` is at least `R / 2`.  The shell is at
  parabolic distance at least `R` from `z` while `q` is at distance at most
  `r ≤ R / 64`, so the excess `R - r` survives in whichever of the two
  coordinates carries the shell separation.  When the shell separates in time
  and the shell point lies *after* `z`, no such `q` exists at all, which is
  why the causal restriction `q.2 ≥ v.2` is part of the statement.

* **Mass.**  The shell sits inside a parabolic cylinder of radius `4 R`, so
  the Morrey seminorm of the source controls its absolute mass by
  `R ^ (5 - 5/θ)` and the source is integrable there.

Both statements fix their constants before the source and before the shell
data.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Parabolic 

/-- A square root bound transported to the square. -/
private axiom farShellAssembly_geometry_sq_of_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (h : Real.sqrt x ≤ y) :
    x ≤ y ^ 2
/-- The inner radius of a far shell is at least `64 r`. -/
axiom farShellAssembly_radius_ge {r : ℝ} (hr : 0 < r) {j : ℕ} (hj : 6 ≤ j) :
    64 * r ≤ (2 : ℝ) ^ j * r
/-- **Parabolic separation on a far shell.**  An observation point in the
closed ball of radius `r` around `z` sees every causally relevant point of the
shell `multiplierHeatShellSet z r j` at parabolic gauge at least
`(2 ^ j r) / 2`. -/
theorem farShellAssembly_gauge_lower {z v q : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hj : 6 ≤ j) (hv : v ∈ multiplierHeatShellSet z r j)
    (hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hqv : 0 ≤ q.2 - v.2) :
    (2 : ℝ) ^ j * r / 2 ≤
      max (vec3EuclideanNorm (q.1 - v.1)) (Real.sqrt (q.2 - v.2)) := by
  set R : ℝ := (2 : ℝ) ^ j * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hR64 : 64 * r ≤ R := farShellAssembly_radius_ge hr hj
  obtain ⟨-, hvout⟩ := hv
  have hvz : R ≤ dist v z := by
    by_contra hcon
    exact hvout (Metric.mem_ball.mpr (not_le.mp hcon))
  rw [dist_eq_parabolicDist] at hvz
  have hvz' : R ≤ max (vec3EuclideanNorm (v.1 - z.1)) (Real.sqrt |v.2 - z.2|) := hvz
  have hqz : dist q z ≤ r := Metric.mem_closedBall.mp hq
  rw [dist_eq_parabolicDist] at hqz
  have hqs : vec3EuclideanNorm (q.1 - z.1) ≤ r := (le_max_left _ _).trans hqz
  have hqt : Real.sqrt |q.2 - z.2| ≤ r := (le_max_right _ _).trans hqz
  have hqt2 : |q.2 - z.2| ≤ r ^ 2 := farShellAssembly_geometry_sq_of_sqrt_le (abs_nonneg _) hqt
  have hrsq : r ^ 2 ≤ R ^ 2 / 4096 := by
    have h1 : 0 ≤ r := hr.le
    nlinarith only [hR64, h1, hRpos]
  rcases le_max_iff.mp hvz' with hcase | hcase
  · refine le_trans ?_ (le_max_left _ _)
    have htri : vec3EuclideanNorm (v.1 - z.1) ≤
        vec3EuclideanNorm (q.1 - v.1) + vec3EuclideanNorm (q.1 - z.1) := by
      have hsplit : v.1 - z.1 = -(q.1 - v.1) + (q.1 - z.1) := by abel
      rw [hsplit]
      exact (vec3EuclideanNorm_add_le _ _).trans_eq
        (by rw [vec3EuclideanNorm_neg])
    linarith only [hcase, htri, hqs, hR64, hr]
  · refine le_trans ?_ (le_max_right _ _)
    have hsq : R ^ 2 ≤ |v.2 - z.2| := by
      have hpow : R ^ 2 ≤ (Real.sqrt |v.2 - z.2|) ^ 2 :=
        pow_le_pow_left₀ hRpos.le hcase 2
      rwa [Real.sq_sqrt (abs_nonneg _)] at hpow
    have hR2pos : (0 : ℝ) < R ^ 2 := pow_pos hRpos 2
    have hquarter : R ^ 2 / 4 ≤ q.2 - v.2 := by
      rcases le_or_gt v.2 z.2 with hvt | hvt
      · have habs : |v.2 - z.2| = z.2 - v.2 := by
          rw [abs_of_nonpos (by linarith only [hvt])]; ring
        have hlow : -(r ^ 2) ≤ q.2 - z.2 := (abs_le.mp hqt2).1
        rw [habs] at hsq
        linarith only [hsq, hlow, hrsq, hR2pos]
      · have habs : |v.2 - z.2| = v.2 - z.2 := by
          rw [abs_of_nonneg (by linarith only [hvt])]
        have hhigh : q.2 - z.2 ≤ r ^ 2 := (abs_le.mp hqt2).2
        rw [habs] at hsq
        exact absurd hqv (by
          have : q.2 - v.2 ≤ r ^ 2 - R ^ 2 := by linarith only [hsq, hhigh]
          have hneg : r ^ 2 - R ^ 2 < 0 := by
            linarith only [hrsq, hR2pos]
          exact not_le.mpr (by linarith only [this, hneg]))
    have hhalf : R / 2 = Real.sqrt ((R / 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [hhalf]
    refine Real.sqrt_le_sqrt ?_
    have : (R / 2) ^ 2 = R ^ 2 / 4 := by ring
    linarith only [hquarter, this.le, this.ge]

end CKN.Core.HeatPotential
