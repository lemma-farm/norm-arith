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

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Parabolic.Basic ====
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

def vec3Ball (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) < r}
def parabolicCylinder (x : Vec3) (t r : ℝ) : Set ParabolicPoint :=
  vec3Ball x r ×ˢ Ioc (t - r ^ 2) t

instance : MeasureSpace ParabolicPoint := inferInstanceAs (MeasureSpace (Vec3 × ℝ))

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Parabolic.Morrey.Basic ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic Morrey cells and norms

This module records the extended-real Morrey seminorm on the backward
parabolic cylinders already defined by the parabolic geometry module.  The
metric-ball version is kept alongside it; the two versions are compared by
the inclusions between cylinders and metric balls.
-/
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic.Morrey
private abbrev Q := (5 : ℝ)
/-- The integral part of a Morrey cell on a parabolic cylinder. -/
def cylinderPowerIntegral (p : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ w in parabolicCylinder z.1 z.2 r, ENNReal.ofReal |f w| ^ p
def morreyCell (p q : ℝ) (f : ParabolicPoint → ℝ)
    (z : ParabolicPoint) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal r) ^ (-(Q * (1 - p / q) / p)) *
    (cylinderPowerIntegral p f z r) ^ (1 / p)
/-! The fixed homogeneous dimension in the cylinder normalization. -/
def morreyNorm (p q : ℝ) (f : ParabolicPoint → ℝ) : ℝ≥0∞ :=
  ⨆ z : ParabolicPoint, ⨆ r : {r : ℝ // 0 < r}, morreyCell p q f z r.1

end CKN.Foundation.Parabolic.Morrey

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Parabolic.Morrey.StripMass ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Mass of a parabolic Morrey source on a thin time strip

A parabolic Morrey source of exponents `(p, q)` has controlled mass on every
backward cylinder: on a cylinder of radius `d` the mass is `O(d^{5 - 5/q})`.
The cylinder is isotropic in the parabolic sense, its time width being the
square of its spatial radius.  This module records the *anisotropic* estimate
that a shrinking time strip needs: on

```
parabolicStrip x a R d = vec3Ball x R ×ˢ Ioc (a - d ^ 2) a,
```

a spatial ball of radius `R` crossed with a time interval of the much smaller
width `d ^ 2`, the mass is `O(R ^ 3 * d ^ (2 - 5/q))`.

The estimate is obtained by covering the strip with backward cylinders of
radius `d`.  Because such a cylinder already has the strip's exact time face
`Ioc (a - d ^ 2) a`, the covering is purely spatial: the spatial ball of
radius `R` is cut into `⌈2R/d⌉₊ ^ 3` grid cubes of side at most `d`, and each
cube sits inside a ball of radius `d` since its half-diagonal is `√3/2` times
its side.  Summing the cylinder estimate over the `O((R/d) ^ 3)` cubes turns
`d ^ (5 - 5/q)` into `R ^ 3 * d ^ (2 - 5/q)`, which is the shrinking factor
`(d/R) ^ (2 - 5/q)` times the isotropic mass `R ^ (5 - 5/q)` of the full
cylinder of radius `R`.

No hypothesis beyond measurability of the source and the finiteness of its
Morrey seminorm enters the statements.
-/
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic.Morrey
/-- The thin space-time strip of spatial radius `R` and time width `d ^ 2`
ending at time `a`.  For `d = R` it is the backward parabolic cylinder. -/
def parabolicStrip (x : Vec3) (a R d : ℝ) : Set ParabolicPoint :=
  vec3Ball x R ×ˢ Ioc (a - d ^ 2) a
/-- A strip whose time width matches its spatial radius is a parabolic cylinder. -/
axiom parabolicStrip_self (x : Vec3) (a r : ℝ) :
    parabolicStrip x a r r = parabolicCylinder x a r

/-- **Strip mass estimate, real form.**  One constant, fixed before the source
and before the strip, controls the absolute integral of a parabolic Morrey
source on every thin strip. -/
axiom exists_stripAbsIntegral_bound {P θ : ℝ} (hP : 1 ≤ P) (hPθ : P ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {G : ParabolicPoint → ℝ}, AEMeasurable G volume → morreyNorm P θ G < ∞ →
        ∀ (x : Vec3) (a R d : ℝ), 0 < d → d ≤ R →
          IntegrableOn G (parabolicStrip x a R d) volume ∧
          (∫ v in parabolicStrip x a R d, |G v|) ≤
            C * R ^ 3 * d ^ (2 - 5 / θ) * (morreyNorm P θ G).toReal
end CKN.Foundation.Parabolic.Morrey

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Core.HeatPotential.GeneralSymbolHeatKernelSplitData ====
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
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
/- The smooth symbol class used by the split node. -/
def multiplierHeatShellSet (z : ParabolicPoint) (r : ℝ) (j : ℕ) : Set ParabolicPoint :=
  Metric.ball z ((2 : ℝ) ^ (j + 1) * r) \
    Metric.ball z ((2 : ℝ) ^ j * r)
end CKN.Core.HeatPotential

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vf6f1a4460687.CKN.Foundation.Parabolic.BallDisplays ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# The parabolic ball and its volume

This file records the literal displays of `paper/ckn.tex` that describe the
open parabolic ball `𝔅_r(z)` of the metric `dpar` (equation
`eq:parabolic-ball` and Lemma `lem:parabolic-metric`):

* `𝔅_r(z) = B_r(x) × (t - r², t + r²)` for `z = (x, t)`;
* `C_r(z) ⊆ 𝔅_r(z)` and `𝔅_r(z) ⊆ C_{2r}(x, t + r²)`, where `C_r(z)` is the
  parabolic cylinder `B_r(x) × (t - r², t]`;
* `|𝔅_r(z)| = (8π/3) r⁵`.

The spatial ball `vec3Ball x r` uses the Euclidean norm on `Fin 3 → ℝ`
(`vec3EuclideanNorm`), so its volume is computed by transporting Mathlib's
volume of the Euclidean ball in `EuclideanSpace ℝ (Fin 3)` along the
measure-preserving equivalence `WithLp.toLp 2`.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic

axiom metricBall_subset_parabolicCylinder_doubled (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) :
    Metric.ball z r ⊆ parabolicCylinder z.1 (z.2 + r ^ 2) (2 * r)
end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_2f0c84560a1bdecb00e0_HeatFarAssemblyGeometry ====
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
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

axiom farShellAssembly_shell_subset_ball (z : ParabolicPoint) (r : ℝ) (j : ℕ) :
    multiplierHeatShellSet z r j ⊆ Metric.ball z (2 * ((2 : ℝ) ^ j * r))
/-- **Source mass on a far shell.**  One constant, fixed before the source and
before the shell data, bounds the absolute mass of a finite-Morrey source on
the shell of inner radius `2 ^ j r` by `(2 ^ j r) ^ (5 - 5/θ)` times its
Morrey seminorm, and the source is integrable there. -/
theorem farShellAssembly_exists_shell_mass_bound {P θ : ℝ} (hP : 1 ≤ P)
    (hPθ : P ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {G : ParabolicPoint → ℝ}, AEMeasurable G volume → morreyNorm P θ G < ∞ →
        ∀ (z : ParabolicPoint) (r : ℝ) (j : ℕ), 0 < r →
          IntegrableOn G (multiplierHeatShellSet z r j) volume ∧
          (∫ v in multiplierHeatShellSet z r j, |G v|) ≤
            C * ((2 : ℝ) ^ j * r) ^ (5 - 5 / θ) *
              (morreyNorm P θ G).toReal := by
  obtain ⟨C, hC, hB⟩ := exists_stripAbsIntegral_bound hP hPθ
  have hθpos : (0 : ℝ) < θ := lt_of_lt_of_le zero_lt_one (hP.trans hPθ)
  refine ⟨1024 * C, by positivity, ?_⟩
  intro G hG hGM z r j hr
  set R : ℝ := (2 : ℝ) ^ j * r with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hincl : multiplierHeatShellSet z r j ⊆
      parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R) := by
    rw [parabolicStrip_self]
    intro v hv
    have hball := farShellAssembly_shell_subset_ball z r j hv
    have hcyl := metricBall_subset_parabolicCylinder_doubled z
      (r := 2 * R) (by positivity) hball
    rwa [show 2 * (2 * R) = 4 * R by ring] at hcyl
  obtain ⟨hint, hbd⟩ := hB hG hGM z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R)
    (by positivity) le_rfl
  refine ⟨hint.mono_set hincl, ?_⟩
  have habs : IntegrableOn (fun v => |G v|)
      (parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R)) volume := hint.abs
  have hmono : (∫ v in multiplierHeatShellSet z r j, |G v|) ≤
      ∫ v in parabolicStrip z.1 (z.2 + (2 * R) ^ 2) (4 * R) (4 * R), |G v| := by
    refine setIntegral_mono_set habs ?_ (Filter.Eventually.of_forall hincl)
    exact Filter.Eventually.of_forall fun v => abs_nonneg _
  refine hmono.trans (hbd.trans ?_)
  have hMnn : (0 : ℝ) ≤ (morreyNorm P θ G).toReal := ENNReal.toReal_nonneg
  refine mul_le_mul_of_nonneg_right ?_ hMnn
  have h4 : (4 * R) ^ (2 - 5 / θ : ℝ) ≤ 16 * R ^ (2 - 5 / θ : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hRpos.le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hRpos.le _)
    have hle : (4 : ℝ) ^ (2 - 5 / θ : ℝ) ≤ (4 : ℝ) ^ (2 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (0 : ℝ) ≤ 5 / θ := by positivity
      linarith only [this]
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hle
    norm_num at hle
    exact hle
  have hcube : (4 * R) ^ 3 = 64 * R ^ 3 := by ring
  have hsplit : R ^ 3 * R ^ (2 - 5 / θ : ℝ) = R ^ (5 - 5 / θ : ℝ) := by
    rw [show (R : ℝ) ^ 3 = R ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_add hRpos]
    congr 1
    push_cast
    ring
  have hrnn : (0 : ℝ) ≤ R ^ (2 - 5 / θ : ℝ) := Real.rpow_nonneg hRpos.le _
  calc C * (4 * R) ^ 3 * (4 * R) ^ (2 - 5 / θ : ℝ)
      = (C * (64 * R ^ 3)) * (4 * R) ^ (2 - 5 / θ : ℝ) := by rw [hcube]
    _ ≤ (C * (64 * R ^ 3)) * (16 * R ^ (2 - 5 / θ : ℝ)) := by
        refine mul_le_mul_of_nonneg_left h4 ?_
        have : (0 : ℝ) ≤ R ^ 3 := by positivity
        positivity
    _ = 1024 * C * (R ^ 3 * R ^ (2 - 5 / θ : ℝ)) := by ring
    _ = 1024 * C * R ^ (5 - 5 / θ : ℝ) := by rw [hsplit]
end CKN.Core.HeatPotential
