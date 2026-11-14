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
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Basic ====
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
def parabolicCylinder (x : Vec3) (t r : ℝ) : Set ParabolicPoint :=
  vec3Ball x r ×ˢ Ioc (t - r ^ 2) t

instance : MeasureSpace ParabolicPoint := inferInstanceAs (MeasureSpace (Vec3 × ℝ))

axiom volume_parabolicCylinder (x : Vec3) (t r : ℝ) :
    volume (parabolicCylinder x t r) =
      volume (vec3Ball x r) * ENNReal.ofReal (r ^ 2)

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Statements.Gamma ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
/-- The velocity cubic quantity γ from the manuscript, `eq:alpha-beta`. -/
noncomputable def gamma (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r ^ (-2 : ℝ) * (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal) ^ (1 / 3 : ℝ)
end CKN

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Core.Caccioppoli.I2 ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
axiom caccioppoli_I2_velocity_integral_identity
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hfin : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
      ENNReal.ofReal (ρ ^ 2 * gamma u z ρ ^ 3)
end CKN

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.BallDisplays ====
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

/-- The volume of the open Euclidean ball of radius `r` centred at any point of
`Vec3`, namely `(4π/3) r³`; this is `volume_vec3Ball_zero` together with
translation invariance of Lebesgue measure. -/
axiom volume_vec3Ball_eq (x : Vec3) (r : ℝ) :
    volume (vec3Ball x r) =
      ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)
end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_4c837f90f13de805dfdf_GammaTerms ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# The `γ`-form Caccioppoli terms

`paper/ckn.tex`, Lemma `lem:caccioppoli-gamma` (`eq:caccioppoli-gamma`), reruns
the proof of the Caccioppoli inequality `lem:caccioppoli` changing only the
bounds on the first two of the four error terms.  This file records those two
replacement bounds as standalone theorems about the same raw integrals that
`CKN.Core.Caccioppoli.RawI1` and `CKN.Core.Caccioppoli.RawI2Bound` bound.

* `I₁`: the test-function weight `|∂ₛφ + Δφ|` is bounded pointwise by
  `C r² ρ⁻⁵`, and `∬_{Q_ρ}|u|²` is estimated by Hölder with `1 = 2/3 + 1/3`,
  `∬_{Q_ρ}|u|² ≤ |Q_ρ|^{1/3} (∬_{Q_ρ}|u|³)^{2/3} = C ρ³ γ(ρ)²`.  Hence
  `I₁ ≤ C κ² γ(ρ)²` with `κ = r/ρ` (`caccioppoli_I1_gamma_heat_cutoff_raw_bound`).
* `I₂`: the Poincaré input is dropped; instead
  `||u|² − ⨍_{B_ρ}|u|²| |u| ≤ 2|u|³ + (⍊_{B_ρ}|u|²)^{3/2}` pointwise, the
  spatial average enters through the Jensen bound
  `⍊_{B_ρ}|u|² ≤ (⍊_{B_ρ}|u|³)^{2/3}`, and `∬_{Q_ρ}|u|³ = ρ² γ(ρ)³` gives
  `I₂ ≤ C κ⁻² γ(ρ)³` (`caccioppoli_I2_gamma_heat_cutoff_raw_bound`).

The remaining two terms `I₃`, `I₄` keep their proved bounds, so the conclusion
of `eq:caccioppoli-gamma` follows by the normalisation lemmas recorded here.
-/
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section
namespace CKN
/-! ## The two elementary estimates behind the replacement bounds -/
/-- Hölder's inequality on a measure space with conjugate exponents `3/2` and `3`
in the form used for `I₁`: the integral of a nonnegative function is bounded by
`(∫ A^{3/2})^{2/3}` times the `1/3` power of the total mass. -/
axiom caccioppoli_holder_l2_le_l3
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {A : α → ℝ≥0∞}
    (hA : AEMeasurable A μ) :
    (∫⁻ x, A x ∂μ) ≤
      (∫⁻ x, A x ^ (3 / 2 : ℝ) ∂μ) ^ (2 / 3 : ℝ) *
        (μ Set.univ) ^ (1 / 3 : ℝ)
/-- The `L²` estimate for the velocity in the `γ`-form Caccioppoli inequality:
Hölder's inequality on `Q_ρ` with `1 = 2/3 + 1/3` combined with
`∬_{Q_ρ}|u|³ = ρ² γ(ρ)³` gives
`∬_{Q_ρ}|u|² ≤ |Q_ρ|^{1/3} (∬_{Q_ρ}|u|³)^{2/3} = (4π/3)^{1/3} ρ³ γ(ρ)²`. -/
theorem caccioppoli_velocity_l2_gamma_bound
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≠ ∞)
    (hA : AEMeasurable (fun w =>
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ))) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ 3 *
        gamma u (x₀, t₀) ρ ^ 2) := by
  let A : ParabolicPoint → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (2 : ℝ)
  have hAg : ∀ w, A w ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) := by
    intro w
    dsimp only [A]
    rw [← ENNReal.rpow_mul]
    rw [show (2 : ℝ) * (3 / 2) = 3 by norm_num]
  have hγ : 0 ≤ gamma u (x₀, t₀) ρ := by unfold gamma; positivity
  have hhold := caccioppoli_holder_l2_le_l3
    (μ := volume.restrict (parabolicCylinder x₀ t₀ ρ)) hA
  have hid := caccioppoli_I2_velocity_integral_identity
    (u := u) (z := (x₀, t₀)) (ρ := ρ) hρ hvelocity
  have hvol : (volume.restrict (parabolicCylinder x₀ t₀ ρ)) Set.univ =
      ENNReal.ofReal ((Real.pi * 4 / 3) * ρ ^ 5) := by
    rw [Measure.restrict_apply_univ]
    have hπ : 0 ≤ Real.pi * 4 / 3 := by positivity
    have hρ3 : 0 ≤ ρ ^ 3 := by positivity
    rw [volume_parabolicCylinder, volume_vec3Ball_eq]
    rw [← ENNReal.ofReal_pow hρ.le]
    rw [← ENNReal.ofReal_mul hρ3, ← ENNReal.ofReal_mul (mul_nonneg hρ3 hπ)]
    congr 1
    ring
  have hpow1 : (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) =
      ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 := by
    have hρpart : (ρ ^ 2) ^ (2 / 3 : ℝ) = ρ ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
      norm_num
    have hγpart : (gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) =
        gamma u (x₀, t₀) ρ ^ 2 := by
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hγ]
      norm_num
    calc
      (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ)
          = (ρ ^ 2) ^ (2 / 3 : ℝ) * (gamma u (x₀, t₀) ρ ^ 3) ^ (2 / 3 : ℝ) :=
            Real.mul_rpow (by positivity) (by positivity)
      _ = ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 := by rw [hρpart, hγpart]
  have hpow2 : ((Real.pi * 4 / 3) * ρ ^ 5) ^ (1 / 3 : ℝ) =
      (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) := by
    have hπ : 0 ≤ Real.pi * 4 / 3 := by positivity
    have hρ5 : 0 ≤ ρ ^ 5 := by positivity
    have hρpart : (ρ ^ 5) ^ (1 / 3 : ℝ) = ρ ^ (5 / 3 : ℝ) := by
      rw [← Real.rpow_natCast ρ 5, ← Real.rpow_mul hρ.le]
      norm_num
    calc
      ((Real.pi * 4 / 3) * ρ ^ 5) ^ (1 / 3 : ℝ)
          = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * (ρ ^ 5) ^ (1 / 3 : ℝ) :=
            Real.mul_rpow hπ hρ5
      _ = (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) := by rw [hρpart]
  calc
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ, A w)
        ≤ (∫⁻ w in parabolicCylinder x₀ t₀ ρ, A w ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) *
            (volume.restrict (parabolicCylinder x₀ t₀ ρ) Set.univ) ^
              (1 / 3 : ℝ) := hhold
    _ = (ENNReal.ofReal (ρ ^ 2 * gamma u (x₀, t₀) ρ ^ 3)) ^ (2 / 3 : ℝ) *
          (ENNReal.ofReal ((Real.pi * 4 / 3) * ρ ^ 5)) ^ (1 / 3 : ℝ) := by
        rw [lintegral_congr fun w => hAg w, hid, hvol]
    _ = ENNReal.ofReal ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ 3 *
          gamma u (x₀, t₀) ρ ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          hpow1, hpow2,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hρ.le _)
            (sq_nonneg _))]
        apply congrArg ENNReal.ofReal
        have hρadd : ρ ^ (4 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ) = ρ ^ 3 := by
          rw [← Real.rpow_add hρ]
          rw [show (4 : ℝ) / 3 + 5 / 3 = 3 by norm_num]
          simp
        calc
          ρ ^ (4 / 3 : ℝ) * gamma u (x₀, t₀) ρ ^ 2 *
              ((Real.pi * 4 / 3) ^ (1 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ)) =
              (Real.pi * 4 / 3) ^ (1 / 3 : ℝ) *
                (ρ ^ (4 / 3 : ℝ) * ρ ^ (5 / 3 : ℝ)) *
                  gamma u (x₀, t₀) ρ ^ 2 := by ring
          _ = _ := by rw [hρadd]
/-! ## The `I₁` replacement bound -/
end CKN
