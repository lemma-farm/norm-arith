module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Gaussian.Poincare ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong

Ported from RegularityStructures-dev, commit 852e51c64f977a7cdd3eacab66e0188bc0ed75a2.
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Finite-dimensional standard Gaussian integration by parts uses coordinate derivatives and polynomial growth bounds (Hairer–Steele, Definition 2.20 and Remark 2.22). -/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace Critical2DKPZ.Gaussian
/-- The product standard Gaussian measure on `(Fin n → ℝ)`. -/
def standardGaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- The `i`th coordinate derivative, written using the coordinate direction in `ℝⁿ`. -/
def coordinateDerivative {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

end Critical2DKPZ.Gaussian
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.GaussianHeat ====
public section
/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott N. Armstrong

Ported from ASDExplicitGamma-dev, commit 2c9673f0bcca8062b441989bdc56f87b38715bb8.
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite-dimensional Gaussian heat flow

The heat flow is the Gaussian average of a translated observable. Its generator is one half of
the Euclidean Laplacian, as follows from Gaussian integration by parts.
-/
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open Filter
open Set
open scoped Topology
open scoped ENNReal NNReal
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)
namespace Critical2DKPZ.Ehrhard
/-- A `C²` function and its first and second coordinate derivatives obey one polynomial bound. -/
def HasPolynomiallyBoundedSecondCoordinateDerivatives {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 2 F ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
    (∀ x, |F x| ≤ C * (1 + ‖x‖) ^ d) ∧
    (∀ i x, |coordinateDerivative F i x| ≤ C * (1 + ‖x‖) ^ d) ∧
    ∀ i j x, |coordinateDerivative (coordinateDerivative F i) j x| ≤
      C * (1 + ‖x‖) ^ d

end Critical2DKPZ.Ehrhard

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.OrnsteinUhlenbeck ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ornstein–Uhlenbeck Gaussian averages

The operator is defined by its Gaussian integral. Time differentiation follows
from the proved Gaussian bridge derivative after the change of parameter
`r = exp(-2*t)`. Only positive times are used in the differential identities.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology
namespace Critical2DKPZ.Ehrhard
/-- The standard finite-dimensional OU operator, in its Gaussian integral form. -/
def ouAverage {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ z, F (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z)
    ∂standardGaussianMeasure n

end Critical2DKPZ.Ehrhard
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.OUGenerator ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The generator identity for Ornstein–Uhlenbeck averages -/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology
namespace Critical2DKPZ.Ehrhard
/-- The standard OU generator `ΔF - x·∇F`. -/
def ouGenerator {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i, coordinateDerivative (coordinateDerivative F i) i x) - fderiv ℝ F x x

end Critical2DKPZ.Ehrhard
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_3622fd6360a7c3441ee5_OUInitialContinuity ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Uniform preservation of an initial gap under small OU smoothing -/
@[expose] public noncomputable section
open Set
namespace Critical2DKPZ.Ehrhard
set_option linter.unusedVariables false in
/-- A uniform generator bound controls the change of an Ornstein–Uhlenbeck average by elapsed time. -/
theorem abs_ouAverage_sub_le_generator_bound {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) {B M : ℝ}
    (hbound : ∀ z, |F z| ≤ B) (hgen : ∀ z, |ouGenerator F z| ≤ M)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) 
    (h_Critical2DKPZ_Ehrhard_abs_ouAverage_le : ∀ {n : ℕ} {F : (Fin n → ℝ) → ℝ} {B : ℝ},
      (∀ (y : Fin n → ℝ), |F y| ≤ B) →
        ∀ (x : Fin n → ℝ) (t : ℝ), |Critical2DKPZ.Ehrhard.ouAverage F x t| ≤ B)
    (h_Critical2DKPZ_Ehrhard_continuous_ouAverage_time : ∀ {n : ℕ} {F : (Fin n → ℝ) → ℝ},
      Continuous F →
        ∀ {B : ℝ},
          (∀ (z : Fin n → ℝ), |F z| ≤ B) →
            ∀ (x : Fin n → ℝ), Continuous (Critical2DKPZ.Ehrhard.ouAverage F x))
    (h_Critical2DKPZ_Ehrhard_ouAverage_zero : ∀ {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), Critical2DKPZ.Ehrhard.ouAverage F x 0 = F x)
    (h_Critical2DKPZ_Ehrhard_hasDerivAt_ouAverage_generator : ∀ {n : ℕ} {F : (Fin n → ℝ) → ℝ},
      Critical2DKPZ.Ehrhard.HasPolynomiallyBoundedSecondCoordinateDerivatives F →
        ∀ (x : Fin n → ℝ) {t : ℝ},
          0 < t →
            HasDerivAt (Critical2DKPZ.Ehrhard.ouAverage F x)
              (Critical2DKPZ.Ehrhard.ouAverage (Critical2DKPZ.Ehrhard.ouGenerator F) x t) t)
    : |ouAverage F x t - F x| ≤ M * t := by
  have hcont := (h_Critical2DKPZ_Ehrhard_continuous_ouAverage_time hF.1.continuous hbound x).continuousOn (s := Icc 0 t)
  have hder (s) (hs : s ∈ interior (Icc (0 : ℝ) t)) :
      HasDerivAt (ouAverage F x) (ouAverage (ouGenerator F) x s) s := by
    rw [interior_Icc] at hs
    exact h_Critical2DKPZ_Ehrhard_hasDerivAt_ouAverage_generator hF x hs.1
  have hdiff : DifferentiableOn ℝ (ouAverage F x) (interior (Icc (0 : ℝ) t)) :=
    fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
  have hderbound (s) (hs : s ∈ interior (Icc (0 : ℝ) t)) : |deriv (ouAverage F x) s| ≤ M := by
    rw [(hder s hs).deriv]
    exact h_Critical2DKPZ_Ehrhard_abs_ouAverage_le hgen x s
  have hhi := (convex_Icc (0 : ℝ) t).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun s hs => (abs_le.mp (hderbound s hs)).2) 0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  have hlo := (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun s hs => (abs_le.mp (hderbound s hs)).1) 0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  rw [h_Critical2DKPZ_Ehrhard_ouAverage_zero, sub_zero] at hlo hhi
  exact abs_le.mpr ⟨by linarith only [hlo], hhi⟩
end Critical2DKPZ.Ehrhard
end
