/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong

Ported from RegularityStructures-dev, commit 852e51c64f977a7cdd3eacab66e0188bc0ed75a2.
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
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
instance isProbabilityMeasure_standardGaussianMeasure (n : ℕ) :
    IsProbabilityMeasure (standardGaussianMeasure n) := by
  unfold standardGaussianMeasure
  infer_instance
end Critical2DKPZ.Gaussian
end
