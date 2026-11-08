/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianIBP
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
/-!
# Finite-dimensional Gaussian integration by parts and Poincare inequality

Points are functions `Fin n → ℝ`. The standard Gaussian measure is the product of the
one-dimensional measures `gaussianReal 0 1`. The growth and integrability hypotheses occur as
theorem arguments below; no theorem-shaped proposition is used in their place.

The identities here are the finite-dimensional Gaussian input corresponding to [HS23, Definition
2.20 and Remark 2.22].
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace RegularityStructures
/-- The product standard Gaussian measure on `(Fin n → ℝ)`. -/
def standardGaussianMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)
end RegularityStructures
end
