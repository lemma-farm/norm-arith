/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianStein
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianSteinGrowth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomial growth of the explicit Gaussian Stein solution

The centered Gaussian datum has Gaussian tails.  Splitting the primitive at the origin and using
the zero-integral identity turns those tails into a polynomial bound for the Stein solution.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Real Set
namespace RegularityStructures
end RegularityStructures
end
