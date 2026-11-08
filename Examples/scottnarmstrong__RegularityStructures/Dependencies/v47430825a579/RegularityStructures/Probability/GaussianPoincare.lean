/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.Poincare
public import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The one-dimensional Gaussian Poincare estimate

This module contains the Stein-solution proof of the one-dimensional Gaussian Poincare
inequality. The analytic hypotheses are written as ordinary regularity and integrability
arguments of the theorem; the inequality itself is not packaged as a proposition-valued target.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace RegularityStructures
end RegularityStructures
end
