/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianPoincareFinite
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Derivatives of the remaining-coordinate Gaussian slices

The induction removes the first coordinate.  This file packages the continuous-linear derivative
of the resulting affine insertion map and its norm bound.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
namespace RegularityStructures
end RegularityStructures
end
