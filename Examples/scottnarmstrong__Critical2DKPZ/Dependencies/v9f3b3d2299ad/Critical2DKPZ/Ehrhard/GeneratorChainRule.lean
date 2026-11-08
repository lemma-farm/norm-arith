/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.OUCommutation
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The second-order chain rule for the OU generator

The outer function needs regularity only at the range of the inner map. This
is essential for Gaussian quantiles, whose natural domain is the probability
box. The Hessian is always evaluated at the smoothed inputs.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)
namespace Critical2DKPZ.Ehrhard
end Critical2DKPZ.Ehrhard
end
