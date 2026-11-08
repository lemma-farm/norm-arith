/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.OUBackwardDerivative
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The time-dependent OU interpolation derivative

The outer backward-time generator cancels the spatial generator of the inner
observable. Bounds here are ordinary space-time regularity bounds; all
Gaussian integrability and generator identities are proved.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology
namespace Critical2DKPZ.Ehrhard
end Critical2DKPZ.Ehrhard
end
