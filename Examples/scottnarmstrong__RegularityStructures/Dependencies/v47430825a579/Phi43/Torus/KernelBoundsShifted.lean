/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Torus.KernelBoundsLocal
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.SpaceTimeMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Integrable shifted parabolic majorants

These are elementary consequences of the homogeneous dimension-five volume estimate.  They
package the two estimates used in the covariance convolution: a globally integrable sixth-power
majorant, and a locally integrable regularised cubic majorant.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
