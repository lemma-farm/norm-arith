/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.Torus.KernelBoundsPeriodiseL1
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.Constants.Finite
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Real-valued `L¹` bounds for the rescaled periodised mollifier

The fundamental-domain estimate for the periodisation is stated first for lower integrals.  This
file records the corresponding Bochner integral estimate, together with the scale invariance of
the Euclidean rescaling, in the form used by the singular convolution bounds.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
