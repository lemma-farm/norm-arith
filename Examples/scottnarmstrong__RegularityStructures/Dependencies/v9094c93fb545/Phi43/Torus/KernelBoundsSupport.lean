/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.RegularityStructures.Torus.KernelBoundsGeometry
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.Phi43.Torus.KernelBoundsMollifier
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.Phi43.Mollifier
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Parabolic support of a periodised mollifier

The support of the periodised rescaling is contained in a parabolic ball of radius `O(ε)`.  The
only quotient input is that the centered representative is the shortest coordinate representative
among all integer translates.
-/
@[expose] public noncomputable section
open Real Set
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
