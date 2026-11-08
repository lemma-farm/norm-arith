/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v634e0d8f16c1.Phi43.Mollifier
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v634e0d8f16c1.RegularityStructures.Torus.HeatKernelFacts
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Elementary support facts for the periodised mollifier

The compact support in the time coordinate survives parabolic rescaling and spatial
periodisation. These are the support facts about the periodised mollifier `ρ_ε^♯` of Definition 2.3; smoothness and
boundedness of the infinite spatial sum require the corresponding locally finite-series argument.
-/
public section
open MeasureTheory Set
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
