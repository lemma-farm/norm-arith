/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.Mollifier
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic scaling of the mollifier

The rescaled mollifier has scale-independent total variation on Euclidean space.  This is the
Euclidean half of the uniform `L¹` estimate for its spatial periodisation.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
