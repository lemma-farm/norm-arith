/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.RegularityStructures.Torus.KernelBoundsBasic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.Phi43.Mollifier
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Quantitative support of a rescaled periodised mollifier

The compact support of a mollifier gives a support box independent of the scale.  After parabolic
rescaling, every nonzero summand of the spatial periodisation lies in the corresponding box of
width `ε²` in time and `ε` in each spatial coordinate.  These are the support estimates used by
the uniform singular-kernel bounds.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
