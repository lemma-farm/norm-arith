/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Constants.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.TestFunction
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Uniform L¹ control of a periodised mollifier

The spatial periodisation is controlled by unfolding the torus into a unit fundamental cell and
then partitioning the universal cover into integer translates.  The parabolic rescaling preserves
the L¹ norm, which is the deterministic input for a uniform Young estimate on mollified tests.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
