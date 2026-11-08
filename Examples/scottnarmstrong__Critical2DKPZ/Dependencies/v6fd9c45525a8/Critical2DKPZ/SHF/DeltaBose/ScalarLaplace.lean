/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The exact Laplace transform of the scalar collision density

Gamma integration in the time variable and Fubini give the logarithmic
resolvent `(log rate - θ)⁻¹`. This supplies the small damped collision factor
in the diagram-chain estimates.
-/
public section
open MeasureTheory Set
namespace Critical2DKPZ.DeltaBose
end Critical2DKPZ.DeltaBose
