/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.Primitive
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.RenewalLaw
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Exact finite-horizon integrals after removal of damping

The discrete weighted integral is the cumulative renewal mass, including its atom at
zero. The corresponding continuum integral is the primitive of the scalar density.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace Critical2DKPZ.Renewal
end Critical2DKPZ.Renewal
end
