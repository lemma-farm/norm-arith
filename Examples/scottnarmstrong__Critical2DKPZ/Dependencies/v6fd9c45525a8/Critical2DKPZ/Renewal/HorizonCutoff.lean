/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.TiltedDensity
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.CompactTilting
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Compactified finite time horizons

A clipped logarithm removes exponential damping continuously on a fixed horizon.
The scalar renewal law gives zero mass to each positive-time boundary.
-/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Critical2DKPZ.Renewal
end Critical2DKPZ.Renewal
end
