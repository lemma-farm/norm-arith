/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.RegularityStructures.Torus.HeatKernelRegularity
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.RegularityStructures.Probability.SpaceTimeMeasure
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Integrability of the massive heat kernel

The nonnegative space-time kernel has mass one: the spatial mass is the Gaussian normalization and
the remaining time integral is the exponential integral on `(0, ∞)`.
-/
@[expose] public noncomputable section
open MeasureTheory Real Set
namespace RegularityStructures
end RegularityStructures
end
