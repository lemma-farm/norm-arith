/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.RegularityStructures.Torus.HeatKernelIntegral
public import Mathlib.Analysis.Normed.Group.FunctionSeries
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Uniform Gaussian bounds for the torus heat kernel

The Gaussian series is controlled uniformly on the half-open fundamental cube.  This file contains
the summable majorant used to prove boundedness and continuity of the kernel.
-/
@[expose] public noncomputable section
open MeasureTheory Real Set
open scoped Topology
namespace RegularityStructures
end RegularityStructures
end
