/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.HeatKernel
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.Topology.Algebra.Order.Floor
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Elementary measurable and order facts for the torus heat kernels

This module records the properties of the heat kernels (2.1)--(2.2) of the statement that follow
directly from the definitions. The fundamental-domain normalization and the locally uniform
Gaussian-series estimates are proved in `RegularityStructures.Torus.HeatKernelIntegral`.
-/
public section
open MeasureTheory Real Set
namespace RegularityStructures
end RegularityStructures
end
