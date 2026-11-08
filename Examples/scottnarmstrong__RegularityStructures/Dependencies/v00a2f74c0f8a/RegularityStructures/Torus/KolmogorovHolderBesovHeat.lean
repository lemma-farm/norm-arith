/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.HeatKernelIntegral
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.HeatKernelRegularity
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.Torus.HolderBesov
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v00a2f74c0f8a.RegularityStructures.PDE.Semigroup
public import Mathlib.MeasureTheory.Integral.MeanInequalities
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Heat-kernel input for the Kolmogorov criterion

This file records the scale-uniform Gaussian estimate used by the spatial
Kolmogorov argument.  The periodisation and normalization are those of
`RegularityStructures.Torus.HeatKernelIntegral`; the resulting estimate is the
three-dimensional heat-kernel bound behind Hairer [Hai14, (2.1)--(2.3)].
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures
end RegularityStructures
end
