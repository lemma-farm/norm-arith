/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Structure.CanonicalKernelHairer
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonKernelLp
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.Support
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The Hairer kernel on `ℝ⁴` is integrable with compact support

This is the Euclidean input of the bridge between the concrete canonical data on
`ParabolicSpace = ℝ⁴` and the tree fields on `ℝ × T³`.  The kernel `hairerKernel N` is the sum of its
causal shells, each of which is a rescaling of a fixed smooth compactly supported function, so the
`L¹` norms of the shells are summable (geometric).  Consequently `hairerKernel N` is integrable, it
vanishes outside the unit parabolic ball, and its convolution with a continuous function exists.
-/
public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
end RegularityStructures.Phi43
end
