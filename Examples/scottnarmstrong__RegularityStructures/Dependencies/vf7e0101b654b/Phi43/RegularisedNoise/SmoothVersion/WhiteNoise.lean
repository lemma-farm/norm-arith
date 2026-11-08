/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vf7e0101b654b.RegularityStructures.Probability.GaussianVector
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vf7e0101b654b.RegularityStructures.Probability.SpaceTimeMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The L² isometry of an arbitrary white noise

The strengthened white-noise predicate supplies measurable Gaussian coordinates for every
square-integrable kernel.  The finite-dimensional covariance clause then gives the exact L²
isometry and the almost-sure identification of evaluations of equal kernels.  These are the
probabilistic identities used when a smooth Fourier series is compared with the original field.
-/
@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
