/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.SpaceTimeMeasure
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.WhiteNoise
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Gaussian pairings and the universal-cover test-function estimate

The white-noise definition identifies the second moment of `W g` with the squared `L²` norm of
`g`.  The rescaled test functions used in Hairer [Hai14, (2.13)] have a uniform `L¹` bound;
their pointwise bound therefore gives the expected `λ⁻⁵` estimate on the universal cover.

The torus-valued pairing with a rescaled test function is deliberately not introduced here:
`rescaledTestFunction` lives on `ParabolicSpace`, whereas `IsWhiteNoise` indexes functions on
`SpaceTime`.  A separate periodisation/lift is needed before these two estimates can be joined.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
namespace RegularityStructures
end RegularityStructures
end
