/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.AnnealedNoiseBridge
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.MollifierL1
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianMoments
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianVector
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Annealed moments of torus test-function pairings

The parabolic test class is lifted to `SpaceTime` by the Ioc fundamental-domain representative. The
white-noise covariance identity then gives the uniform second moment. Higher even moments use the
one-dimensional Gaussian law of each pairing; the normalization identity is the standard Gaussian
scaling formula corresponding to [HS23, Definition 2.20 and Remark 2.22].
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace RegularityStructures
end RegularityStructures
end
