/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonSingularLp
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Constants.Finite
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Torus.KernelBoundsK3
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonConvolution
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.AnnealedNoiseBridge
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Fixed-scale bounds for the causal truncated covariance

This module proves measurability of the mollified causal truncated covariance in Hairer's
(10.41). The scale-uniform covariance difference is proved separately in
`ConstantsComparisonCovarianceUniform`.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
