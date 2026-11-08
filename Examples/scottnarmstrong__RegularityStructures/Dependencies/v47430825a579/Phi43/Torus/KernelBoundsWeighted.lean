/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Torus.KernelBoundsCovariance
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Weighted parabolic volume estimates

The homogeneous dimension of `ℝ × T³` for the parabolic size is five.  This file
records the layer-cake estimate for the truncated kernel `|z|ₛ⁻⁶`, which is the
only non-algebraic input needed for the covariance convolution bound.
-/
@[expose] public noncomputable section
open MeasureTheory Set Metric
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
