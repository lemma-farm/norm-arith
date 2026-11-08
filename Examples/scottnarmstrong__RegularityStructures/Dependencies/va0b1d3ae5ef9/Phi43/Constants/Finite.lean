/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.Constants
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.ClassicalSolution.PeriodiseRegularity
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.RegularityStructures.Torus.HeatKernelIntegrability
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Finiteness of the regularised constants

This is item (W3) of Lemma 4.1 of the statement.  The periodised mollifier is bounded and supported
in a compact time strip, so its translates are square-integrable.  The remaining assertions are
obtained from the integrable massive heat kernel, bounded convolution estimates, and the same
`L¹`--`L∞` argument for the covariance.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
namespace Phi43
end Phi43
end RegularityStructures
end
