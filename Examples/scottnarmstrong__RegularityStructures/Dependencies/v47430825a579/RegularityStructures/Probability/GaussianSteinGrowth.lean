/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianGrowthIntegrability
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomial control of the Gaussian Stein datum

The centred Gaussian density datum `(f - E f) φ` has both a finite Lebesgue integral and a
polynomial-times-Gaussian pointwise bound whenever `f` and its first derivative have the stated
polynomial growth.  This is the input that connects the explicit Stein construction to the tail
estimates in `GaussianTailBound.lean`.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace RegularityStructures
end RegularityStructures
end
