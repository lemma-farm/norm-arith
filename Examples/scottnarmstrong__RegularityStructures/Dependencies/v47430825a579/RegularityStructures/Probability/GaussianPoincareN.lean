/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianPoincareSlices
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianLaw
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
/-!
# The finite-dimensional Gaussian Poincare inequality

This is the genuine product-Gaussian tensorisation of the one-dimensional Stein inequality.  All
polynomial-growth and `L²` hypotheses are explicit.  The proof follows the product decomposition
of the standard Gaussian and the coordinate split at `0`; this is the finite-dimensional spectral
gap input in Hairer--Steele, Definition 2.20 and Remark 2.22.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace RegularityStructures
end RegularityStructures
end
