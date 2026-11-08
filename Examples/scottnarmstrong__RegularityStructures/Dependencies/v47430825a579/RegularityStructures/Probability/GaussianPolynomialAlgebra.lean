/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianPolynomial
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Algebra of explicit polynomial bounds

These elementary closure lemmas keep the polynomial-growth hypotheses visible while making the
many integrability arguments in the Stein proof modular.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace RegularityStructures
end RegularityStructures
end
