/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.Gaussian.Poincare
public import Mathlib.Probability.Independence.InfinitePi
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The product disorder law has Gaussian coordinate marginals and spatial symmetries. -/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
namespace Critical2DKPZ.Gaussian
end Critical2DKPZ.Gaussian
end
