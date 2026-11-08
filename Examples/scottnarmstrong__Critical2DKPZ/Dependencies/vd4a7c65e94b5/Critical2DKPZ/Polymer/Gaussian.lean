/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.DisorderLaw
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Finite linear combinations of independent standard Gaussian disorder coordinates have explicitly computable exponential moments. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Critical2DKPZ.Polymer
end Critical2DKPZ.Polymer
