-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Scalar bookkeeping for §2.2. The flow and interpolation lemmas below
are algebraic consequences of scalar estimates, not proofs of PDE/ODE estimates. -/
@[expose] public section
noncomputable section
open scoped BigOperators
open Finset
namespace AVenhance.Infra.Construction
end AVenhance.Infra.Construction
