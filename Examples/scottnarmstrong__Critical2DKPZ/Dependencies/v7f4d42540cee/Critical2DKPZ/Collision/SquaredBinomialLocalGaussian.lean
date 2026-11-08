/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.WalkTails.LogConcavity
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.WalkTails.SquaredBinomialMGF
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Int.Interval
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.WalkTails.SymmetricMaxAtom
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # A composition-uniform local Gaussian bound for squared-binomial laws -/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.Collision
open Critical2DKPZ.WalkTails
end Critical2DKPZ.Collision
end
