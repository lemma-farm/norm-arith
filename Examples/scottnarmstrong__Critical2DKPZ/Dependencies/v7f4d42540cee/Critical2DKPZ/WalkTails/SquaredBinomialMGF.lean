/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.WalkTails.Hypergeometric
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.SRWOneDim
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.S1Gauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Sub-Gaussian bounds for squared-binomial walk increments

The squared-binomial law is the one-dimensional collision-increment law
`q_m(x)^2 / q_{2m}(0)`.  Its point masses are bounded by three times those of
the ordinary simple walk.  Symmetry lets this comparison be applied to
`cosh(t x) - 1`, which removes any multiplicative prefactor from the resulting
exponential-moment bound.
-/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.WalkTails
open Finset LatticeProb
end Critical2DKPZ.WalkTails
end
