/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Definitions.HeatKernel
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.Definitions.SiteToPlane
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.GaussianFourier
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.SRW
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Gaussian normalization and parity bridges in dimension two

The product Gaussian at time `t` has coordinate variance `t/2`, hence equals
the heat kernel at time `t/2`. Graph distance has coordinate-sum parity.
-/
@[expose] public section
namespace Critical2DKPZ
end Critical2DKPZ
