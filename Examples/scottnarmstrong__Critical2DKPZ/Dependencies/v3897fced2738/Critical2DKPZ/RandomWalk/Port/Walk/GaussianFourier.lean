/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Site
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Gaussian Fourier integrals

The complex Gaussian integral along any horizontal line equals the Gaussian density
at the integer frequency times `2π`. -/
@[expose] public section
open MeasureTheory
noncomputable section
namespace LatticeProb.ContinuousTime
end LatticeProb.ContinuousTime
end
