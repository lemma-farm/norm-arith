/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.Character
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.Basic
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.SRW
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Walk.Fourier
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.RandomWalk.Port.Site
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Fourier representation of the simple random walk kernel

Orthogonality of torus characters and the nearest-neighbour recursion give the Fourier
representation; the cosine Taylor bound controls the characteristic function near zero. -/
@[expose] public section
namespace LatticeProb.LocalCLT
open MeasureTheory
noncomputable section
end
end LatticeProb.LocalCLT
end
