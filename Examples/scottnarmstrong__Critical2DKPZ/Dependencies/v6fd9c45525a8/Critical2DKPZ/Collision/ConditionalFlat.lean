/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.SummableCovariance
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.BlockMeasurability
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Gaussian.TimeBlocks
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.ConstrainedReplica
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Conditional flat-terminal collision formula

Conditioning on the disorder through time `a` freezes a past-measurable initial profile and
integrates the independent future slab.  This file gives the finite-support version directly,
including the zero-mass signed case.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators
namespace Critical2DKPZ.Collision
open Critical2DKPZ.Polymer
end Critical2DKPZ.Collision
end
