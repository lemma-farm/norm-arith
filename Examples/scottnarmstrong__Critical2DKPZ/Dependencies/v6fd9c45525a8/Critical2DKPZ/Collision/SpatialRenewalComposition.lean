/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Collision.SpatialRenewal
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomWalk.Port.Walk.SRWDecomp
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.RandomWalk.Port.Walk.SRWOneDim
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Polymer.PathComposition
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.WalkTails.LogConcavity
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Collision.SquaredBinomialLocalGaussian
public import Mathlib
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Composition formula for the spatial renewal profile -/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.Collision
open LatticeProb
open Critical2DKPZ.WalkTails
private theorem composition_zero_eq_ones (c : Composition 0) :
    c = Composition.ones 0 := by
  apply Composition.ext
  have hc : c.length = 0 := Nat.eq_zero_of_le_zero c.length_le
  have hl : c.blocks.length = 0 := by simp [hc]
  have hblocks : c.blocks = [] := List.length_eq_zero_iff.mp hl
  simp [Composition.ones_blocks, hblocks]
private instance compositionZeroUnique : Unique (Composition 0) where
  default := Composition.ones 0
  uniq := composition_zero_eq_ones
end Critical2DKPZ.Collision
end
