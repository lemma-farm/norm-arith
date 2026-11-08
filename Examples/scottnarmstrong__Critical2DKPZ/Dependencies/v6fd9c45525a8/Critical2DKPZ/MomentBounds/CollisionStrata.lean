/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Definitions.Site
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.CollisionWords
public import Mathlib
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Replica partitions and the two collision-stratum conventions

A partition is its equivalence relation on the finite label set. LZ21 imposes
only equality inside blocks. CCR25 additionally separates distinct nonsingleton
blocks, while allowing singleton labels to coincide with all other coordinates.
-/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.MomentBounds
/-- A partition of the replica labels, represented by its equivalence relation. -/
abbrev ReplicaPartition (h : ℕ) := Setoid (Fin h)
end Critical2DKPZ.MomentBounds
