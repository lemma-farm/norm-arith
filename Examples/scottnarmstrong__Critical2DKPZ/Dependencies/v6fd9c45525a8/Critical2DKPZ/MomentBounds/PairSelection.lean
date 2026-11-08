/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.MomentBounds.CollisionStrata
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Reduction of admissible partitions to two distinct collision pairs

Equal coarser partitions are allowed. Only the common single-pair partition is
excluded. This supplies the reduction implicit in the LZ21 lattice proof.
-/
@[expose] public section
namespace Critical2DKPZ.MomentBounds
instance finite_replicaPartition (h : ℕ) : Finite (ReplicaPartition h) := by
  classical
  apply Finite.of_injective (fun I : ReplicaPartition h => I.r)
  intro I J he
  exact Setoid.ext fun i j => Iff.of_eq (congrFun (congrFun he i) j)
noncomputable instance fintype_replicaPartition (h : ℕ) : Fintype (ReplicaPartition h) :=
  Fintype.ofFinite _
end Critical2DKPZ.MomentBounds
