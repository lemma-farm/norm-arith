-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v36644ef8c8d0.Hormander.D.Cutoffs
public import Mathlib.Topology.Algebra.Support
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open Set
namespace Hormander.E
variable {N : ℕ}
/-- A nested cutoff pair has ordered topological supports. -/
theorem cutoffPrecedes_tsupport_subset
    {η η' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hη : Hormander.D.cutoffPrecedes η η') : tsupport η ⊆ tsupport η' := by
  intro x hx
  have hplateau :=
    (Hormander.D.cutoffPrecedes_eventually_iff_interior η η').mp hη.2.2.2.2 hx
  have hvalue : x ∈ {y | η' y = 1} := interior_subset hplateau
  apply subset_tsupport
  apply Function.mem_support.mpr
  rw [hvalue]
  norm_num
end Hormander.E
