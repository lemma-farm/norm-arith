/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Analysis.Lattice.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Sampling each lattice cell at its representative gives a measurable map that converges pointwise to the identity as the mesh tends to zero. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Critical2DKPZ
/-- The continuum location of the lattice site at diffusive scale `N`. -/
def latticeRepresentative (N : ℕ) (z : Site) : Plane :=
  (Real.sqrt (N / 2))⁻¹ • siteToPlane z
/-- Each point is mapped to the representative of its nearest-even-lattice cell. -/
def cellSample (N : ℕ) (x : Plane) : Plane := latticeRepresentative N (latticePoint N x)
theorem dist_cellSample_le {N : ℕ} (hN : 0 < N) (x : Plane) :
    dist (cellSample N x) x ≤ (Real.sqrt (N / 2))⁻¹ := by
  rw [dist_comm, dist_eq_norm]
  exact norm_sub_latticePoint_le hN x
end Critical2DKPZ
end
