/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.PointToPoint
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.PointToPlane
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.ProfileP2Fun
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.SmoothedP2Plane
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.SrwKernel
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Finite polymer path weights include disorder at times `a+1,…,a+n`, as in equation (1.3), and yield measurable partition functions supported on reachable endpoints. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Critical2DKPZ.Polymer
/-- The Boltzmann weight of a fixed walk, excluding its initial disorder slice. -/
def pathWeight (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) : ℝ :=
  Real.exp (∑ j ∈ Finset.Icc 1 n,
    (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2))
theorem walkPosition_eq_start_add {n : ℕ} (w : Site)
    (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition w s j = w + walkPosition 0 s j := by
  simp only [walkPosition, zero_add]
end Critical2DKPZ.Polymer
