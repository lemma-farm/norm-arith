/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.MomentBounds.CSZ25Green
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Polymer.SummableCovariance
import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Lattice.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Summability and finite-time calculus of Green energies -/
@[expose] public noncomputable section
namespace Critical2DKPZ.MomentBounds
/-- The truncated Green function is nonnegative. -/
theorem truncatedGreen_nonneg (L : ℕ) (z : Site) : 0 ≤ truncatedGreen L z :=
  Finset.sum_nonneg fun n _ => srwKernel_nonneg (2 * n) z
end Critical2DKPZ.MomentBounds
