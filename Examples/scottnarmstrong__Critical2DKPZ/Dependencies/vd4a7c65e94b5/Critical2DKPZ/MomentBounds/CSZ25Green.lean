/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.MomentBounds.CSZ25Profiles
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.SrwKernel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Green energies and localisation in CSZ25 Section 5 -/
@[expose] public noncomputable section
namespace Critical2DKPZ.MomentBounds
/-- The truncated Green function sums the even-time transition kernel up to the given horizon. -/
def truncatedGreen (L : ℕ) (z : Site) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, srwKernel (2 * n) z
/-- The Green energy `R_L(φ, φ)`, including both parity classes. -/
def greenEnergy (L : ℕ) (φ : Site → ℝ) : ℝ :=
  ∑' z, ∑' w, φ z * truncatedGreen L (z - w) * φ w
end Critical2DKPZ.MomentBounds
