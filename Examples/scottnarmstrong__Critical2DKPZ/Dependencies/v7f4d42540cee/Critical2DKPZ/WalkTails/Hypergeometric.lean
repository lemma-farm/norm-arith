/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.OneDim
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The squared-binomial walk law

The normalized squared-binomial weights form a hypergeometric law.
Through the increment `2j-m`, they describe the common endpoint of two independent simple walks
conditioned to have the same endpoint after `m` steps.
-/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.WalkTails
open Finset.Nat Finset.HasAntidiagonal
/-- The finite hypergeometric mass at `j`: the squared binomial law on
`{0, ..., m}`.  It is zero outside that interval. -/
def hypergeometricWeight (m j : ℕ) : ℝ :=
  ((Nat.choose m j : ℝ) ^ 2) / (Nat.choose (2 * m) m : ℝ)
/-- The denominator in the squared-binomial law is positive. -/
theorem hypergeometric_denominator_pos (m : ℕ) :
    0 < (Nat.choose (2 * m) m : ℝ) := by
  exact_mod_cast (Nat.choose_pos (by omega : m ≤ 2 * m))
end Critical2DKPZ.WalkTails
end
