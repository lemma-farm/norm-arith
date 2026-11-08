/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.Renewal.Sequence
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Truncated increment probabilities and the CSZ19a normalization dictionary

For positive steps, replacing the weights `σ r(n)` by the normalized increment law `r(n)/R_N`
and the fugacity `λ = σ R_N` leaves all renewal masses unchanged up to the cutoff. Here `σ`
denotes the variance `σ_N²`, rather than its square root. The unit atom at zero is included.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace Critical2DKPZ.Renewal
/-- The sum of the renewal step weights through the cutoff. -/
def cutoffMass (w : ℕ → ℝ) (N : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 N, w r
end Critical2DKPZ.Renewal
end
