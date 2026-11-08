/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianWickBlocksFour
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianWickMonomialSpecial
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.Isserlis
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moment bounds for `:X_a³: X_b :X_c³: X_d` on a Gaussian vector

For a centred Gaussian vector `X` with covariance `C` whose diagonal is bounded by `D`, every
entry satisfies `|C i j| ≤ D`, the product `:X_a³: X_b :X_c³: X_d` is integrable, and
`E|:X_a³: X_b :X_c³: X_d| ≤ 42 D⁴`.  Integrability and the bound come from
`|p q| ≤ (p² + q²) / 2` together with the block formula `integral_wick_three_mul_X_mul_wick_three_mul_X`
at `(a, b, a, b)`.
-/
public section
open MeasureTheory
namespace RegularityStructures
namespace IsCentredGaussianVector
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}
end IsCentredGaussianVector
end RegularityStructures
end
