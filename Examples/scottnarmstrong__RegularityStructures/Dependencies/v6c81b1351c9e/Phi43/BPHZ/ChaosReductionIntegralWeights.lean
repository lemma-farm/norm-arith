/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v6c81b1351c9e.Phi43.BPHZ.KernelCalculusBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The λ-integral of the chaos reduction: pointwise reduction to non-positive exponents

For a real exponent `a`, a real `t ∈ [0, R]` satisfies `t^a ≤ R^(max a 0) t^(-(max (-a) 0))`, and
`t^(-p) ≤ 2^p t'^(-p)` when `t` and `t'` are comparable up to the factor `2` (the parabolic size of
`-z` is at most twice that of `z`).  With `|f| ≤ B 1_K`, `s(w - x) ≤ 3 lam` on `K`, this reduces the
integrands `|f y||f ȳ| s(y - x)^ζ s(y - ȳ)^e` and `|f y||f ȳ| s(ȳ - x)^ζ s(y - ȳ)^e` for arbitrary real
`ζ, e` to the non-positive-exponent integrand of `chaosDouble_bound`.
-/
public section
open MeasureTheory
namespace RegularityStructures
theorem chaosSize_flip (a b : SpaceTime) :
    torusParabolicSize (a - b) ≤ 2 * torusParabolicSize (b - a) := by
  have := torusParabolicSize_neg_le_two_mul (b - a)
  rwa [neg_sub] at this
end RegularityStructures
end
