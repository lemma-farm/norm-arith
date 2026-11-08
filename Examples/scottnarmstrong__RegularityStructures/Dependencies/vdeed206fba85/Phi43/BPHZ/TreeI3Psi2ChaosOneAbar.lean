/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2ChaosOneSplit
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.KernelCalculusRenorm
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Bound for the renormalised convolution `Ā`

`L = K Q²` is of order `-5`, hence (on its support `s ≤ 2`) also of order `-(5+δ)`, and
Lemma 10.16 of [Hai14] (`abs_integral_mul_sub_le`, with `a₁ = 5 + δ`, `a₂ = 3`) gives
`|Ā(x)| ≤ C s(x)^(-(3+δ))`, with `C` depending only on `B, δ`.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
