/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3Psi2ChaosOneSplit
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3PsiLeaves
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Convolution estimates for the absolute value of the kernel `J`

* `integral_swap_nonneg`: Tonelli for nonnegative functions in terms of Bochner integrals;
* `abs_J_mul_J_le`: `∫ |J(w - y)| |J(w' - y)| dy ≤ C B² s(w - w')^(-1)`;
* `power_mul_abs_J_le`: `∫ s(c - y)^(-a) |J(w - y)| dy ≤ C B s(c - w)^(2-a)` for `a ∈ (2, 5)`.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
