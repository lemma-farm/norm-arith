/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2ChaosOneBasic
public import Mathlib.Analysis.Convolution
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Fubini identities for the chaos-`1` part of `I(Ψ³)Ψ²`

For an integrable `h` write `smear J h (y) = ∫ h(w) J(w - y) dw`.  With `Q(x) = ∫ J(x + w) J(w) dw`
and `J` bounded and integrable:

* `integral_smear_mul_smear`: `∫ smear h₁ · smear h₂ dy = ∫ h₁(w) ∫ h₂(w') Q(w - w') dw' dw`;
* `integral_smear_mul_J`: `∫ smear h (y) J(p - y) dy = ∫ h(w) Q(w - p) dw`.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
