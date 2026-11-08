/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.RegularityStructures.Probability.WhiteNoise
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Mollifiers and regularised noise

A mollifier is a smooth compactly supported function `ρ` on `ℝ × ℝ³` with `∫ ρ = 1`. It is
rescaled parabolically, `ρ_ε(t, x) = ε⁻⁵ ρ(ε⁻² t, ε⁻¹ x)`, and periodised in space. A regularised
noise at scale `ε` is a version of `z ↦ W(ρ_ε^♯(z - ·))` that is smooth in `z` for every `ω`.

Source: the statement, Definitions 2.3 and 2.4.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
