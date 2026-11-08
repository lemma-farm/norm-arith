/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vcf8a52064a9c.Phi43.Mollifier
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vcf8a52064a9c.RegularityStructures.Torus.HeatKernel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The renormalisation constants

The constants of Definition 2.5 of the statement:
`G_ε = G * ρ_ε^♯`, `Q_ε(z) = ∫ G_ε(z + w) G_ε(w) dw`,
`C₁^ε = ∫ G_ε²` and `C₂^ε = 2 ∫ G Q_ε²`. They are the constants of [Hai14, (10.33) and (10.41)],
with Hairer's truncated heat kernel replaced by the massive heat kernel `G`.

Source: the statement, Definition 2.5; [Hai14, (10.33), (10.41)].
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
