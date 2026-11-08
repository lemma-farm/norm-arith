/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.RandomFieldFubini
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.SpaceTimeMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# A double Fubini identity for products of two kernel integrals

Let `Y₁, Y₃` be jointly measurable random fields and `A, B` random variables, and let
`g₁, g₃ ∈ L¹(SpaceTime)`.  If `E|Y₁(w) A Y₃(w') B| ≤ M` uniformly in `(w, w')` and each
`Y₁(w) A Y₃(w') B` is integrable, then
`E[(∫ g₁ Y₁) A ((∫ g₃ Y₃) B)] = ∫∫ g₁(w) g₃(w') E[Y₁(w) A Y₃(w') B] dw dw'`
and the integrand on the right is integrable on `SpaceTime × SpaceTime`.  This is the Fubini step
in the covariance of the tree `I(Ψ²) Ψ²` [Hai14, (10.39)-(10.42)].
-/
public section
open MeasureTheory
namespace RegularityStructures.Phi43
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
end RegularityStructures.Phi43
end
