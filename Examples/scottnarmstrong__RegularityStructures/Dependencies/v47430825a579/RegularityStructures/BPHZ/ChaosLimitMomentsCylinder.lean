/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.WhiteNoiseChaosMoments
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomials of finitely many values of a field that is a white-noise pairing

Let `ψ` be a random field such that every value `ψ(·, y)` is almost surely `W h_y` for a
square-integrable `h_y`. Then every polynomial of finitely many values `ψ(·, z_i)` is almost surely
a cylindrical polynomial of the white noise `W`, of the same total degree
(`exists_cylindrical_eval_ae`).

* `chaosPolyAt a P`: the one-variable polynomial `P` evaluated at the coordinate `X a`.
-/
@[expose] public noncomputable section
open MvPolynomial
namespace RegularityStructures
end RegularityStructures
end
public section
open MvPolynomial MeasureTheory
namespace RegularityStructures
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
end RegularityStructures
end
