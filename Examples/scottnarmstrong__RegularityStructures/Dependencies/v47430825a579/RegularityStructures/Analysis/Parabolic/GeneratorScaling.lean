/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.GeneratorScaling.Algebra
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Scaling, support and size of the generator on rescaled test functions

Facade: see `RegularityStructures.Analysis.Parabolic.GeneratorScaling.Algebra` (exact scaling
`L φ^c_z = c⁻⁴ (L φ)^c_z`, support, pointwise bound) and
`RegularityStructures.Analysis.Parabolic.GeneratorScaling.Integral` (volume of the unit ball, `L¹`
bounds and the packaged hypotheses for `RegularisingSemigroup.abs_pairing_le`).
-/
