/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.Generator
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.TestFunction
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Scaling, support and size of the generator on rescaled test functions

For `φ ∈ B^4` and the rescaled `φ^c_z` we show that `L φ^c_z = c⁻⁴ (L φ)^c_z`
(`parabolicGenerator_rescaledTestFunction`), that `L` preserves the support condition, that
`|L φ| ≤ (4π²)⁻¹ + 3 (16π⁴)⁻¹`, and the `L¹` bounds `∫ |φ^c_z| ≤ 16`,
`∫ |L φ^c_z| ≤ 16 (…) c^{-4}`. These supply the test-function hypotheses of
`RegularisingSemigroup.abs_pairing_le` for `φ^c_z` and `L φ^c_z` (order `ℓ = 4`).
-/
public section
namespace RegularityStructures
open MeasureTheory
end RegularityStructures
end
