/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.Generator
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The 1D heat equations for the symbol kernels

For `t > 0`: `k_t = symKernel j t` is smooth, `k_t'' = -4π² C_2`, `k_t'''' = 16π⁴ C_4`, and
`∂_t k_t = -C_{2j}`. Hence
`∂_t g_t = (4π²)⁻¹ g_t''` (`j = 1`) and `∂_t k_t = -(16π⁴)⁻¹ k_t''''` (`j = 2`), i.e. the
coefficients `generatorTimeCoeff = (4π²)⁻¹` and `generatorSpaceCoeff = (16π⁴)⁻¹` of
`RegularityStructures.Analysis.Parabolic.Generator` are the correct ones for the normalisation
`symKernel j t b = ∫ exp(-t ξ^{2j}) cos(2π ξ b) dξ`.
-/
public section
open MeasureTheory Real
namespace RegularityStructures
open scoped ContDiff
end RegularityStructures
end
