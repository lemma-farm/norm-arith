/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.CanonicalBridgePeriodise
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Torus.HeatKernelFacts
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Unfolding of nonnegative integrals onto the torus

For a measurable `H : ℝ³ → [0, ∞]`,
`∫⁻_{ℝ³} H = ∫⁻_{T³} ∑_{k ∈ ℤ³} H (torusRep u + k) du`
(`lintegral_eq_lintegral_torus_tsum`), and, for `H : ℝ × ℝ³ → [0, ∞]`, the same identity on
`ℝ × T³` with the time variable carried along (`lintegral_eq_lintegral_spaceTime_tsum`).

This is the `[0, ∞]`-valued companion of `integral_eq_integral_torus_tsum`; unlike the real
version it needs no integrability and yields the integrability of the periodised sum.
-/
public section
open MeasureTheory Set
open scoped ENNReal
namespace RegularityStructures.Phi43
open RegularityStructures
end RegularityStructures.Phi43
end
