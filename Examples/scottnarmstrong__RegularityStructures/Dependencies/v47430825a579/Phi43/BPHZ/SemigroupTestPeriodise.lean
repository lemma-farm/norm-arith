/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.SemigroupTestUnfold
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.CanonicalBridgeConvolution
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.ParabolicSemigroup
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Periodisation of the semigroup test function

Let `Q_t = parabolicSemigroup.kernel t` on `ℝ⁴`.  For a point `x ∈ ℝ⁴` the *periodised* kernel
`q^♯_t(x, ·) : ℝ × T³ → ℝ` is
`q^♯_t(x, u) = ∑_{k ∈ ℤ³} Q_t(x, (u₀, torusRep u' + k))`.
For a spatially `1`-periodic function `g(y) = G(proj y)` on `ℝ⁴`, with `proj y = (y₀, y' mod ℤ³)`,
`∫_{ℝ⁴} Q_t(x, y) g(y) dy = ∫_{ℝ × T³} q^♯_t(x, u) G(u) du`
(`integral_semigroup_kernel_mul_comp_proj`), with integrability of the right-hand integrand.

The proof unfolds the `ℝ³` integral over the torus slice by slice (`integral_eq_integral_torus_tsum`)
and gets the integrability of the periodised integrand from the `[0, ∞]`-valued unfolding
`lintegral_eq_lintegral_spaceTime_tsum`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
open scoped ENNReal
namespace RegularityStructures
end RegularityStructures
end
