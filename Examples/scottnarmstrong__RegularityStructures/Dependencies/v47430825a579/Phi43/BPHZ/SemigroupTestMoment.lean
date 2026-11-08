/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.SemigroupTestPeriodise
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Torus.KernelBoundsBasic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.ChaosReductionIntegralSupport
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.Moments
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moments of the periodised semigroup kernel

For `t > 0`, `r ≥ 0` and the periodised kernel `q^♯_t(x, ·)` on `ℝ × T³`,
`∫ |q^♯_t(x, u)| s(u - proj x)^r du ≤ M_r t^(r/4)`
(`integral_abs_semigroupPeriodised_mul_le`), with `M_r = parabolicMomentConst r` the moment
constant of `parabolicSemigroup`.  The torus size is dominated by the parabolic size of any lift,
`s(proj d) ≤ ‖d‖_𝔰` (`torusParabolicSize_spaceTimeProj_le`), so the `[0, ∞]`-valued unfolding turns
the periodised moment into the moment of `Q_t(x, ·)` on `ℝ⁴`.
-/
public section
open MeasureTheory
open scoped ENNReal
namespace RegularityStructures
end RegularityStructures
end
