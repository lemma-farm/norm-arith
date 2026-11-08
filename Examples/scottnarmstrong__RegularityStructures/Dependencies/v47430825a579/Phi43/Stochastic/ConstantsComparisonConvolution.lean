/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonDefinitions
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonPeriodise
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Torus.KernelBoundsPeriodiseL1
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Torus.KernelBoundsConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.AnnealedNoiseBridge
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Convolution form of the Section 7 mollifications

The comparison of the constants uses the periodised mollifier as an approximate identity.  This
module records the exact convolution identities and the signed total-variation bound needed before
an `Lᵖ` estimate is applied.  No positivity of the mollifier is assumed.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.Phi43
theorem constantsComparison_hairerMollifiedKernel_eq_convolution
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ} :
    spaceTimeConvolution (periodise ρ ε) (hairerKernelTorus N) =
      hairerMollifiedKernel N ρ ε := by
  funext z
  apply integral_congr_ae
  filter_upwards [] with w
  change periodise ρ ε w * hairerKernelTorus N (z - w) =
    hairerKernelTorus N (z - w) * periodise ρ ε w
  ring
end RegularityStructures.Phi43
end
