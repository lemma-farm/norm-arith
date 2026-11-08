-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.FiniteProductWeakForm
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Weak limit passage on fixed Fourier tests

A fixed real Fourier test is embedded in every sufficiently large cutoff. The finite product-space
identities therefore pass to the synchronized weak product limits without changing their tests.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
end AVenhance.Infra.Parabolic.FourierGalerkin
end
