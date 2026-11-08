-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Nested finite real Fourier spaces

This module transfers a coefficient vector from a cutoff into any larger symmetric cutoff. Both its
scalar synthesis and its gradient synthesis are preserved. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace AVenhance.Infra.Parabolic.FourierGalerkin
end AVenhance.Infra.Parabolic.FourierGalerkin
end
