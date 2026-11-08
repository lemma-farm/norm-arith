-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.PositiveCutoff
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.LimitPassage
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Time-tested finite Galerkin equation

The measurable-coefficient ODE yields the weak equation against a fixed finite Fourier test with
an arbitrary smooth time factor vanishing at the terminal time. This is the finite test identity
used before passing to the space-time weak limit.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
open scoped Topology RealInnerProductSpace
namespace AVenhance.Infra.Parabolic.FourierGalerkin
end AVenhance.Infra.Parabolic.FourierGalerkin
end
