-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.ODE.Linear
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Parabolic.FourierGalerkin.ODE
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Energy estimate for a finite Galerkin system

The finite weak-form matrix splits into transport and diffusion forms. The transport contribution
is bounded by `B ‖D u‖ ‖u‖`; Young's inequality absorbs one diffusion term and leaves a scalar
Grönwall coefficient `B² / κ`. The result below takes those two finite-dimensional form facts as
its interface, so the spatial mode calculus can establish them independently.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Topology RealInnerProductSpace
namespace AVenhance.Infra.Parabolic.FourierGalerkin
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end AVenhance.Infra.Parabolic.FourierGalerkin
end
