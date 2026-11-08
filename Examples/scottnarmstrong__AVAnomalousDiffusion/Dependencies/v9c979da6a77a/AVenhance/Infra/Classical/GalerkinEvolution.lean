-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.ForcedGalerkin
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.GalerkinModeCalculus
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Linear coefficient transforms of forced finite-dimensional Galerkin paths. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Topology
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVenhance.Infra.Classical
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
end AVenhance.Infra.Classical
end
