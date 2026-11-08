-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.GalerkinEvolution
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Energy estimates for a finite family of coupled derivative paths. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Topology
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVenhance.Infra.Classical
variable {ι E G : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
end AVenhance.Infra.Classical
end
