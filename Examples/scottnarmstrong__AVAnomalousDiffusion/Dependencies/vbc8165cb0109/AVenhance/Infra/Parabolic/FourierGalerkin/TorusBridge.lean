-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Torus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Statements.Roots.SpaceGrad
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Real-valued periodic integration by parts for Galerkin tests

This bridge specializes the landed complex torus-calculus theorem to the real gradient and
the open unit-cell carrier used by the parabolic weak formulation.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
namespace AVenhance.Infra.Parabolic.FourierGalerkin
def TorusBridge.closedCell : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
theorem TorusBridge.isCompact_closedCell : IsCompact TorusBridge.closedCell := by
  simpa [TorusBridge.closedCell] using (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
theorem TorusBridge.realToComplex_periodic {f : Vec 2 → ℝ}
    (hperiodic : AVenhance.IsZ2Periodic f) :
    AVenhance.Infra.Torus.IsZdPeriodic (AVenhance.Infra.Torus.realToComplex f) := by
  intro k x
  have h := (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2 hperiodic k x
  exact congrArg (fun y : ℝ => (y : ℂ)) h
end AVenhance.Infra.Parabolic.FourierGalerkin
end
