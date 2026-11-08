-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.WeakUniqueness.ScalarPath
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Integral paths for weak Fourier coefficients

Testing the weak equation by a spatial Fourier mode and a smooth time factor gives an
ordinary scalar weak equation. The scalar reconstruction lemma then identifies each coefficient
with its absolutely continuous forcing path.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped ContDiff
namespace AVenhance.Infra.Parabolic.WeakUniqueness
def weakModePairing (u : ℝ → Vec 2 → ℝ) (ψ : Vec 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube, u t x * ψ x
end AVenhance.Infra.Parabolic.WeakUniqueness
end
