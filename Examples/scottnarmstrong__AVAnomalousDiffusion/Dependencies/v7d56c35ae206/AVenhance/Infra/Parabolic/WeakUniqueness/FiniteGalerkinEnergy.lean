-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.WeakUniqueness.ModePath
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.WeakUniqueness.FiniteEnergy
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Classical.GalerkinModeCalculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.ODE.Linear.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Energy identity for finite Fourier coefficients of weak solutions

Each real Fourier coefficient satisfies a scalar integral equation. Applying the finite-path
energy identity coefficientwise and summing gives the exact energy identity for every Fourier
cutoff.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
namespace AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Parabolic.FourierGalerkin
/-- The finite vector of real Fourier coefficients of a weak path at time `t`. -/
def weakFourierCoefficientPath (N : ℕ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) :
    Coefficients (RealFourierDimension N) :=
  WithLp.toLp 2 (fun i => weakModePairing u
    (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) t)
theorem FiniteGalerkinEnergy.weakFourierMode_smooth (N : ℕ) (i : Fin (RealFourierDimension N)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) :=
  (realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm i)).of_le
    (by simp)
theorem FiniteGalerkinEnergy.weakFourierMode_periodic (N : ℕ) (i : Fin (RealFourierDimension N)) :
    AVenhance.IsZ2Periodic
      (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)) :=
  realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm i)
end AVenhance.Infra.Parabolic.WeakUniqueness
end
