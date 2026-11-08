-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.GalerkinResidualTail
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.GalerkinGenerator
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.GalerkinDerivative
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Classical.Commutator
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.FourierCalculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.FrozenBridge
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Cutoff tails of smooth real periodic residuals. -/
@[expose] public section
noncomputable section
open MeasureTheory
open Filter
open scoped Topology
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin
local instance classicalResidualMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalResidualMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalResidualProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Classical
theorem GalerkinResidual.continuous_spaceGrad_component {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) := by
  change Continuous (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
theorem classicalL2_norm_le_of_all_projection_bounds
    (v : ScalarTorusL2) {B : ℝ}
    (hproj : ∀ N, ‖realFourierProjectionCoefficients N v‖ ≤ B) :
    ‖v‖ ≤ B := by
  have hlim := tendsto_realFourierProjection v
  have hnorm : Tendsto
      (fun N => ‖realFourierScalarMap N (realFourierProjectionCoefficients N v)‖)
      atTop (𝓝 ‖v‖) := by
    exact (continuous_norm.continuousAt.tendsto).comp hlim
  apply le_of_tendsto hnorm
  filter_upwards with N
  simpa only [realFourierScalarMap_norm] using hproj N
/-- Uniform bounds for all scalar Fourier projections of each derivative component bound the
full Dirichlet energy of a smooth periodic function. -/
theorem classicalSmoothSource_gradient_energy_le_of_projection_bounds
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ 1 f)
    (hper : AVenhance.IsZ2Periodic f) {B : ℝ} (hB : 0 ≤ B)
    (hproj : ∀ i K,
      ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceGrad f x i))‖ ≤ B) :
    AVenhance.gradNormSq (AVenhance.spaceGrad f) ≤ 2 * B ^ 2 := by
  let g (i : Fin 2) : Vec 2 → ℝ := fun x => AVenhance.spaceGrad f x i
  let v (i : Fin 2) : ScalarTorusL2 :=
    (memLp_periodicToTorus_real (GalerkinResidual.continuous_spaceGrad_component hf i)
      (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).toLp
      (AVenhance.Infra.Torus.periodicToTorus (g i))
  have hvproj (i : Fin 2) (K : ℕ) :
      realFourierProjectionCoefficients K (v i) =
        modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
          (AVenhance.Infra.Torus.periodicToTorus (g i)) := by
    unfold realFourierProjectionCoefficients
    ext m
    simp only [modeProjectionCoefficients, PiLp.toLp_apply]
    apply integral_congr_ae
    filter_upwards [(memLp_periodicToTorus_real
      (GalerkinResidual.continuous_spaceGrad_component hf i)
      (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).coeFn_toLp] with x hx
    rw [hx]
  have hvbound (i : Fin 2) : ‖v i‖ ≤ B := by
    apply classicalL2_norm_le_of_all_projection_bounds
    intro K
    rw [hvproj]
    simpa [g] using hproj i K
  have hcomponent (i : Fin 2) :
      ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 ≤ B ^ 2 := by
    have hnorm := AVenhance.Infra.Parabolic.FourierGalerkin.l2_norm_sq_eq_integral_sq (v i)
    have hcell : (∫ x : Torus, ‖v i x‖ ^ 2) =
        ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 := by
      calc
        (∫ x : Torus, ‖v i x‖ ^ 2) =
            ∫ x : Torus,
              ‖AVenhance.Infra.Torus.periodicToTorus (g i) x‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [(memLp_periodicToTorus_real
            (GalerkinResidual.continuous_spaceGrad_component hf i)
            (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).coeFn_toLp]
            with x hx
          rw [show (v i) x =
            ((memLp_periodicToTorus_real
              (GalerkinResidual.continuous_spaceGrad_component hf i)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component hper i)).toLp
              (AVenhance.Infra.Torus.periodicToTorus (g i))) x by rfl, hx]
        _ = ∫ x : Torus,
            AVenhance.Infra.Torus.periodicToTorus (fun y : Vec 2 => (g i y) ^ 2) x := by
          apply integral_congr_ae
          filter_upwards with x
          simp [AVenhance.Infra.Torus.periodicToTorus]
        _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, (g i x) ^ 2 :=
          AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell _
        _ = ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 := by
          rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
    calc
      ∫ x in AVenhance.unitCube, (AVenhance.spaceGrad f x i) ^ 2 = ‖v i‖ ^ 2 := by
        rw [← hcell, ← hnorm]
      _ ≤ B ^ 2 := by nlinarith [hvbound i, norm_nonneg (v i), hB]
  have hgradIdent :
      (∑ i : Fin 2, ∫ x in AVenhance.unitCube,
        (AVenhance.spaceGrad f x i) ^ 2) =
        AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
    let fc : Vec 2 → ℂ := AVenhance.Infra.Torus.realToComplex f
    have hfc : ContDiff ℝ 1 fc := Complex.ofRealCLM.contDiff.comp hf
    have hsum := AVenhance.Infra.Torus.integral_unitCell_gradSq_eq_sum_coord hfc
    have hcoord (i : Fin 2) (x : Vec 2) :
        AVenhance.Infra.Torus.coordDeriv i fc x =
          (AVenhance.spaceGrad f x i : ℂ) :=
      AVenhance.Infra.Torus.coordDeriv_realToComplex hf i x
    calc
      (∑ i : Fin 2, ∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad f x i) ^ 2) =
          ∑ i : Fin 2, ∫ x in AVenhance.Infra.Torus.unitCell 2,
            ‖AVenhance.Infra.Torus.coordDeriv i fc x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
        apply setIntegral_congr_ae
          (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        filter_upwards with x _hx
        rw [hcoord]
        simp
      _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          ∑ i : Fin 2, ‖AVenhance.Infra.Torus.coordDeriv i fc x‖ ^ 2 := hsum
      _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          Homogenization.vecNormSq (AVenhance.spaceGrad f x) := by
        apply setIntegral_congr_ae
          (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        filter_upwards with x _hx
        simp [Homogenization.vecNormSq, Homogenization.vecDot, hcoord, pow_two]
      _ = ∫ x in AVenhance.unitCube,
          Homogenization.vecNormSq (AVenhance.spaceGrad f x) :=
        AVenhance.Infra.Torus.integral_unitCell_eq_unitCube _
      _ = AVenhance.gradNormSq (AVenhance.spaceGrad f) := rfl
  calc
    AVenhance.gradNormSq (AVenhance.spaceGrad f) =
        ∑ i : Fin 2, ∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad f x i) ^ 2 := hgradIdent.symm
    _ ≤ ∑ _i : Fin 2, B ^ 2 := Finset.sum_le_sum fun i hi => hcomponent i
    _ = 2 * B ^ 2 := by norm_num
end AVenhance.Infra.Classical
end
