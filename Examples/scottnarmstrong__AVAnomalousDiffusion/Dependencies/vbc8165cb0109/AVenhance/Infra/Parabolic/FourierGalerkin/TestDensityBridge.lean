-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarFourierDerivative
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Section5.TestDensity
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth periodic spatial tests from the real Fourier identities

The synchronized limit has a common full-measure set of times on which its weak spatial
derivative identity holds for every real Fourier mode. This module begins the density bridge from
those modes to the smooth periodic tests used by the solution predicate.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open AVenhance.Infra.Ergodic
open scoped RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance testDensityBridgeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance testDensityBridgeMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance testDensityBridgeProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance testDensityBridgeProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance avInfraParabolicFourierGalerkinTestDensityBridgeIsFiniteMeasure1 : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]
theorem bridge_continuous_integrable_cube {g : Vec 2 → ℝ}
    (hg : Continuous g) : IntegrableOn g AVenhance.unitCube := by
  have hcell := continuous_unitCell_integrable hg
  have hμ : (volume : Measure (Vec 2)).restrict
      (AVenhance.Infra.Torus.unitCell 2) =
      (volume : Measure (Vec 2)).restrict AVenhance.unitCube :=
    Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube
  change Integrable g ((volume : Measure (Vec 2)).restrict AVenhance.unitCube)
  rw [← hμ]
  exact hcell
theorem TestDensityBridge.frequencyBall_pairFrequency_iff (N : ℕ) (k : Fin 2 → ℤ) :
    k ∈ AVenhance.Infra.Ergodic.frequencyBall N ↔
      frequencyPair k ∈ symmetricFrequencyBox N := by
  rw [AVenhance.Infra.Ergodic.mem_frequencyBall]
  simp only [frequencyPair, symmetricFrequencyBox, Finset.mem_product,
    Finset.mem_Icc]
  constructor
  · intro hk
    have h0 : ‖(k 0 : ℝ)‖ ≤ ‖k‖ := norm_le_pi_norm k 0
    have h1 : ‖(k 1 : ℝ)‖ ≤ ‖k‖ := norm_le_pi_norm k 1
    have hcast0 : |k 0| ≤ (N : ℤ) := by
      have hreal : |(k 0 : ℝ)| ≤ (N : ℝ) := by
        simpa only [Real.norm_eq_abs] using h0.trans hk
      exact_mod_cast hreal
    have hcast1 : |k 1| ≤ (N : ℤ) := by
      have hreal : |(k 1 : ℝ)| ≤ (N : ℝ) := by
        simpa only [Real.norm_eq_abs] using h1.trans hk
      exact_mod_cast hreal
    exact ⟨abs_le.mp hcast0, abs_le.mp hcast1⟩
  · intro hk
    have hcoord : ∀ i : Fin 2, ‖(k i : ℝ)‖ ≤ (N : ℝ) := by
      intro i
      have habs : |k i| ≤ (N : ℤ) := by
        fin_cases i
        · exact abs_le.mpr hk.1
        · exact abs_le.mpr hk.2
      have hcast : |(k i : ℝ)| ≤ (N : ℝ) := by exact_mod_cast habs
      simpa only [Real.norm_eq_abs] using hcast
    exact (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (N : ℝ))).2 hcoord
theorem TestDensityBridge.frequencyPair_pairFrequency (p : ℤ × ℤ) :
    frequencyPair (pairFrequency p) = p := by
  rcases p with ⟨p₀, p₁⟩
  rfl
theorem TestDensityBridge.frequencyPair_injective {p q : Fin 2 → ℤ}
    (h : frequencyPair p = frequencyPair q) : p = q := by
  change (p 0, p 1) = (q 0, q 1) at h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  funext i
  fin_cases i
  · exact h0
  · exact h1
theorem TestDensityBridge.testFourierCutoff_eq_realFourierProjection_ambient
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) (N : ℕ) (x : Vec 2) :
    AVenhance.Infra.Section5.testFourierCutoff ψ N x =
      realFourierProjection N
        (AVenhance.Infra.Torus.periodicToTorus ψ)
        (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
  let a : (Fin 2 → ℤ) → ℂ :=
    fun k => AVenhance.Infra.Torus.smoothFourierCoeff
      (fun y => (ψ y : ℂ)) k
  have ha : ∀ k, a (-k) = star (a k) := by
    intro k
    dsimp [a]
    exact AVenhance.Infra.Ergodic.smoothFourierCoeff_real_neg k
  have hperiodicC : AVenhance.Infra.Torus.IsZdPeriodic
      (fun y => (ψ y : ℂ)) := by
    intro k y
    exact congrArg Complex.ofReal (hperiodic k y)
  have hcoeff (k : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff
          (fun y : Torus =>
            (AVenhance.Infra.Torus.periodicToTorus (α := ℝ) ψ y : ℂ)) k = a k := by
    have h := AVenhance.Infra.Ergodic.mFourierCoeff_periodicToTorus_eq_smooth
      hperiodicC (Complex.continuous_ofReal.comp hψ.continuous) k
    have h' : UnitAddTorus.mFourierCoeff
        (AVenhance.Infra.Torus.periodicToTorus
          (fun y => (ψ y : ℂ))) k = a k := by
      simpa [a] using h
    have hfun : AVenhance.Infra.Torus.periodicToTorus
        (fun y => (ψ y : ℂ)) =
          fun y => (AVenhance.Infra.Torus.periodicToTorus (α := ℝ) ψ y : ℂ) := by
      rfl
    rw [← hfun]
    exact h'
  have hsum :
      ∑ k ∈ AVenhance.Infra.Ergodic.frequencyBall N,
        a k * AVenhance.Infra.Torus.torusCharacter (-k) x =
      ∑ p ∈ symmetricFrequencyBox N,
        UnitAddTorus.mFourierCoeff
            (fun y : Torus =>
              (AVenhance.Infra.Torus.periodicToTorus (α := ℝ) ψ y : ℂ))
            (pairFrequency p) *
          UnitAddTorus.mFourier (pairFrequency p)
            (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
    classical
    apply Finset.sum_bij (fun k _ => frequencyPair k)
    · intro k hk
      exact (TestDensityBridge.frequencyBall_pairFrequency_iff N k).mp hk
    · intro k hk l hl hkl
      exact TestDensityBridge.frequencyPair_injective hkl
    · intro p hp
      refine ⟨pairFrequency p, ?_, TestDensityBridge.frequencyPair_pairFrequency p⟩
      rw [TestDensityBridge.frequencyBall_pairFrequency_iff, TestDensityBridge.frequencyPair_pairFrequency]
      exact hp
    · intro k hk
      rw [pairFrequency_frequencyPair, hcoeff]
      simp [AVenhance.Infra.Torus.torusCharacter]
  change (∑ k ∈ AVenhance.Infra.Ergodic.frequencyBall N,
      a k * AVenhance.Infra.Torus.torusCharacter (-k) x).re = _
  rw [hsum]
  rfl
theorem TestDensityBridge.realFourierModeFin_ambient_at (N : ℕ)
    (i : Fin (RealFourierDimension N)) (x : Vec 2) :
    realFourierModeFin N i (AVenhance.Infra.Torus.toUnitTorus 2 x) =
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) x := by
  rw [realFourierModeFin_eq_periodicToTorus]
  have hper := (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _).2
    (realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm i))
  have h := congrFun
    (AVenhance.Infra.Torus.fromUnitTorus_periodicToTorus hper) x
  simpa [AVenhance.Infra.Torus.fromUnitTorus,
    AVenhance.Infra.Torus.periodicToTorus] using h
theorem testFourierCutoff_ambientExpansion_coeff
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hperiodic : AVenhance.IsZ2Periodic ψ) (N : ℕ) :
    ∀ x : Vec 2,
      AVenhance.Infra.Section5.testFourierCutoff ψ N x =
        ∑ i : Fin (RealFourierDimension N),
          (modeProjectionCoefficients (RealFourierDimension N)
            (realFourierModeFin N)
            (AVenhance.Infra.Torus.periodicToTorus ψ)) i *
            realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm i) x := by
  let f : Torus → ℝ := AVenhance.Infra.Torus.periodicToTorus ψ
  let fC : Torus → ℂ := AVenhance.Infra.Torus.periodicToTorus
    (fun x => (ψ x : ℂ))
  have hfC : Continuous fC := by
    exact AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
      (Complex.continuous_ofReal.comp hψ.continuous)
      (fun k x => congrArg Complex.ofReal (hperiodic k x))
  have hf : Continuous f := by
    have heq : f = fun y => (fC y).re := by
      funext y
      rfl
    rw [heq]
    exact Complex.continuous_re.comp hfC
  have hint : Integrable f (volume : Measure Torus) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let c : Coefficients (RealFourierDimension N) :=
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
  have hprojection := realFourierModeFin_projectionExpansion_eq_projection N hint
  intro x
  calc
    AVenhance.Infra.Section5.testFourierCutoff ψ N x =
        realFourierProjection N f
          (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
            exact TestDensityBridge.testFourierCutoff_eq_realFourierProjection_ambient
              (hψ.of_le (by norm_num)) hperiodic N x
    _ = modeExpansion (RealFourierDimension N) (realFourierModeFin N) c
          (AVenhance.Infra.Torus.toUnitTorus 2 x) := by
            exact congrFun hprojection.symm
              (AVenhance.Infra.Torus.toUnitTorus 2 x)
    _ = ∑ i : Fin (RealFourierDimension N),
          c i * realFourierModeAmbient N
            ((realFourierIndexEquivFin N).symm i) x := by
            unfold modeExpansion
            apply Finset.sum_congr rfl
            intro i hi
            rw [TestDensityBridge.realFourierModeFin_ambient_at]
end AVenhance.Infra.Parabolic.FourierGalerkin
end
