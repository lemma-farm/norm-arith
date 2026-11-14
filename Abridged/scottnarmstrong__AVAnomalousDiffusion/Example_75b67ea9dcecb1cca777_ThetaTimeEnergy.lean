module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Constructions
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8c2bc0ddceb.Homogenization.Ambient.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8c2bc0ddceb.AVenhance.Statements.Roots.UnitCube ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `unitCube` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- The open unit cube `(0,1)²`, a full-measure representative of the fundamental cell of `𝕋²`. -/
def unitCube : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_75b67ea9dcecb1cca777_ThetaTimeEnergy ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Time differentiation of the periodic quadratic energy. -/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization

open scoped Topology
namespace AVenhance.Infra.Section4
def classicalPositiveTimeDomain : Set (ℝ × Vec 2) := Set.Ioi (0 : ℝ) ×ˢ Set.univ
axiom ThetaTimeEnergy.thetaTime_unitCube_subset_closedCell :
    AVenhance.unitCube ⊆ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)
axiom ThetaTimeEnergy.isCompact_closedUnitCell :
    IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1))
axiom thetaTime_integrableOn_unitCube {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (AVenhance.unitCube)
axiom thetaTime_measurableSet_unitCube : MeasurableSet AVenhance.unitCube
def ThetaTimeEnergy.timeVector : ℝ × Vec 2 := (1, 0)
def classicalTimePartial (u : ℝ → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  fderiv ℝ (Function.uncurry u) p ThetaTimeEnergy.timeVector
axiom ThetaTimeEnergy.partialTime_continuousOn {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain) :
    ContinuousOn (classicalTimePartial u) classicalPositiveTimeDomain
axiom classicalTimeSection_hasDerivAt {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun s => u s x) (classicalTimePartial u (t, x)) t

axiom classicalTimePartial_continuous_slice {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : Continuous (fun x => classicalTimePartial u (t, x))

axiom classicalContinuous_slice {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) : Continuous (u t)
/-- The unit-cell quadratic energy is differentiable at every positive time, with the expected
pointwise time derivative under the integral. -/
theorem theta_energy_hasDerivAt {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in AVenhance.unitCube, (u s x) ^ 2)
      (∫ x in AVenhance.unitCube, 2 * u t x * classicalTimePartial u (t, x)) t := by
  have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u) classicalPositiveTimeDomain :=
    hu.mono (by
      intro p hp
      simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
      exact ⟨le_of_lt hp.1, trivial⟩)
  let radius : ℝ := t / 2
  have hradius : 0 < radius := by dsimp [radius]; linarith
  have hball : Metric.ball t radius ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    dsimp [radius] at hs
    have h := abs_lt.mp hs
    rw [Set.mem_Ioi]
    linarith
  let K : Set (ℝ × Vec 2) :=
    Set.Icc (t - radius) (t + radius) ×ˢ
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)
  have hKcompact : IsCompact K := by
    apply IsCompact.prod isCompact_Icc
    exact ThetaTimeEnergy.isCompact_closedUnitCell
  have hKopen : K ⊆ classicalPositiveTimeDomain := by
    rintro ⟨s, x⟩ hp
    simp only [K, Set.mem_prod, Set.mem_Icc] at hp
    dsimp [radius] at hp
    simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ]
    constructor
    · linarith
    · trivial
  have huCont := huOpen.continuousOn
  have huBound := hKcompact.exists_bound_of_continuousOn (huCont.mono hKopen)
  obtain ⟨C₀, hC₀⟩ := huBound
  have hdtCont := ThetaTimeEnergy.partialTime_continuousOn huOpen
  have hdtBound := hKcompact.exists_bound_of_continuousOn (hdtCont.mono hKopen)
  obtain ⟨C₁, hC₁⟩ := hdtBound
  let bound : ℝ := 2 * (C₀ + 1) * (C₁ + 1)
  let μ : Measure (Vec 2) := volume.restrict (AVenhance.unitCube)
  let integrand : ℝ → Vec 2 → ℝ := fun s x => (u s x) ^ 2
  let integrandDeriv : ℝ → Vec 2 → ℝ :=
    fun s x => 2 * u s x * classicalTimePartial u (s, x)
  have hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (integrand s) μ := by
    filter_upwards [Metric.ball_mem_nhds t hradius] with s hs
    exact ((classicalContinuous_slice huOpen (hball hs)).pow 2).aestronglyMeasurable
  have hFint : Integrable (integrand t) μ := by
    change IntegrableOn (fun x => (u t x) ^ 2) (AVenhance.unitCube)
    apply thetaTime_integrableOn_unitCube
    exact (classicalContinuous_slice huOpen ht).pow 2
  have hF'diff : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t radius,
      HasDerivAt (integrand · x) (integrandDeriv s x) s := by
    apply (ae_restrict_iff' thetaTime_measurableSet_unitCube).2
    filter_upwards with x hx
    intro s hs
    have htime := classicalTimeSection_hasDerivAt huOpen (hball hs) x
    have hpow : HasDerivAt (fun r => u r x ^ 2)
        (2 * u s x * classicalTimePartial u (s, x)) s := by
      have hpow0 := htime.pow 2
      have hfun : (fun r => u r x) ^ 2 = (fun r => u r x ^ 2) := by
        funext r
        rfl
      rw [hfun] at hpow0
      simpa using hpow0
    change HasDerivAt (fun r => u r x ^ 2)
      (2 * u s x * classicalTimePartial u (s, x)) s
    exact hpow
  have hF'meas : AEStronglyMeasurable (integrandDeriv t) μ := by
    have hcont : Continuous (integrandDeriv t) := by
      have huC := classicalContinuous_slice huOpen ht
      have hdtC := classicalTimePartial_continuous_slice huOpen ht
      change Continuous (fun x => 2 * u t x * classicalTimePartial u (t, x))
      exact ((continuous_const : Continuous fun _ : Vec 2 => (2 : ℝ)).mul huC).mul hdtC
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t radius,
      ‖integrandDeriv s x‖ ≤ bound := by
    apply (ae_restrict_iff' thetaTime_measurableSet_unitCube).2
    filter_upwards with x hx
    intro s hs
    have hsK : (s, x) ∈ K := by
      simp only [K, Set.mem_prod, Set.mem_Icc]
      refine ⟨?_, ThetaTimeEnergy.thetaTime_unitCube_subset_closedCell hx⟩
      rw [Metric.mem_ball, Real.dist_eq] at hs
      dsimp [radius] at hs
      have h := abs_lt.mp hs
      change t - radius ≤ s ∧ s ≤ t + radius
      dsimp [radius]
      constructor <;> linarith
    have huBound' := hC₀ (s, x) hsK
    have hdtBound' := hC₁ (s, x) hsK
    have huNorm : ‖u s x‖ ≤ C₀ + 1 := by
      have huBound'' : ‖u s x‖ ≤ C₀ := by
        simpa [Function.uncurry] using huBound'
      exact le_trans huBound'' (by linarith)
    have hdtNorm : ‖classicalTimePartial u (s, x)‖ ≤ C₁ + 1 := by
      exact le_trans hdtBound' (by linarith)
    have huAbs : |u s x| ≤ C₀ + 1 := by simpa [Real.norm_eq_abs] using huNorm
    have hdtAbs : |classicalTimePartial u (s, x)| ≤ C₁ + 1 := by
      simpa [Real.norm_eq_abs] using hdtNorm
    dsimp [integrandDeriv, bound]
    calc
          |2 * u s x * classicalTimePartial u (s, x)| =
          2 * |u s x| * |classicalTimePartial u (s, x)| := by simp [abs_mul]
      _ ≤ 2 * (C₀ + 1) * (C₁ + 1) := by
        have hC₀nonneg : 0 ≤ C₀ + 1 := le_trans (abs_nonneg _) huAbs
        have hmul := mul_le_mul huAbs hdtAbs (abs_nonneg _) hC₀nonneg
        calc
          2 * |u s x| * |classicalTimePartial u (s, x)| =
              2 * (|u s x| * |classicalTimePartial u (s, x)|) := by ring
          _ ≤ 2 * ((C₀ + 1) * (C₁ + 1)) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
          _ = 2 * (C₀ + 1) * (C₁ + 1) := by ring
      _ = bound := rfl
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t radius) (μ := μ) (bound := fun _ : Vec 2 => bound)
    (Metric.ball_mem_nhds t hradius) hFmeas hFint hF'meas hbound
    (by
      change IntegrableOn (fun _ : Vec 2 => bound) (AVenhance.unitCube)
      exact thetaTime_integrableOn_unitCube continuous_const)
    hF'diff
  simpa [integrand, integrandDeriv, μ] using hderiv.2
end AVenhance.Infra.Section4
end
