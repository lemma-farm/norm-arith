module

public import Mathlib
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- ==== Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.Gaussian ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# Concrete Gaussian quantities

The expectations in the paper are Bochner integrals against mathlib's standard
Gaussian probability measure. We keep `q` explicit; existence and uniqueness of
the fixed point are proved separately in `FixedPointUnique.lean`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
noncomputable def gaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂gaussianReal 0 1
noncomputable def heatSemigroup (ell : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  gaussianExpectation (fun z => φ (x + Real.sqrt ell * z))
end Paper

end
end

-- ==== Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.ParisiPDE ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# The weak Parisi equation and its concrete Duhamel operator

The potential has linear growth and is not required to be bounded.  The
weak spatial gradient is separately represented and essentially bounded.
Tests for the terminal equation have compact support away from time zero;
their support is allowed to meet time one, so the terminal trace is retained.

The Gaussian operators below are actual integrals, not abstract kernels.
The estimates are the preliminary bounds for a bounded-gradient fixed point.
No existence or uniqueness of the general weak PDE is asserted in this file.
-/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace Paper

noncomputable def gaussianAbsMoment : ℝ := gaussianExpectation (fun z => ‖z‖)

end Paper

end
end

-- ==== Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.VolterraFubini ====
public section
set_option autoImplicit false
@[expose] public section
/-! # Changing the order of integration on the Volterra time triangle -/
open Set MeasureTheory
namespace Paper
noncomputable def parisiTimeMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
set_option linter.unusedVariables false in
axiom _root_.Paper.instIsFiniteMeasureRealParisiTimeMeasure : MeasureTheory.IsFiniteMeasure Paper.parisiTimeMeasure
attribute [instance] _root_.Paper.instIsFiniteMeasureRealParisiTimeMeasure
end Paper

end
end

-- ==== Examples.pmaronow__frsb_palomar.Examples.Example_6fd5e73ce51180901fff_ParisiTerminalWeak ====
set_option autoImplicit false
@[expose] public section
/-! # The linearly growing terminal term in the weak Parisi equation

The terminal datum is `log cosh`.  Spatial self-adjointness and the heat
operator's first absolute moment justify the terminal heat identity without
assuming that this datum is bounded.
-/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff
namespace Paper

set_option linter.unusedVariables false in
theorem integrable_logcosh_heatTest (β : ℝ) (ψ : ℝ × ℝ → ℝ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) 
    (h_Paper_exists_uniform_integral_norm_sections_bound : ∀ (ψ : ℝ × ℝ → ℝ),
      Continuous ψ → HasCompactSupport ψ → ∃ (B : ℝ), 0 ≤ B ∧ ∀ (t : ℝ), ∫ (x : ℝ), ‖ψ (t, x)‖ ≤ B)
    (h_Paper_gaussianAbsMoment_nonneg : 0 ≤ Paper.gaussianAbsMoment)
    (h_Paper_norm_logcosh_le_abs : ∀ (x : ℝ), ‖Real.log (Real.cosh x)‖ ≤ |x|)
    (h_Paper_continuous_logcosh : Continuous fun (x : ℝ) ↦ Real.log (Real.cosh x))
    (h_Paper_heatSemigroup_firstMoment : ∀ (ell : ℝ),
      0 ≤ ell →
        ∀ (g : ℝ → ℝ),
          Measurable g →
            MeasureTheory.Integrable g MeasureTheory.MeasureSpace.volume →
              MeasureTheory.Integrable (fun (x : ℝ) ↦ ‖x‖ * ‖g x‖) MeasureTheory.MeasureSpace.volume →
                MeasureTheory.Integrable (fun (x : ℝ) ↦ ‖x‖ * Paper.heatSemigroup ell g x)
                    MeasureTheory.MeasureSpace.volume ∧
                  ∫ (x : ℝ), ‖x‖ * ‖Paper.heatSemigroup ell g x‖ ≤
                    (∫ (x : ℝ), ‖x‖ * ‖g x‖) + √ell * Paper.gaussianAbsMoment * ∫ (x : ℝ), ‖g x‖)
    (h_Paper_hasCompactSupport_spatial_section : ∀ (φ : ℝ × ℝ → ℝ), HasCompactSupport φ → ∀ (t : ℝ), HasCompactSupport fun (x : ℝ) ↦ φ (t, x))
    :
    Integrable (fun p : ℝ × ℝ => Real.log (Real.cosh p.2) *
      heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => ψ (p.1, y)) p.2)
      (parisiTimeMeasure.prod volume) := by
  obtain ⟨B, hB0, hB⟩ := h_Paper_exists_uniform_integral_norm_sections_bound ψ hψ hc
  let χ : ℝ × ℝ → ℝ := fun p => ‖p.2‖ * ψ p
  have hχ : Continuous χ := by unfold χ; fun_prop
  have hχc : HasCompactSupport χ := hc.mul_left
  obtain ⟨D, _hD0, hD⟩ := h_Paper_exists_uniform_integral_norm_sections_bound χ hχ hχc
  have hψmeas : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      ψ (p.1.1, p.1.2 + Real.sqrt (β ^ 2 * (1 - p.1.1)) * p.2)) :=
    hψ.measurable.comp (by fun_prop)
  have hh := (hψmeas.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hp : Measurable (fun p : ℝ × ℝ => Real.log (Real.cosh p.2) *
      heatSemigroup (β ^ 2 * (1 - p.1)) (fun y => ψ (p.1, y)) p.2) :=
    (h_Paper_continuous_logcosh.comp continuous_snd).measurable.mul hh
  have hsections (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) := by
    have hψi : Integrable (fun x : ℝ => ψ (t, x)) :=
      (hψ.comp (by fun_prop)).integrable_of_hasCompactSupport
        (h_Paper_hasCompactSupport_spatial_section ψ hc t)
    have hχi : Integrable (fun x : ℝ => ‖x‖ * ψ (t, x)) :=
      (hχ.comp (by fun_prop)).integrable_of_hasCompactSupport
        (h_Paper_hasCompactSupport_spatial_section χ hχc t)
    have hweighted : Integrable (fun x : ℝ => ‖x‖ * ‖ψ (t, x)‖) := by
      simpa only [norm_mul, norm_norm] using hχi.norm
    exact h_Paper_heatSemigroup_firstMoment (β ^ 2 * (1 - t))
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr ht.2)) (fun y => ψ (t, y))
      ((hψ.comp (by fun_prop)).measurable) hψi hweighted
  have hbound (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      (∫ x, ‖Real.log (Real.cosh x) *
        heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x‖) ≤
        D + |β| * gaussianAbsMoment * B := by
    have hheat := hsections t ht
    have hi : Integrable (fun x : ℝ => Real.log (Real.cosh x) *
        heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x) := by
      apply hheat.1.norm.mono'
        ((hp.comp (show Measurable (fun x : ℝ => (t, x)) by fun_prop)).aestronglyMeasurable)
      filter_upwards with x
      change ‖Real.log (Real.cosh x) * heatSemigroup (β ^ 2 * (1 - t))
        (fun y => ψ (t, y)) x‖ ≤ ‖‖x‖ * heatSemigroup (β ^ 2 * (1 - t))
        (fun y => ψ (t, y)) x‖
      simp only [norm_mul, norm_norm]
      have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using (h_Paper_norm_logcosh_le_abs x)
      exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    have hsq : Real.sqrt (β ^ 2 * (1 - t)) ≤ |β| := by
      calc
        _ ≤ Real.sqrt (β ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg β, ht.1.le])
        _ = _ := Real.sqrt_sq_eq_abs β
    calc
      _ ≤ ∫ x, ‖x‖ * ‖heatSemigroup (β ^ 2 * (1 - t)) (fun y => ψ (t, y)) x‖ := by
        apply integral_mono hi.norm
          (by simpa only [norm_mul, norm_norm] using hheat.1.norm)
        intro x
        dsimp only
        rw [norm_mul]
        have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
          simpa only [Real.norm_eq_abs] using (h_Paper_norm_logcosh_le_abs x)
        exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      _ ≤ _ := hheat.2
      _ ≤ D + |β| * gaussianAbsMoment * B := by
        have hDw : (∫ x, ‖x‖ * ‖ψ (t, x)‖) ≤ D := by
          simpa only [χ, norm_mul, norm_norm] using hD t
        calc
          _ ≤ D + Real.sqrt (β ^ 2 * (1 - t)) * gaussianAbsMoment * B :=
            add_le_add hDw (mul_le_mul_of_nonneg_left (hB t)
              (mul_nonneg (Real.sqrt_nonneg _) h_Paper_gaussianAbsMoment_nonneg))
          _ ≤ _ := add_le_add (le_refl D)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq h_Paper_gaussianAbsMoment_nonneg) hB0)
  apply (integrable_prod_iff hp.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply (hsections t ht).1.norm.mono'
      ((hp.comp (show Measurable (fun x : ℝ => (t, x)) by fun_prop)).aestronglyMeasurable)
    filter_upwards with x
    change ‖Real.log (Real.cosh x) * heatSemigroup (β ^ 2 * (1 - t))
      (fun y => ψ (t, y)) x‖ ≤ ‖‖x‖ * heatSemigroup (β ^ 2 * (1 - t))
      (fun y => ψ (t, y)) x‖
    simp only [norm_mul, norm_norm]
    have hl : ‖Real.log (Real.cosh x)‖ ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using (h_Paper_norm_logcosh_le_abs x)
    exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
  · apply (integrable_const (D + |β| * gaussianAbsMoment * B)).mono'
      (hp.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using hbound t ht
end Paper
