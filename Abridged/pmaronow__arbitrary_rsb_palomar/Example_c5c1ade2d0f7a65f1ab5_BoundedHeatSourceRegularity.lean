module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Monotone
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.Gaussian ====
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
end Paper

end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.ParisiPDE ====
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
noncomputable def heatGradient (ell : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt ell)⁻¹ * gaussianExpectation (fun z => z * f (x + Real.sqrt ell * z))

end Paper

end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.VolterraFubini ====
public section
set_option autoImplicit false
@[expose] public section
/-! # Changing the order of integration on the Volterra time triangle -/
open Set MeasureTheory
namespace Paper
noncomputable def parisiTimeMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

end Paper

end
end

-- ==== Examples.pmaronow__arbitrary_rsb_palomar.Examples.Example_c5c1ade2d0f7a65f1ab5_BoundedHeatSourceRegularity ====
set_option autoImplicit false
@[expose] public section
/-!
# Regularity of the heat Volterra potential of a bounded measurable source

The source may be discontinuous in both variables. Spatial differentiation
acts on the genuine Gaussian kernel; the inverse-square-root time singularity
is integrable. The source is never assumed to have a classical derivative.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real Filter
open scoped Topology NNReal
namespace Paper
def boundedHeatGradientSource (β : ℝ) (F : ℝ × ℝ → ℝ) (t s x : ℝ) : ℝ :=
  heatGradient (β ^ 2 * (s - t)) (fun y => F (s, y)) x
def boundedVolterraGradient (β : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s, if p.1 < s then boundedHeatGradientSource β F p.1 s p.2 else 0 ∂parisiTimeMeasure


set_option linter.unusedVariables false in
theorem norm_boundedVolterraGradient_le (β : ℝ) (F : ℝ × ℝ → ℝ)
    (hF : Measurable F) (M : ℝ) (hb : ∀ p, ‖F p‖ ≤ M)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) 
    (h_Paper_norm_boundedHeatGradientSource_le : ∀ (β : ℝ) (F : ℝ × ℝ → ℝ) (M : ℝ),
      (∀ (p : ℝ × ℝ), ‖F p‖ ≤ M) →
        ∀ (t s x : ℝ),
          ‖Paper.boundedHeatGradientSource β F t s x‖ ≤
            |β|⁻¹ * Paper.gaussianAbsMoment * M * (√(s - t))⁻¹)
    (h_Paper_intervalIntegrable_inv_sqrt_sub : ∀ (t b : ℝ),
      t ≤ b → IntervalIntegrable (fun (s : ℝ) ↦ (√(s - t))⁻¹) MeasureTheory.MeasureSpace.volume t b)
    (h_Paper_integral_inv_sqrt_sub : ∀ (t b : ℝ), t ≤ b → ∫ (s : ℝ) in t..b, (√(s - t))⁻¹ = 2 * √(b - t))
    (h_Paper_boundedVolterraGradient_eq : ∀ (β : ℝ) (F : ℝ × ℝ → ℝ) (t x : ℝ),
      t ∈ Set.Icc 0 1 →
        Paper.boundedVolterraGradient β F (t, x) =
          ∫ (s : ℝ) in t..1, Paper.boundedHeatGradientSource β F t s x)
    :
    ‖boundedVolterraGradient β F (t, x)‖ ≤
      2 * M * gaussianAbsMoment / |β| * Real.sqrt (1 - t) := by
  rw [h_Paper_boundedVolterraGradient_eq β F t x ht]
  have hh := intervalIntegral.norm_integral_le_of_norm_le ht.2
    (.of_forall (fun s _ => h_Paper_norm_boundedHeatGradientSource_le β F M hb t s x))
    ((h_Paper_intervalIntegrable_inv_sqrt_sub t 1 ht.2).const_mul (|β|⁻¹ * gaussianAbsMoment * M))
  rw [intervalIntegral.integral_const_mul, h_Paper_integral_inv_sqrt_sub t 1 ht.2] at hh
  exact hh.trans_eq (by ring)
end Paper
