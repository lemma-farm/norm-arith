module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_2d55283b0ad1a4ceec6b_GammaGaussianTransform ====
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Provenance: ../../../../../third_party/twelfth/ATKINSON_GAUSSIAN_MANIFEST.json.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


set_option linter.unusedVariables false in
private theorem norm_integral_sub_window_le {f : ℝ → ℂ} {G r : ℝ}
    (hG : 0 < G) (hr : 0 ≤ r) (hf : Integrable f)
    (hfn : ∀ x, ‖f x‖ ≤ Real.exp (-(x / G) ^ 2)) 
    (h_MathCollab_Density_Stronger_Atkinson_integrable_physical_gaussian : ∀ {G : ℝ},
      G ≠ 0 →
        MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (-(x / G) ^ 2))
          MeasureTheory.MeasureSpace.volume)
    (h_MathCollab_Density_Stronger_Atkinson_physical_gaussian_tail_le : ∀ {G r : ℝ},
      0 < G →
        0 ≤ r →
          ∫ (x : ℝ) in (Set.Ioc (-r) r)ᶜ, Real.exp (-(x / G) ^ 2) ≤
            √(2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2))
    :
    ‖(∫ x : ℝ, f x) - ∫ x in -r..r, f x‖ ≤
      Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) := by
  rw [intervalIntegral.integral_of_le (by linarith),
    ← setIntegral_compl measurableSet_Ioc hf]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact (integral_mono_ae hf.norm.integrableOn
    (h_MathCollab_Density_Stronger_Atkinson_integrable_physical_gaussian hG.ne').integrableOn
    (Eventually.of_forall hfn)).trans (h_MathCollab_Density_Stronger_Atkinson_physical_gaussian_tail_le hG hr)

end MathCollab.Density.Stronger.Atkinson
