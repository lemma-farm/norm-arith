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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v0329a7ad73dc.MathCollab.Density.Stronger.Fourth.Coefficients ====
public section
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set Finset MeasureTheory Filter
open scoped BigOperators Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

noncomputable def afeCriticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I

end MathCollab.Density.Stronger.Fourth

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v0329a7ad73dc.MathCollab.Density.Stronger.Atkinson.GammaPhase ====
public section
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
open Complex MeasureTheory
open scoped ComplexConjugate
open MathCollab.Density.Stronger.Fourth

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def zetaSquareReflectedGammaPhase (t : ℝ) : ℂ :=
  Complex.Gammaℝ (afeCriticalPoint (-t)) / Complex.Gammaℝ (afeCriticalPoint t)

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v0329a7ad73dc.MathCollab.Density.Stronger.Atkinson.QuadraticGaussian ====
public section
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
open Complex MeasureTheory
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
def zetaGaussianQuadraticCoefficient (T G : ℝ) : ℂ :=
  ((1 / G ^ 2 : ℝ) : ℂ) + ((1 / (2 * T) : ℝ) : ℂ) * I
def zetaGaussianQuadraticIntegral (T G v : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (I * (v : ℂ) * x) *
    Complex.exp (-zetaGaussianQuadraticCoefficient T G * x ^ 2)

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_c4c68ca7c55b506551fb_GammaGaussianTransform ====
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

def zetaSquareGammaGaussianIntegrand (T G v x : ℝ) : ℂ :=
  zetaSquareReflectedGammaPhase (T + x) * Complex.exp (I * (v : ℂ) * x) *
    ((Real.exp (-(x / G) ^ 2) : ℝ) : ℂ)
def zetaSquareGammaGaussianTransform (T G v : ℝ) : ℂ :=
  ∫ x : ℝ, zetaSquareGammaGaussianIntegrand T G v x


set_option linter.unusedVariables false in
/-- The actual Gamma-phase transform is approximated by the proved quadratic
Gaussian transform, uniformly in frequency, with both omitted tails paid. -/
theorem norm_zetaSquareGammaGaussianTransform_sub_quadratic_le {T G r : ℝ}
    (hT : 4 ≤ T) (hG : 0 < G) (hr : 0 ≤ r) (hrT : r ≤ T / 2) (v : ℝ) 
    (h_MathCollab_Density_Stronger_Atkinson_norm_quadratic_gaussian_integrand : ∀ (T v x : ℝ) {G : ℝ},
      G ≠ 0 →
        ‖Complex.exp (Complex.I * (↑v : ℂ) * (↑x : ℂ)) *
              Complex.exp
                (-MathCollab.Density.Stronger.Atkinson.zetaGaussianQuadraticCoefficient T G *
                  (↑x : ℂ) ^ 2)‖ =
          Real.exp (-(x / G) ^ 2))
    (h_MathCollab_Density_Stronger_Atkinson_norm_zetaSquareReflectedGammaPhase : ∀ (t : ℝ), ‖MathCollab.Density.Stronger.Atkinson.zetaSquareReflectedGammaPhase t‖ = 1)
    (h_MathCollab_Density_Stronger_Atkinson_norm_integral_zetaSquareGammaPhase_sub_quadratic_le : ∀ {T r G : ℝ},
      4 ≤ T →
        0 ≤ r →
          r ≤ T / 2 →
            ∀ (v : ℝ),
              ‖(∫ (x : ℝ) in -r..r,
                      MathCollab.Density.Stronger.Atkinson.zetaSquareReflectedGammaPhase (T + x) *
                          Complex.exp (Complex.I * (↑v : ℂ) * (↑x : ℂ)) *
                        (↑(Real.exp (-(x / G) ^ 2)) : ℂ)) -
                    MathCollab.Density.Stronger.Atkinson.zetaSquareReflectedGammaPhase T *
                      ∫ (x : ℝ) in -r..r,
                        Complex.exp (Complex.I * (↑(v - Real.log (T / (2 * Real.pi))) : ℂ) * (↑x : ℂ)) *
                          Complex.exp
                            (-MathCollab.Density.Stronger.Atkinson.zetaGaussianQuadraticCoefficient T
                                  G *
                              (↑x : ℂ) ^ 2)‖ ≤
                2 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2))
    (h_MathCollab_Density_Stronger_Atkinson_norm_integral_sub_window_le : ∀ {f : ℝ → ℂ} {G r : ℝ},
      0 < G →
        0 ≤ r →
          MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume →
            (∀ (x : ℝ), ‖f x‖ ≤ Real.exp (-(x / G) ^ 2)) →
              ‖(∫ (x : ℝ), f x) - ∫ (x : ℝ) in -r..r, f x‖ ≤
                √(2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2))
    (h_MathCollab_Density_Stronger_Atkinson_integrable_zetaSquareGammaGaussianIntegrand : ∀ (T v : ℝ) {G : ℝ},
      G ≠ 0 →
        MeasureTheory.Integrable
          (MathCollab.Density.Stronger.Atkinson.zetaSquareGammaGaussianIntegrand T G v)
          MeasureTheory.MeasureSpace.volume)
    (h_MathCollab_Density_Stronger_Atkinson_integrable_zetaGaussianQuadraticIntegrand : ∀ (T v : ℝ) {G : ℝ},
      G ≠ 0 →
        MeasureTheory.Integrable
          (fun (x : ℝ) ↦
            Complex.exp (Complex.I * (↑v : ℂ) * (↑x : ℂ)) *
              Complex.exp
                (-MathCollab.Density.Stronger.Atkinson.zetaGaussianQuadraticCoefficient T G *
                  (↑x : ℂ) ^ 2))
          MeasureTheory.MeasureSpace.volume)
    (h_MathCollab_Density_Stronger_Atkinson_norm_zetaSquareGammaGaussianIntegrand : ∀ (T G v x : ℝ),
      ‖MathCollab.Density.Stronger.Atkinson.zetaSquareGammaGaussianIntegrand T G v x‖ =
        Real.exp (-(x / G) ^ 2))
    :
    ‖zetaSquareGammaGaussianTransform T G v - zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi)))‖ ≤
      2 * r ^ 2 * (18 / T + 2 * r ^ 2 / T ^ 2) +
        2 * Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) := by
  let q := fun x : ℝ => Complex.exp (I * ((v - Real.log (T / (2 * Real.pi)) : ℝ) : ℂ) * x) *
    Complex.exp (-zetaGaussianQuadraticCoefficient T G * (x : ℂ) ^ 2)
  let F := ∫ x in -r..r, zetaSquareGammaGaussianIntegrand T G v x
  let Q := ∫ x in -r..r, q x
  have hleft := h_MathCollab_Density_Stronger_Atkinson_norm_integral_sub_window_le hG hr
    (h_MathCollab_Density_Stronger_Atkinson_integrable_zetaSquareGammaGaussianIntegrand T v hG.ne')
    (fun x => (h_MathCollab_Density_Stronger_Atkinson_norm_zetaSquareGammaGaussianIntegrand T G v x).le)
  have hright := h_MathCollab_Density_Stronger_Atkinson_norm_integral_sub_window_le hG hr
    (h_MathCollab_Density_Stronger_Atkinson_integrable_zetaGaussianQuadraticIntegrand T (v - Real.log (T / (2 * Real.pi))) hG.ne')
    (fun x => (h_MathCollab_Density_Stronger_Atkinson_norm_quadratic_gaussian_integrand T _ x hG.ne').le)
  have hmiddle := h_MathCollab_Density_Stronger_Atkinson_norm_integral_zetaSquareGammaPhase_sub_quadratic_le
    (G := G) hT hr hrT v
  change ‖F - zetaSquareReflectedGammaPhase T * Q‖ ≤ _ at hmiddle
  change ‖zetaSquareGammaGaussianTransform T G v - F‖ ≤ _ at hleft
  change ‖zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi))) - Q‖ ≤ _ at hright
  have hright' : ‖zetaSquareReflectedGammaPhase T * Q - zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi)))‖ ≤
      Real.sqrt (2 * Real.pi) * G * Real.exp (-(r / G) ^ 2 / 2) := by
    rw [← mul_sub, norm_mul, h_MathCollab_Density_Stronger_Atkinson_norm_zetaSquareReflectedGammaPhase, one_mul, norm_sub_rev]
    exact hright
  have htri := norm_sub_le_norm_sub_add_norm_sub (zetaSquareGammaGaussianTransform T G v) F
    (zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi))))
  have htri' := norm_sub_le_norm_sub_add_norm_sub F (zetaSquareReflectedGammaPhase T * Q)
    (zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (v - Real.log (T / (2 * Real.pi))))
  linarith
end MathCollab.Density.Stronger.Atkinson
