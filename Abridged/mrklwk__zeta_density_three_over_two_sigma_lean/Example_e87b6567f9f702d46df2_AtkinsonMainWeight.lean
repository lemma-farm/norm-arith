module

public import Mathlib
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.MeanValue

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Fourth.Coefficients ====
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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Fourth.SquareSource ====
public section
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Source slices and exact hashes:
../../../../../third_party/twelfth/SQUARE_PORT_MANIFEST.json.
See ../../../../../third_party/twelfth/LICENSE-MIT-0.
The local rectangle theorem preserves its PNT+ Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology ArithmeticFunction
open  MathCollab.Density.Stronger
open MathCollab.Density.Stronger.Fourth
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma BigOperators Interval
  LSeries.notation ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
noncomputable def hughesYoungAuxiliaryZero (w : ℂ) : ℂ :=
  (1 - 4 * w ^ 2) ^ 4

end MathCollab.Density.Stronger.Fourth

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.GammaPhase ====
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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.DivisorWeightKernel ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth

open scoped Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
def zetaDivisorWeightNumerator (q w : ℂ) : ℂ :=
  Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w * Complex.exp (-q * w)
def zetaDivisorWeightKernel (q w : ℂ) : ℂ := zetaDivisorWeightNumerator q w / w
def zetaDivisorWeight (q : ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u : ℝ, zetaDivisorWeightKernel q (1 + (u : ℂ) * I)

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.QuadraticGaussian ====
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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.DivisorBandCutoff ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth

open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
def zetaBandCutoff (a b c d x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a) / (b - a)) *
    Real.smoothTransition ((d - x) / (d - c))
def zetaDivisorBandEdge (T G v : ℝ) : ℝ := T / (2 * Real.pi) * Real.exp (v / G)
def zetaDivisorBandCutoff (T G L : ℝ) : ℝ → ℝ :=
  zetaBandCutoff (zetaDivisorBandEdge T G (-2 * L)) (zetaDivisorBandEdge T G (-L))
    (zetaDivisorBandEdge T G L) (zetaDivisorBandEdge T G (2 * L))

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeBounds ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-!
# Concrete C1 amplitude bounds on an interval

The bound records the actual supremum and integral of the norm of
the derivative. Product rules preserve those literal analytic quantities;
the source application below must construct every bound it consumes.
-/
noncomputable section
open Complex MeasureTheory Set
open scoped ContDiff
namespace MathCollab.Density.Stronger.Atkinson
structure IntervalC1Bound (f : ℝ → ℂ) (a b M : ℝ) : Prop where
  nonneg : 0 ≤ M
  smooth : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x
  norm_le : ∀ x ∈ Icc a b, ‖f x‖ ≤ M
  variation_le : (∫ x in a..b, ‖deriv f x‖) ≤ M

set_option linter.unusedVariables false in
axiom _root_.MathCollab.Density.Stronger.Atkinson.IntervalC1Bound.mono : ∀ {f : ℝ → ℂ} {a b M N : ℝ},
  MathCollab.Density.Stronger.Atkinson.IntervalC1Bound f a b M →
    M ≤ N → MathCollab.Density.Stronger.Atkinson.IntervalC1Bound f a b N

set_option linter.unusedVariables false in
axiom _root_.MathCollab.Density.Stronger.Atkinson.IntervalC1Bound.mul : ∀ {f g : ℝ → ℂ} {a b M N : ℝ},
  MathCollab.Density.Stronger.Atkinson.IntervalC1Bound f a b M →
    MathCollab.Density.Stronger.Atkinson.IntervalC1Bound g a b N →
      a ≤ b →
        MathCollab.Density.Stronger.Atkinson.IntervalC1Bound (fun (x : ℝ) ↦ f x * g x) a b
          (2 * M * N)

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.AtkinsonCompactProfiles ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_RESIDUAL_VARIATION_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
def zetaMainMellinProfile (u : ℝ) : ℂ :=
  zetaDivisorWeight ((Real.log u + Real.log (2 * Real.pi) : ℝ) +
    (Real.pi / 2 : ℝ) * I)

end MathCollab.Density.Stronger.Atkinson

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_e87b6567f9f702d46df2_AtkinsonMainWeight ====
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
def zetaAtkinsonMainWeight (T G L x : ℝ) : ℂ :=
  ((Real.log x + 2 * Real.eulerMascheroniConstant : ℝ) : ℂ) *
    (zetaDivisorBandCutoff T G L x : ℂ) * (Real.sqrt x : ℂ) *
      zetaMainMellinProfile (x / T) * zetaSquareReflectedGammaPhase T *
        zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))
set_option linter.unusedVariables false in
theorem exists_intervalC1Bound_zetaAtkinsonMainWeight 
    (h_MathCollab_Density_Stronger_Atkinson_exists_intervalC1Bound_zetaMainMellinProfile : ∃ (C : ℝ),
      0 < C ∧
        ∀ (T : ℝ),
          0 < T →
            MathCollab.Density.Stronger.Atkinson.IntervalC1Bound
              (fun (x : ℝ) ↦ MathCollab.Density.Stronger.Atkinson.zetaMainMellinProfile (x / T))
              (T / 16) T C)
    (h_MathCollab_Density_Stronger_Atkinson_norm_zetaSquareReflectedGammaPhase : ∀ (t : ℝ), ‖MathCollab.Density.Stronger.Atkinson.zetaSquareReflectedGammaPhase t‖ = 1)
    (h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_zetaDivisorBandCutoff : ∀ {T G L A B : ℝ},
      0 < T →
        0 < G →
          0 < L →
            A ≤ B →
              MathCollab.Density.Stronger.Atkinson.IntervalC1Bound
                (fun (x : ℝ) ↦
                  (↑(MathCollab.Density.Stronger.Atkinson.zetaDivisorBandCutoff T G L x) : ℂ))
                A B 2)
    (h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_source_sqrt : ∀ {T : ℝ},
      0 < T →
        MathCollab.Density.Stronger.Atkinson.IntervalC1Bound (fun (x : ℝ) ↦ (↑√x : ℂ)) (T / 16) T √T)
    (h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_source_log : ∀ {T : ℝ},
      16 ≤ T →
        MathCollab.Density.Stronger.Atkinson.IntervalC1Bound
          (fun (x : ℝ) ↦ (↑(Real.log x + 2 * Real.eulerMascheroniConstant) : ℂ)) (T / 16) T
          (Real.log T + 2 * Real.eulerMascheroniConstant))
    (h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_zetaQuadraticLogGaussian : ∀ {T G : ℝ},
      0 < T →
        0 < G →
          G ^ 2 ≤ 2 * T →
            MathCollab.Density.Stronger.Atkinson.IntervalC1Bound
              (fun (x : ℝ) ↦
                MathCollab.Density.Stronger.Atkinson.zetaGaussianQuadraticIntegral T G
                  (Real.log x - Real.log (T / (2 * Real.pi))))
              (T / 16) T (4 * √Real.pi * G))
    (h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_const : ∀ (c : ℂ) (a b : ℝ), MathCollab.Density.Stronger.Atkinson.IntervalC1Bound (fun (x : ℝ) ↦ c) a b ‖c‖)
    (h_MathCollab_Density_Stronger_Atkinson_sourceLogWeight_le_three_log : ∀ {T : ℝ}, 1 ≤ Real.log T → Real.log T + 2 * Real.eulerMascheroniConstant ≤ 3 * Real.log T)
    :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 1 ≤ Real.log T →
      0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      IntervalC1Bound (zetaAtkinsonMainWeight T G L) (T / 16) T
        (C * G * Real.sqrt T * Real.log T) := by
  obtain ⟨C, hC, hprofile⟩ := h_MathCollab_Density_Stronger_Atkinson_exists_intervalC1Bound_zetaMainMellinProfile
  refine ⟨768 * C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hlog hG hGT hL
  have hT0 : 0 < T := by linarith
  have hinterval : T / 16 ≤ T := by linarith
  have hphase : IntervalC1Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (T / 16) T 1 := by
    simpa only [h_MathCollab_Density_Stronger_Atkinson_norm_zetaSquareReflectedGammaPhase] using
      h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_const (zetaSquareReflectedGammaPhase T) (T / 16) T
  have h := (((((h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_source_log hT).mul
    (h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_zetaDivisorBandCutoff hT0 hG hL hinterval) hinterval).mul
      (h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_source_sqrt hT0) hinterval).mul (hprofile T hT0) hinterval).mul
        hphase hinterval).mul (h_MathCollab_Density_Stronger_Atkinson_intervalC1Bound_zetaQuadraticLogGaussian hT0 hG hGT) hinterval
  apply h.mono
  have hp : 0 ≤ 256 * C * Real.sqrt Real.pi * G * Real.sqrt T := by positivity
  have hl := mul_le_mul_of_nonneg_left (h_MathCollab_Density_Stronger_Atkinson_sourceLogWeight_le_three_log hlog) hp
  convert hl using 1 <;> ring
end MathCollab.Density.Stronger.Atkinson
