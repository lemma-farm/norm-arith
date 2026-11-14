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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.Stronger.Fourth.Coefficients ====
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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.Stronger.Fourth.SquareSource ====
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

def zetaSquareGammaNormalization (t : ℝ) : ℂ :=
  Gammaℝ (afeCriticalPoint t) * Gammaℝ (afeCriticalPoint (-t))
end MathCollab.Density.Stronger.Fourth

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.Stronger.Fourth.SquareNormalized ====
public section
-- Reversible module-visibility port of the audited development.
/- Narrow actual normalized-zeta source and kernel port from Scott McColm,
MIT-0, exact pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SQUARE_NORMALIZED_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0. -/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth

open scoped ComplexConjugate Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

def zetaSquarePoleShift (t : ℝ) (w : ℂ) : ℂ :=
  ((afeCriticalPoint (-t) + w) * (1 - (afeCriticalPoint (-t) + w)) /
    (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)))) ^ 2

def zetaFourthKernel (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (100*w^2) * hughesYoungAuxiliaryZero w *
    zetaSquarePoleShift t w *
      (Complex.Gammaℝ (afeCriticalPoint (-t)+w)^2 /
        zetaSquareGammaNormalization t) / w

end MathCollab.Density.Stronger.Fourth

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.Stronger.Fourth.GammaShiftLog ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See ../../../../../third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/SQUARE_KERNEL_NEAR_MANIFEST.json.
The imported DigammaSeries retains its separate Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set MeasureTheory
open MathCollab.Density.Stronger

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

def zetaGammaLeadingLog (t : ℝ) : ℂ :=
  (Real.log (t / (2 * Real.pi)) : ℂ) - ((Real.pi / 2 : ℝ) : ℂ) * I

end MathCollab.Density.Stronger.Fourth

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.Stronger.Fourth.GammaShiftAmplitude ====
public section
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See ../../../../../third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/SQUARE_KERNEL_NEAR_MANIFEST.json.
The imported DigammaSeries retains its separate Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set MeasureTheory
open MathCollab.Density.Stronger

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

def zetaGammaShiftError (t : ℝ) (w : ℂ) : ℝ := (17 * ‖w‖ + 2 * ‖w‖ ^ 2) / t

end MathCollab.Density.Stronger.Fourth

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_43a2de1e7adf6cfe8d22_SquareKernel ====
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See ../../../../../third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/SQUARE_KERNEL_NEAR_MANIFEST.json.
The imported DigammaSeries retains its separate Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set MeasureTheory
open MathCollab.Density.Stronger

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth


set_option linter.unusedVariables false in
theorem exists_norm_zetaFourthKernel_near_le {c : ℝ} (hc : 0 < c) 
    (h_MathCollab_Density_Stronger_Fourth_exp_zetaGammaLeadingLog_vertical_le : ∀ {t c : ℝ},
      0 < t →
        0 ≤ c →
          ∀ (u : ℝ),
            Real.exp
                (((↑c : ℂ) + (↑u : ℂ) * Complex.I) *
                    MathCollab.Density.Stronger.Fourth.zetaGammaLeadingLog t).re ≤
              t ^ c * Real.exp (Real.pi * |u| / 2))
    (h_MathCollab_Density_Stronger_Fourth_norm_zetaSquarePoleShift_le : ∀ {t : ℝ},
      0 < t → ∀ {w : ℂ}, ‖w‖ ≤ t / 2 → ‖MathCollab.Density.Stronger.Fourth.zetaSquarePoleShift t w‖ ≤ 9)
    (h_MathCollab_Density_Stronger_Fourth_norm_vertical_shift_le : ∀ {c : ℝ}, 0 ≤ c → ∀ (u : ℝ), ‖(↑c : ℂ) + (↑u : ℂ) * Complex.I‖ ≤ c + |u|)
    (h_MathCollab_Density_Stronger_Fourth_norm_hughesYoungAuxiliaryZero_le_polynomial : ∀ {w : ℂ} {R : ℝ},
      1 ≤ R → ‖w‖ ≤ R → ‖MathCollab.Density.Stronger.Fourth.hughesYoungAuxiliaryZero w‖ ≤ 625 * R ^ 8)
    (h_MathCollab_Density_Stronger_Fourth_norm_zetaFourthKernel_vertical : ∀ (t c u : ℝ),
      ‖MathCollab.Density.Stronger.Fourth.zetaFourthKernel t ((↑c : ℂ) + (↑u : ℂ) * Complex.I)‖ =
        Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
                ‖MathCollab.Density.Stronger.Fourth.hughesYoungAuxiliaryZero
                    ((↑c : ℂ) + (↑u : ℂ) * Complex.I)‖ *
              ‖MathCollab.Density.Stronger.Fourth.zetaSquarePoleShift t
                  ((↑c : ℂ) + (↑u : ℂ) * Complex.I)‖ *
            ‖((MathCollab.Density.Stronger.Fourth.afeCriticalPoint (-t) +
                      ((↑c : ℂ) + (↑u : ℂ) * Complex.I)).Gammaℝ /
                  (MathCollab.Density.Stronger.Fourth.afeCriticalPoint (-t)).Gammaℝ) ^
                2‖ /
          ‖(↑c : ℂ) + (↑u : ℂ) * Complex.I‖)
    (h_MathCollab_Density_Stronger_Fourth_vertical_shift_re_le_norm : ∀ {c : ℝ}, 0 ≤ c → ∀ (u : ℝ), c ≤ ‖(↑c : ℂ) + (↑u : ℂ) * Complex.I‖)
    (h_MathCollab_Density_Stronger_Fourth_norm_gammaReal_shift_sq_le_exp : ∀ {t : ℝ},
      4 ≤ t →
        ∀ {w : ℂ},
          0 ≤ w.re →
            ‖w‖ ≤ t / 2 →
              ‖((MathCollab.Density.Stronger.Fourth.afeCriticalPoint (-t) + w).Gammaℝ /
                      (MathCollab.Density.Stronger.Fourth.afeCriticalPoint (-t)).Gammaℝ) ^
                    2‖ ≤
                Real.exp (MathCollab.Density.Stronger.Fourth.zetaGammaShiftError t w) *
                  Real.exp (w * MathCollab.Density.Stronger.Fourth.zetaGammaLeadingLog t).re)
    (h_MathCollab_Density_Stronger_Fourth_abs_polynomial_mul_exp_le_gaussian : ∀ {a b : ℝ},
      0 ≤ a →
        0 ≤ b →
          ∀ (D : ℝ) (m : ℕ) (u : ℝ),
            (a + b * |u|) ^ m * Real.exp (D * |u|) ≤
              Real.exp ((↑m : ℝ) * a + ((↑m : ℝ) * b + D) ^ 2 / 4) * Real.exp (u ^ 2))
    (h_MathCollab_Density_Stronger_Fourth_zetaGammaShiftError_le_quadratic : ∀ {t c : ℝ},
      4 ≤ t →
        0 ≤ c →
          ∀ {w : ℂ} (u : ℝ),
            ‖w‖ ≤ c + |u| →
              MathCollab.Density.Stronger.Fourth.zetaGammaShiftError t w ≤
                17 * c / 4 + c ^ 2 + u ^ 2 + 17 * |u| / 4)
    :
    ∃ K : ℝ, 0 < K ∧ ∀ t u : ℝ,
      4 ≤ t → 4*c ≤ t → |u| ≤ t/4 →
      ‖zetaFourthKernel t ((c:ℂ)+(u:ℂ)*I)‖ ≤
        K*t^c*Real.exp (-98*u^2) := by
  let D : ℝ := 17/4+Real.pi/2
  let A : ℝ := 101*c^2+17*c/4
  let Q : ℝ := 8*(1+c)+(8+D)^2/4
  let K : ℝ := (5625/c)*Real.exp A*Real.exp Q
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro t u ht hct hu
  have ht0 : 0 < t := by linarith
  let w : ℂ := (c:ℂ)+(u:ℂ)*I
  let R : ℝ := 1+c+|u|
  let E : ℝ := 17*c/4+c^2+u^2+17*|u|/4
  have hw : ‖w‖ ≤ c+|u| := h_MathCollab_Density_Stronger_Fourth_norm_vertical_shift_le hc.le u
  have hwsmall : ‖w‖ ≤ t/2 := hw.trans (by linarith)
  have hwre : 0 ≤ w.re := by dsimp [w]; norm_num; exact hc.le
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg u]
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ 625*R^8 :=
    h_MathCollab_Density_Stronger_Fourth_norm_hughesYoungAuxiliaryZero_le_polynomial hR (hw.trans (by dsimp [R]; linarith))
  have hpole := h_MathCollab_Density_Stronger_Fourth_norm_zetaSquarePoleShift_le ht0 hwsmall
  have herr : zetaGammaShiftError t w ≤ E :=
    h_MathCollab_Density_Stronger_Fourth_zetaGammaShiftError_le_quadratic ht hc.le u hw
  have hlead := h_MathCollab_Density_Stronger_Fourth_exp_zetaGammaLeadingLog_vertical_le ht0 hc.le u
  have hgamma :
      ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
        Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖ ≤
      Real.exp E * (t^c*Real.exp (Real.pi*|u|/2)) := by
    exact (h_MathCollab_Density_Stronger_Fourth_norm_gammaReal_shift_sq_le_exp ht hwre hwsmall).trans
      (mul_le_mul (Real.exp_le_exp.mpr herr) hlead
        (Real.exp_pos _).le (Real.exp_pos _).le)
  have hwlower : c ≤ ‖w‖ := h_MathCollab_Density_Stronger_Fourth_vertical_shift_re_le_norm hc.le u
  have hpoly : R^8*Real.exp (D*|u|) ≤ Real.exp Q*Real.exp (u^2) := by
    simpa [R,Q] using
      h_MathCollab_Density_Stronger_Fourth_abs_polynomial_mul_exp_le_gaussian (by linarith : 0 ≤ 1+c)
        (by norm_num : (0:ℝ) ≤ 1) D 8 u
  have hexp :
      Real.exp (100*c^2-100*u^2)*Real.exp E*Real.exp (Real.pi*|u|/2) =
        Real.exp A*Real.exp (D*|u|)*Real.exp (-99*u^2) := by
    simp only [← Real.exp_add]
    congr 1
    dsimp [A,D,E]
    ring
  have hg : Real.exp (u^2)*Real.exp (-99*u^2) = Real.exp (-98*u^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_MathCollab_Density_Stronger_Fourth_norm_zetaFourthKernel_vertical]
  change Real.exp (100*c^2-100*u^2)*‖hughesYoungAuxiliaryZero w‖*
    ‖zetaSquarePoleShift t w‖*
    ‖(Complex.Gammaℝ (afeCriticalPoint (-t)+w) /
      Complex.Gammaℝ (afeCriticalPoint (-t)))^2‖/‖w‖ ≤ _
  calc
    _ ≤ Real.exp (100*c^2-100*u^2)*(625*R^8)*9*
        (Real.exp E*(t^c*Real.exp (Real.pi*|u|/2)))/c := by
      gcongr
    _ = (5625/c)*t^c*R^8*
        (Real.exp (100*c^2-100*u^2)*Real.exp E*Real.exp (Real.pi*|u|/2)) := by ring
    _ = (5625/c)*t^c*Real.exp A*(R^8*Real.exp (D*|u|))*Real.exp (-99*u^2) := by
      rw [hexp]
      ring
    _ ≤ (5625/c)*t^c*Real.exp A*(Real.exp Q*Real.exp (u^2))*Real.exp (-99*u^2) := by
      gcongr
    _ = K*t^c*(Real.exp (u^2)*Real.exp (-99*u^2)) := by dsimp [K]; ring
    _ = _ := by rw [hg]
end MathCollab.Density.Stronger.Fourth
