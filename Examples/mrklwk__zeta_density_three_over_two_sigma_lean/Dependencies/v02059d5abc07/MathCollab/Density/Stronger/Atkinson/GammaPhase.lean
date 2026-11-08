module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see ../../../../../third_party/twelfth/LICENSE-MIT-0.
Provenance: ../../../../../third_party/twelfth/ATKINSON_GAUSSIAN_MANIFEST.json.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Only the listed proof slices are retained. Mathlib retains Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import Mathlib
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Fourth.GammaShiftLog
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Fourth.SquareNormalized
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex MeasureTheory
open scoped ComplexConjugate
open MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Stronger.Fourth.Digamma
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
def zetaSquareReflectedGammaPhase (t : ℝ) : ℂ :=
  Complex.Gammaℝ (afeCriticalPoint (-t)) / Complex.Gammaℝ (afeCriticalPoint t)
theorem norm_zetaSquareReflectedGammaPhase (t : ℝ) :
    ‖zetaSquareReflectedGammaPhase t‖ = 1 := by
  rw [zetaSquareReflectedGammaPhase, afeCriticalPoint_neg_eq_star]
  change ‖Complex.Gammaℝ (conj (afeCriticalPoint t)) / Complex.Gammaℝ (afeCriticalPoint t)‖ = 1
  rw [gammaReal_conj, norm_div, Complex.norm_conj, div_self]
  exact norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [afeCriticalPoint]))
end MathCollab.Density.Stronger.Atkinson
