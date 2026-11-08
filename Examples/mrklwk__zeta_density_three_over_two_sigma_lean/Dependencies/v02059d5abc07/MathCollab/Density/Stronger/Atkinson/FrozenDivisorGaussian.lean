module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.DivisorWeightFreezing
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Atkinson.GammaGaussianTransform
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson
theorem norm_zetaGaussianQuadraticIntegral_le_mass {T G : ℝ} (hT : 0 < T)
    (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (v : ℝ) :
    ‖zetaGaussianQuadraticIntegral T G v‖ ≤ Real.sqrt Real.pi * G := by
  apply (norm_zetaGaussianQuadraticIntegral_le hT hG hGT v).trans
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (G * v)]))
end MathCollab.Density.Stronger.Atkinson
