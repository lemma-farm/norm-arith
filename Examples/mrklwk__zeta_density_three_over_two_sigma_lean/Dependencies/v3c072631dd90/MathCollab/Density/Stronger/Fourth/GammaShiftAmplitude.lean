module
-- Reversible module-visibility port of the audited development.
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under the MIT-0 license. See ../../../../../third_party/twelfth/LICENSE-MIT-0.
Adapted from exact source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Provenance: ../../../../../third_party/twelfth/SQUARE_KERNEL_NEAR_MANIFEST.json.
The imported DigammaSeries retains its separate Apache-2.0 attribution.
-/
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v3c072631dd90.MathCollab.Density.Stronger.Fourth.GammaShiftLog
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set MeasureTheory
open MathCollab.Density.Stronger
open MathCollab.Density.Stronger.Fourth.Digamma
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
def zetaGammaShiftError (t : ℝ) (w : ℂ) : ℝ := (17 * ‖w‖ + 2 * ‖w‖ ^ 2) / t
end MathCollab.Density.Stronger.Fourth
