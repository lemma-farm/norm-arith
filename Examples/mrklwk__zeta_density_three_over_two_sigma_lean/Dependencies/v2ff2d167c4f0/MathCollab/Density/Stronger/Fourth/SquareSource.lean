module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Source slices and exact hashes:
../../../../../third_party/twelfth/SQUARE_PORT_MANIFEST.json.
See ../../../../../third_party/twelfth/LICENSE-MIT-0.
The local rectangle theorem preserves its PNT+ Apache-2.0 attribution.
-/
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.RectangleResidue
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.Stronger.Fourth.Coefficients
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2ff2d167c4f0.MathCollab.Density.Stronger.CriticalMoment
public import Mathlib
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology ArithmeticFunction
open MathCollab.Density.Contour MathCollab.Density.Stronger
open MathCollab.Density.Stronger.Fourth
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma BigOperators Interval
  LSeries.notation ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
noncomputable def hughesYoungAuxiliaryZero (w : ℂ) : ℂ :=
  (1 - 4 * w ^ 2) ^ 4
theorem afeCriticalPoint_neg_eq_star (t : ℝ) :
    afeCriticalPoint (-t) = star (afeCriticalPoint t) := by
  simp [afeCriticalPoint]
def zetaSquareGammaNormalization (t : ℝ) : ℂ :=
  Gammaℝ (afeCriticalPoint t) * Gammaℝ (afeCriticalPoint (-t))
end MathCollab.Density.Stronger.Fourth
