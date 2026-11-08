module
-- Reversible module-visibility port of the audited development.
/- Narrow actual normalized-zeta source and kernel port from Scott McColm,
MIT-0, exact pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SQUARE_NORMALIZED_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0. -/
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v02059d5abc07.MathCollab.Density.Stronger.Fourth.SquareContour
public import Mathlib
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped ComplexConjugate Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
theorem gammaReal_conj (z : ℂ) : Complex.Gammaℝ (conj z) = conj (Complex.Gammaℝ z) := by
  have hpow := Complex.cpow_conj (Real.pi : ℂ) (-z / 2)
    (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm)
  simp only [map_div₀, map_neg, map_ofNat, conj_ofReal] at hpow
  simp only [Complex.Gammaℝ, map_mul, ← Complex.Gamma_conj,
    map_div₀, map_ofNat, hpow]
end MathCollab.Density.Stronger.Fourth
