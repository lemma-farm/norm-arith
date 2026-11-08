module
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
The fixed-strip growth and Gaussian contour majorants are new proofs.
See ../../../../../third_party/twelfth/SQUARE_GROWTH_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
No global-order, Hadamard, Architect, or upstream project module is imported.
-/
public import Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v3c072631dd90.MathCollab.Density.Stronger.Fourth.SquareGrowth
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth
end MathCollab.Density.Stronger.Fourth
