module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.vd6815cf84743.SquaresInCircles.Common.Contacts
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.vd6815cf84743.SquaresInCircles.Common.Sweep
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.vd6815cf84743.SquaresInCircles.Common.ExteriorCharts
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.vd6815cf84743.SquaresInCircles.Common.DiskSupport
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.vd6815cf84743.SquaresInCircles.Common.Congruence
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.vd6815cf84743.SquaresInCircles.Six.Constants
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.vd6815cf84743.SquaresInCircles.Common.SeparatingAxes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
/-!
# Six squares: charts and the separating axes of the central square

The normalization works in disks of squared radius at most `Q0`, just above the
square of the optimal radius, with the constants `R0`, `ρ0`, `c0`, `coreRadius`,
`aMin` and `U0` of `Constants`. An exterior square is read as
`orientedSquare t a b`, the square at the phase `t` with centre `(a, b)` in its
frame; a sorted chart has `1/2 ≤ a`, `|b| ≤ a` and
`(a + 1/2)² + (|b| + 1/2)² ≤ Q0` (`ContainedChart`), and if the square avoids
the core disk also `2 - ρ0 ≤ a` and `|b| ≤ U0` (`AvoidsCore`). Its centre lies
within `ρ0` of the origin. By the separating axis theorem it is separated from C
along its own axis, its secondary axis in either direction, or a side of C
(`central_separators_complete`); `centralMargin k t a b cx cy ≥ 0` is the
separating inequality along the axis `k`, with threshold `1/2 + angularWidth t`.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles.Six.Normalization
abbrev ContainedChart (a u : ℝ) : Prop := ExteriorChart Q0 a u
namespace ContainedChart
variable {a u : ℝ} (h : ContainedChart a u)
include h
end ContainedChart
end SquaresInCircles.Six.Normalization
namespace SquaresInCircles.Six
/-! ### Projections of a square -/
end SquaresInCircles.Six
namespace SquaresInCircles.Six.Normalization
/-! ### Separating axes of the central square -/
lemma transverse_distance_lt_one {b cx cy t : ℝ}
    (hb : |b| ≤ U0) (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy)
    (hx : cx ≤ c0) (hy : cy ≤ c0) :
    |b - (-cx * Real.sin t + cy * Real.cos t)| < 1 := by
  have hb' := abs_le.mp hb
  have hslo := mul_le_mul_of_nonneg_left (Real.neg_one_le_sin t) hx0
  have hshi := mul_le_mul_of_nonneg_left (Real.sin_le_one t) hx0
  have hclo := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos t) hy0
  have hchi := mul_le_mul_of_nonneg_left (Real.cos_le_one t) hy0
  apply abs_lt.mpr
  constructor <;> nlinarith [U0_upper, c0_bounds.2]
end SquaresInCircles.Six.Normalization
