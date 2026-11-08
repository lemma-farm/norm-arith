module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.Contacts
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.Sweep
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.ExteriorCharts
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.DiskSupport
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.Congruence
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Six.Constants
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.SeparatingAxes
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
/-- A sorted chart `(a, u)` whose far corner lies in the disk of squared radius
`Q0`. -/
abbrev ContainedChart (a u : ℝ) : Prop := ExteriorChart Q0 a u
namespace ContainedChart
variable {a u : ℝ} (h : ContainedChart a u)
include h
end ContainedChart
lemma projection_abs_le_rho0 {x y c s : ℝ}
    (hp : x ^ 2 + y ^ 2 ≤ rho0 ^ 2) (hu : c ^ 2 + s ^ 2 = 1) :
    |x*c + y*s| ≤ rho0 := by
  have h := dot_sq_le (p := c) (r := s) hp
  rw [hu,mul_one] at h
  exact abs_le_of_sq_le_sq (by linarith) (by linarith [rho0_bounds.1])
end SquaresInCircles.Six.Normalization
namespace SquaresInCircles.Six
/-! ### Projections of a square -/
end SquaresInCircles.Six
namespace SquaresInCircles.Six.Normalization
/-! ### Separating axes of the central square -/
/-- The projection of the centre `(cx, cy)` of C on the axis `(cos t, sin t)`. -/
def centralNormal (t cx cy : ℝ) : ℝ := cx*Real.cos t+cy*Real.sin t
lemma centralNormal_le_width {t cx cy : ℝ}
    (hx0 : 0 ≤ cx) (hy0 : 0 ≤ cy) (hx : cx ≤ 1/2) (hy : cy ≤ 1/2) :
    centralNormal t cx cy ≤ angularWidth t := by
  have hc := mul_le_mul_of_nonneg_left (le_abs_self (Real.cos t)) hx0
  have hs := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin t)) hy0
  have hcx := mul_le_mul_of_nonneg_right hx (abs_nonneg (Real.cos t))
  have hcy := mul_le_mul_of_nonneg_right hy (abs_nonneg (Real.sin t))
  dsimp [centralNormal,angularWidth]
  linarith
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
