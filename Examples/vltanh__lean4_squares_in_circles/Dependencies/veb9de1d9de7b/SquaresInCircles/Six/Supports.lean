module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.veb9de1d9de7b.SquaresInCircles.Six.Normalization.Basic
/-!
# Six squares: supports of the squares in the disk

A force `(U, V)` does work at most `R0 |(U, V)| - (|U| + |V|)/2` on the centre
`(a, b)` of a chart in the disk of radius `R0`, by its far vertex
(`local_vertex_support`), and the centre lies within `ρ0` of the origin
(`chart_radial_work`). A linear function on the part of the disk beyond a line
`A = l` is largest at a corner of that part (`disk_corner_support`,
`circle_support_above_primary`), so a force close to the primary axis has the
cap bound `ρ0 U` (`cap_linear_upper`); the far corner gives
`a + (31/100)(|b| + b²) ≤ ρ0` (`radial_transverse_quadratic`), and hence the
cone supports `ρ̄ U` for `|V| ≤ (31/100) U` and `ρ̄ U` plus a multiple of `V²`
in wider cones, by completed squares; and the force `(z + sin q, cos q - 1)` on
D has length at most `(2 + z²/4) sin (q/2) + z cos (q/2)` (`chord_support`). The
centre of C lies in the box `[0, c0]²`, where the work of a force is largest at
a corner or on the face chosen by the sign of a component (`center_face`).
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles.Six
open Normalization
/-! ### The far vertex -/
lemma disk_corner_support {A B a b c s : ℝ}
    (ha : 0 < a) (hB : b ≤ B) (hc : 0 ≤ c)
    (hcircle : a ^ 2 + b ^ 2 = Q0) (hbox : A ^ 2 + B ^ 2 ≤ Q0)
    (hslope : a * s ≤ b * c) : A * c + B * s ≤ a * c + b * s := by
  have ht : a * (A - a) + b * (B - b) ≤ 0 := by
    nlinarith [sq_nonneg (A - a), sq_nonneg (B - b)]
  have hct := mul_nonpos_of_nonneg_of_nonpos hc ht
  have hp := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hB)
  have hprod : a * (A * c + B * s - (a * c + b * s)) ≤ 0 := by
    nlinarith
  by_contra! h
  exact (not_lt_of_ge hprod)
    (mul_pos ha (show 0 < A * c + B * s - (a * c + b * s) by linarith))
end SquaresInCircles.Six
