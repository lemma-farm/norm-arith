module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.v436b2a4cbb13.SquaresInCircles.Common.Basic ====
public section
/-!
# Frames, interior-disjointness and the farthest-vertex bound

Vector operations, a square's frame and vertices, and the squared distance
`phi` from a point to the farthest vertex of a square: the closed square lies
in a closed disk about the point exactly when `phi` is at most the squared
radius, and `phi` bounds the distance of the centre. Distances always use
`normSq`; the product-space norm on `ℝ × ℝ` is the maximum norm.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles

def phi (a b : ℝ) : ℝ := (a + 1/2)^2 + (b + 1/2)^2

end SquaresInCircles

end
end
end

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.v436b2a4cbb13.SquaresInCircles.Common.ExteriorCharts ====
public section
/-!
# Charts of exterior squares in a disk

A sorted chart `(a, u)` of an exterior square whose far vertex lies in the
closed disk of squared radius `Q` has `1/2 ≤ a`, `0 ≤ u ≤ a` and `φ(a, u) ≤ Q`
(`ExteriorChart`). With a signed transverse coordinate `b`, `|b| = u`, the far
corner `(|a| + 1/2, |b| + 1/2)` lies in the disk and the centre `(a, b)` within
`√(Q - 1/4) - 1/2` of the disk centre.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles
/-- The sorted chart `(a, u)` of an exterior square whose far vertex lies in the
closed disk of squared radius `Q`. -/
structure ExteriorChart (Q a u : ℝ) : Prop where
  half_le : 1/2 ≤ a
  u_nonneg : 0 ≤ u
  u_le : u ≤ a
  phi_le : phi a u ≤ Q
namespace ExteriorChart
variable {Q a u : ℝ} (h : ExteriorChart Q a u)
include h

end ExteriorChart
end SquaresInCircles

end
end
end

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.v436b2a4cbb13.SquaresInCircles.Six.Constants ====
public section
/-!
# Six squares: the constants

The constants of the six-square proof, each with one decimal bracket.

The model (defined with the statement, in `Geometry.lean`) is built from
`h = √2/2` and the smaller root `s*` of `s² - A s + B`; `t*`, `d*` and the
squared radius `q* = 2s*² + 4s* + 5/2` follow from it. The far corners of E and
W and the far vertices of D lie on the circle of squared radius `q*`. The
stress of the model has weight `1` on the four contacts of
C, `r* = (s* + 1/2)/(s* + 3/2)` on N–W and E–S, and `m* = (1 + r*) k*`, with
`k* = (t* + 1/2)/(3/2 - s*)`, on W–D and D–S; the force on D has length
`diagonalK = 2h m*`, the centre of D lies at distance `ρ* = √(q* - 1/4) - 1/2`
from the disk centre, and `pairBase = m* (1/2 - t*)`. The forces of the model
point at the far corners of N and W on the circle, which gives their lengths,
and `2 pairBase + diagonalK (1 - ρ*) = 0` because `ρ* = 2h d*`. The brackets
have as many decimals as their uses need: seven or eight for `h`, `s*`, `t*`,
`r*`, `k*` and `m*`, from which the others are computed, and at most five for
the rest. `s*` comes from the sign of its quadratic, the others from it by
products, quotients and square roots.

The normalization works below the ceiling `Q0 = 2.85118` on the squared radius,
less than `3·10⁻⁶` above `q*`. With `R0 = √Q0`, the number
`ρ0 = √(Q0 - 1/4) - 1/2` is the largest radial coordinate of a square in the
disk, `c0 = ρ0 - 1` bounds the centre of the central square C,
`coreRadius = 3/2 - ρ0` is the radius of a disk about the origin inside C,
`aMin = 2 - ρ0` is the least radial coordinate of a square outside that disk and
`U0` its largest transverse coordinate. The decimals `radiusBound`, `rhoBound`,
`coreLower` and `coreUpper` stand for `R0`, `ρ0` and `c0`, rounded, in the
estimates, and `A` and `B` for `1/2 ∓ coreUpper`.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles.Six
/-! ### The model -/
def Q0 : ℝ := 2.85118
def rho0 : ℝ := Real.sqrt (Q0-1/4)-1/2

namespace Wings
end Wings
end SquaresInCircles.Six

end
end
end

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.v436b2a4cbb13.SquaresInCircles.Six.Normalization.Basic ====
public section
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
end SquaresInCircles.Six.Normalization

end
end
end

-- ==== Examples.vltanh__lean4_squares_in_circles.Examples.Example_5a29d8d1e833d581fcf1_Supports ====
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

set_option linter.unusedVariables false in
/-- The support of a nearly radial force exceeds `ρ0 U` by at most `1/160`,
by the far-corner bound `a + (31/100)(|b| + b²) ≤ ρ0` and a completed square. -/
theorem narrow_support {a b U V : ℝ} (hc : ContainedChart a |b|)
    (hU : 3/5≤U ∧ U≤7/10) (hV : |V|≤(2/5)*U) 
    (h_SquaresInCircles_Six_radial_transverse_quadratic : ∀ {a b : ℝ},
      SquaresInCircles.Six.Normalization.ContainedChart a |b| →
        a + 31 / 100 * (|b| + b ^ 2) ≤ SquaresInCircles.Six.rho0)
    : U*a+V*b≤rho0*U+1/160 := by
  have hU0 : 0≤U := by linarith [hU.1]
  have hrad := h_SquaresInCircles_Six_radial_transverse_quadratic hc
  have hm := mul_nonneg hU0 (show 0≤rho0-a-(31/100)*(|b|+b^2) by linarith)
  have hlinear := mul_nonneg (show 0≤(31/100)*U-(31/40)*|V| by linarith [hV]) (abs_nonneg b)
  have hquadratic := mul_nonneg (sub_nonneg.mpr hU.1) (sq_nonneg b)
  have hproduct : V*b≤|V| *|b| := by simpa only [abs_mul] using le_abs_self (V*b)
  have hsq : 0≤(31/100)*(3/5)*|b|^2-(9/40)*|b| *|V|+(7/100)*|V|^2 := by
    nlinarith [sq_nonneg (|V|-(45/28)*|b|),sq_nonneg |b|]
  rw [sq_abs,sq_abs] at hsq
  have hsoft : U*a+V*b≤rho0*U+(7/100)*V^2 := by
    nlinarith only [hm,hlinear,hquadratic,hproduct,hsq]
  have habs : |V|≤7/25 := by linarith [hV,hU.2]
  have hbound : V^2≤(7/25:ℝ)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr habs) (show 0≤7/25+|V| by positivity),sq_abs V]
  nlinarith only [hsoft,hbound]
/-! ### The box of the centre of C -/
end SquaresInCircles.Six
