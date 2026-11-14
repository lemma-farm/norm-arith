module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.vea432f6b55ff.SquaresInCircles.Common.Basic ====
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

/-- Squared distance to the farthest vertex in local absolute coordinates. -/
def phi (a b : ℝ) : ℝ := (a + 1/2)^2 + (b + 1/2)^2

end SquaresInCircles

end
end
end

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.vea432f6b55ff.SquaresInCircles.Common.ExteriorCharts ====
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

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.vea432f6b55ff.SquaresInCircles.Six.Constants ====
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

/-! ### The stress of the model -/

/-! ### The ceiling of the normalization -/
/-- The ceiling on the squared radius, just above `qStar`. -/
def Q0 : ℝ := 2.85118

/-! ### Decimal ceilings -/
/-- `R0` rounded up. -/
def radiusBound : ℝ := 1.6886

namespace Wings

end Wings
end SquaresInCircles.Six

end
end
end

-- ==== Examples.vltanh__lean4_squares_in_circles.Dependencies.vea432f6b55ff.SquaresInCircles.Six.Normalization.Basic ====
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

/-! ### Charts of exterior squares -/
/-- A sorted chart `(a, u)` whose far corner lies in the disk of squared radius
`Q0`. -/
abbrev ContainedChart (a u : ℝ) : Prop := ExteriorChart Q0 a u

namespace ContainedChart
variable {a u : ℝ} (h : ContainedChart a u)
include h

end ContainedChart

/-! ### Oriented squares -/

/-! ### Phases -/

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

-- ==== Examples.vltanh__lean4_squares_in_circles.Examples.Example_2140d87aa0bfa026e306_Supports ====
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

/-- A majorant of the length of the force `(z + sin q, cos q - 1)` on D. -/
def chordMajorant (z q : ℝ) : ℝ := (2+z^2/4)*Real.sin (q/2)+z*Real.cos (q/2)
set_option linter.unusedVariables false in
/-- The far-vertex support of D with the length of its force bounded by
`chordMajorant`, whose square exceeds the squared length by
`(z³/2) sin (q/2) cos (q/2) + (z⁴/16) sin² (q/2)`. -/
lemma chord_support {a b z q : ℝ} (hc : ContainedChart a |b|) (hz : 0 ≤ z)
    (hq : 0 ≤ q ∧ q ≤ Real.pi) 
    (h_SquaresInCircles_Six_vertex_support : ∀ {a b U V r : ℝ},
      SquaresInCircles.Six.Normalization.ContainedChart a |b| →
        0 ≤ r →
          U ^ 2 + V ^ 2 ≤ r ^ 2 → U * a + V * b ≤ SquaresInCircles.Six.radiusBound * r - (|U| + |V|) / 2)
    :
    (z+Real.sin q)*a+(Real.cos q-1)*b ≤
      radiusBound*chordMajorant z q-(z+Real.sin q+1-Real.cos q)/2 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ q/2 by linarith)
    (show q/2 ≤ Real.pi by linarith [Real.pi_pos])
  have hc2 := Real.cos_nonneg_of_mem_Icc
    (show q/2 ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
  have hsin : Real.sin q=2*Real.sin (q/2)*Real.cos (q/2) := by
    simpa only [show 2*(q/2)=q by ring] using Real.sin_two_mul (q/2)
  have hcos : Real.cos q=2*Real.cos (q/2)^2-1 := by
    simpa only [show 2*(q/2)=q by ring] using Real.cos_two_mul (q/2)
  have hsq : (z+Real.sin q)^2+(Real.cos q-1)^2 ≤ chordMajorant z q^2 := by
    rw [hsin,hcos]
    dsimp [chordMajorant]
    nlinarith [Real.sin_sq_add_cos_sq (q/2),mul_nonneg (mul_nonneg (pow_nonneg hz 3) hs) hc2,
      mul_nonneg (pow_nonneg hz 4) (sq_nonneg (Real.sin (q/2)))]
  have h := h_SquaresInCircles_Six_vertex_support hc (by dsimp [chordMajorant]; positivity) hsq
  linarith [le_abs_self (z+Real.sin q),neg_le_abs (Real.cos q-1)]
/-! ### The cap and the cones -/

/-! ### The box of the centre of C -/

end SquaresInCircles.Six
