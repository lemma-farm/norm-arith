module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.veb9de1d9de7b.SquaresInCircles.Common.Sweep
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
/-!
# Charts

A chart of a square seen from the disk centre records a phase and a possible
reversal of orientation in which the square, on every circle about the disk
centre and slid along the ray through its centre, is the axis-parallel square
at `(a, b)` with `a, b ≥ 0`. The two coordinates can be sorted, `b ≤ a`, without
changing the square. In the Cartesian coordinates of the frame of the phase the
square sits at `(a, ±b)`, the sign recording the reversal
(`SquareChart.cartesian`); points in a rotated frame and polar coordinates
connect the two descriptions.
-/
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles
def chartAngle (phase : Direction) (rev : Bool) (t : ℝ) : Direction :=
  phase+((if rev then -t else t : ℝ) : Direction)
/-- Seen from `o` along `chartAngle phase rev`, the square slid by `m` along
the ray through its centre is the axis-parallel square at `(1+m)(a,b)`. -/
abbrev ChartCondition (S : UnitSquare) (o : Point) (phase : Direction) (rev : Bool) (a b : ℝ) :
    Prop :=
  ∀ r t m, openSquare S
    (sub (circlePoint o r (chartAngle phase rev t)) (scale m (sub S.center o))) ↔
    |r*Real.cos t-(1+m)*a| < 1/2 ∧ |r*Real.sin t-(1+m)*b| < 1/2
structure SquareChart (S : UnitSquare) (o : Point) where
  a : ℝ
  b : ℝ
  phase : Direction
  reversed : Bool
  coordinates : (a=alpha S o ∧ b=beta S o) ∨ (a=beta S o ∧ b=alpha S o)
  shifted_membership : ChartCondition S o phase reversed a b
section ChartCondition
variable {S : UnitSquare} {o : Point} {φ : Direction} {rev : Bool} {a b : ℝ}
end ChartCondition
end SquaresInCircles
