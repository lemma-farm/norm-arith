module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.Contacts
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v99a3c95ae15b.SquaresInCircles.Common.Angles
/-!
# The separating-axis theorem

Strict overlap on the two edge axes of each of two squares implies overlap
along every normal. With `support_separator`, disjoint squares are separated
along one of their four edge axes (`SAT.separating_axes`). For two oriented
squares, the second turned by `d` from the first, the threshold is
`1/2 + angularWidth d` and the offset of the centres has explicit coordinates
in either frame (`oriented_separating_axes`).
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles.SAT
end SquaresInCircles.SAT
namespace SquaresInCircles
/-! ### Two oriented squares -/
/-- `(|cos t| + |sin t|)/2`, the half-width along a coordinate axis of a unit
square at angle `t`. -/
def angularWidth (t : ℝ) : ℝ := (|Real.cos t|+|Real.sin t|)/2
end SquaresInCircles
