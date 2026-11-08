module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v436b2a4cbb13.SquaresInCircles.Common.Separation
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v436b2a4cbb13.SquaresInCircles.Common.Arcs
/-!
# The radial sweep

The radial sweep of a square is the union of its translates along the ray from
the disk centre through its centre. If the centres of two squares with disjoint
interiors are within distance 1 of the disk centre, the separating functional of
`support_separator` keeps the sweep of either square away from the other
(`safe_openRay_of_disjoint`): along every direction, the disk centre is within
the sum of the two widths of each centre. Of two or more disjoint squares at
most one contains the disk centre, and in the angular budget it can be replaced
by its sweep (`ray_budget_impossible`).
-/
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles
end SquaresInCircles
