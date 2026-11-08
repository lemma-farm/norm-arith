module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.veb9de1d9de7b.SquaresInCircles.Common.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
/-!
# A supporting functional for two squares with disjoint interiors

Open squares are convex and open, so the geometric Hahn--Banach theorem
separates two squares with disjoint interiors by a nonzero linear functional
`dot n`. `support_separator` sharpens this to the exact support bound
`width S n + width T n ≤ dot n (sub T.center S.center)` by testing the
functional on shrunk support vertices, which lie in the open squares.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles
end SquaresInCircles
