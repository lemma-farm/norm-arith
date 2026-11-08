module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v436b2a4cbb13.SquaresInCircles.Common.Congruence
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.v436b2a4cbb13.SquaresInCircles.Common.Arcs
public import Mathlib.Data.Fin.Tuple.Sort
/-!
# Directions on the circle

Sorted as reals `p 0 ≤ … ≤ p n`, `n+1` directions pairwise at least `g` apart
have neighbours at least `g` apart, and so are `p n` and `p 0+2π`; so `p i-i*g`
increases and ends at most `2π-(n+1)g` above where it starts. Hence
`(n+1)g ≤ 2π`, and if `(n+1)g = 2π` then `p i-i*g` is constant: the directions
form a regular polygon. Two directions at least `π` apart are
opposite, so disjoint half circles have opposite centres. A quarter turn of the
frame turns the centre of a square by a quarter turn.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles
end SquaresInCircles
