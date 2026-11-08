module
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.veb9de1d9de7b.SquaresInCircles.Common.Charts
public import Examples.vltanh__lean4_squares_in_circles.Dependencies.veb9de1d9de7b.SquaresInCircles.Common.Constructions
/-!
# Congruence to a model

A configuration is congruent to a model when, in one frame at the disk centre
and after a relabelling, every square is the corresponding model square, both
as an open and as a closed set. It compares point sets, since a quarter-turn
of a frame describes the same square. `Represents`
places one square at an axis-parallel slot of the frame, and
`congruent_of_slots` turns an assignment of slots into congruence.
`modelSquare o φ c` is the square at `c` in the frame `φ` at `o`, and
`orientedSquare t a b` the one at `(a, b)` in the frame `t` at the origin.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles
end SquaresInCircles
