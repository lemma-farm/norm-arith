module
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.GaussianHeat
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.ParisiPDE
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! # The backward heat identity for time-dependent tests

Derivative exchange is proved against the actual standard Gaussian measure.
The space-time derivative is assembled from the proved time and variance
partials. Bounded smooth compactly supported tests satisfy the regularity
hypotheses by the test-regularity lemmas.
-/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper
end Paper
