module
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.ParisiMild
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-!
# Spatial derivatives of Gaussian smoothing for bounded measurable data

Differentiation acts on the density, so the observable need not possess a
derivative.  A shifted Gaussian with doubled variance dominates the density
derivative uniformly over a neighborhood of its mean.
-/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Paper
end Paper
