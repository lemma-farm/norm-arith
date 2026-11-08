module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.v91d9f6a1eb8c.Paper.ParisiMild
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option autoImplicit false
set_option backward.privateInPublic true
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
