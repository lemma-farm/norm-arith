module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourC1Space
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourChordArc
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# The genuinely integrable increment part of the contour Cauchy integral

The curve, its derivative and the density below are actual functions.  A
short-arc chord bound and a Hölder increment produce the integrable majorant
`|τ| ^ (γ - 1)`.  No principal-value identity is assumed.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal Interval
namespace Euler2D
end Euler2D
