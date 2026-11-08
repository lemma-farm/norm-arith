module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.FiniteVectorConvergence
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.LpTendsto
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.NormalizedLpTendsto
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.ConvexApprox.Convergence
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.EuclideanGradient
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.Mean
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.Smooth
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth density on bounded open convex domains

This file packages convex approximation as a sequence of smooth
`W1pFunction`s and records its exact convergence properties for every finite
exponent `p ≥ 1`.

The native gradient remains `Vec d`-valued. Coordinatewise convergence is
exported for compatibility, while the public gradient norm is the exact
Euclidean norm obtained through the internal Hilbert lift. Finite coordinate
sums occur only inside the convergence majorant supplied by
`PDEFoundation.Measure.FiniteVectorConvergence`.

Centering is performed against `normalizedVolumeOn U`, so convergence of
arithmetic means and centered values includes the endpoint `p = 1`.
-/
@[expose] public section
open scoped ENNReal Topology
namespace PDE
open Filter MeasureTheory
namespace W1pFunction
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
end W1pFunction
end PDE
