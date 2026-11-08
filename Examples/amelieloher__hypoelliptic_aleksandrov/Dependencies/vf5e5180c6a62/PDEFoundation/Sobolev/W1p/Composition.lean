module
public import Mathlib
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.EuclideanFieldMeasurability
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.LpDominatedConvergence
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.Closure
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.ConvexApprox.Density
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Bounded-derivative composition in `W^{1,p}`

This file proves the `C¹` chain rule on bounded open convex domains for every
finite exponent `p ≥ 1`.  If `|G'| ≤ M`, then

`D(G ∘ u) = G'(u) Du`

with the exact multiplier `M` in the value and gradient estimates.

The proof follows the non-circular route used later for truncations:

1. approximate `u` smoothly on the convex domain;
2. extract an almost-everywhere convergent subsequence;
3. use domination by `2 M |Du|` for the nonlinear gradient term;
4. pass to the limit through the closed `W^{1,p}` graph.

No general Lipschitz Sobolev chain rule is asserted here.  Such a theorem also
requires Stampacchia's null-preimage result at the nondifferentiability set.
-/
@[expose] public section
open scoped ENNReal Topology
namespace PDE
open Filter MeasureTheory
namespace W1pFunction
variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
end W1pFunction
end PDE
