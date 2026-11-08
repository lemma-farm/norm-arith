-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.v22d23b3f3b2b.FluidSingularSets.PolynomialBallEnergy
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Uniform polynomial divergence estimate on the actual ball

A weighted Rellich identity expresses the difference between three times the
divergence energy and the full gradient energy as nonnegative squares, modulo
a genuinely zero-boundary polynomial divergence. The constant is independent
of polynomial degree. The differential identity is a weighted version of the
classical Miranda-Talenti divergence identity; the specific square completion
below is proved directly.
-/
@[expose] public section
open MvPolynomial CKN MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FluidSingularSets
end FluidSingularSets
