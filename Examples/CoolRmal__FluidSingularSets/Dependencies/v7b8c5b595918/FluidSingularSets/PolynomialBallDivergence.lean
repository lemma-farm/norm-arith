-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.v7b8c5b595918.FluidSingularSets.WeightedBallDivergence
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Actual smooth polynomial divergence fields on the unit ball

Polynomial inversion is transported to actual smooth functions and genuine
spatial derivatives. The resulting vector field has the prescribed polynomial
divergence modulo a constant and vanishes pointwise on the unit sphere. The
constant is not yet identified with the ball mean; a uniform Sobolev bound is
also a separate analytic obligation.
-/
@[expose] public section
open MvPolynomial CKN
open CKN.Foundation.Parabolic
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace FluidSingularSets
end FluidSingularSets
