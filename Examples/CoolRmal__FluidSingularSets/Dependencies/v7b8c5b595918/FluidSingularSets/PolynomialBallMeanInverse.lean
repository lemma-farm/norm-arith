-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.v7b8c5b595918.FluidSingularSets.BallBoundaryApproximation
public import Examples.CoolRmal__FluidSingularSets.Dependencies.v7b8c5b595918.CKN.Foundation.Parabolic.Integration.Average
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Actual mean-zero polynomial divergence inversion on the ball

Compact interior approximations identify the algebraic obstruction constant
with the actual ball average. Consequently every polynomial with zero ball
integral is the divergence of a genuine smooth vector field vanishing on the
sphere. No uniform inverse norm is assumed.
-/
@[expose] public section
open CKN MvPolynomial MeasureTheory Set
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Integration
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace FluidSingularSets
end FluidSingularSets
