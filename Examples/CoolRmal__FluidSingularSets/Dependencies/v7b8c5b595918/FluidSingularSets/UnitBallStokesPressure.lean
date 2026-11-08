-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.v7b8c5b595918.FluidSingularSets.BallDivergenceInverse
public import Examples.CoolRmal__FluidSingularSets.Dependencies.v7b8c5b595918.FluidSingularSets.StokesPressureRecovery
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Genuine bounded mean-zero Stokes pressure on the unit ball

The actual divergence right inverse constructs a continuous pressure functional
from the actual variational residual. Negative Riesz representation gives the
usual Stokes sign: gradient energy minus the pressure-divergence pairing equals
the force. The pressure has literal zero ball integral and a uniform norm bound.
-/
@[expose] public section
open MeasureTheory Set CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FluidSingularSets
end FluidSingularSets
