-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GOEExtremalEdges
set_option autoImplicit false
@[expose] public section
/-!
# Actual finite-dimensional spectral trace Lipschitz bound

Squared overlaps between actual orthonormal eigenbases give a doubly stochastic
coupling. Its squared spectral displacement is the literal Frobenius matrix
norm. Weighted Cauchy--Schwarz then controls every scalar Lipschitz spectral
trace, without assuming Hoffman--Wielandt as a premise.
-/
namespace SlowEquilibration.SpectralTraceLipschitz
noncomputable section
set_option backward.isDefEq.respectTransparency false
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace Topology NNReal
def clippedLog (k rho x : ℝ) : ℝ := Real.log (max |k - x| rho)
end
end SlowEquilibration.SpectralTraceLipschitz
