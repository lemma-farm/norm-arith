-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.SphericalConcentration
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.MixtureThresholds
set_option autoImplicit false
/-!
# Constrained, shifted free-energy concentration

All observables below use the original finite Gaussian tensor disorder law.
The reference spatial measure may be any finite nonzero measure carried by
the actual sphere. Deterministic domains and bounded measurable shifts are
constructed as a restricted, reweighted sphere measure.
-/
@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
end
end SlowEquilibration.SphericalModel
