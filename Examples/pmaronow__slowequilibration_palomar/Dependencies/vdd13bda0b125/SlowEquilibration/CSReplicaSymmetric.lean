-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.CSVariation
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.CSFirstVariation
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.MixtureThresholds
public import Mathlib.Analysis.Calculus.Deriv.Inv
set_option autoImplicit false
@[expose] public section
/-!
# The actual replica-symmetric Crisanti--Sommers candidate

The measure is the genuine Dirac mass at zero. Its hatted distribution,
functional value and first variation are evaluated from the integral definitions.
The scalar static-threshold criterion is then applied through the proved
Crisanti--Sommers supporting inequality.
-/
namespace SlowEquilibration.CSReplicaSymmetric
open MeasureTheory Set Filter CrisantiSommers
open scoped Topology
end SlowEquilibration.CSReplicaSymmetric
