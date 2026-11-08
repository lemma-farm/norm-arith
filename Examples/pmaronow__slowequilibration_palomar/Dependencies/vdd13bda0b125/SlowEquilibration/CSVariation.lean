-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.CrisantiSommers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
set_option autoImplicit false
/-!
# The Crisanti--Sommers supporting inequality

This file proves the variational lower bound directly from the ordinary
Crisanti--Sommers functional. All distribution functions, potentials,
probability measures and integrals are the definitions in `CrisantiSommers`.
-/
@[expose] public section
namespace SlowEquilibration.CrisantiSommers
open MeasureTheory Set Filter
open scoped Topology
end SlowEquilibration.CrisantiSommers
